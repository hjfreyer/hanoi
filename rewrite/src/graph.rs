//! The graph itself: boxes, the links between them, and what can be asked
//! of the pair.
//!
//! This is what [`crate::diagram2`] rewrites, kept apart from it because the
//! two are different things. A graph knows what a box takes and leaves, what
//! reads what, whether it holds together, and whether another graph is the
//! same diagram. It knows nothing about terms, laws, tactics or proofs; the
//! traffic in that direction is all diagram2's, which
//! [`build`](crate::diagram2::build)s one from a term,
//! [`read_back`](crate::diagram2::read_back)s one out again, and rewrites
//! one in place against its table.
//!
//! Nothing here is generic, and that is deliberate. A [`NodeKind`] is a
//! Hanoi [`Prim`], a call into a Hanoi library, or one of the structural
//! boxes the term language has. The point of the split is that the graph is
//! its own layer, not that it is anybody's graph.
//!
//! The one invariant worth stating up front is that **a link is written at
//! both ends**: a [`Source`] names the one producer an input port reads, a
//! [`Sink`] names one reader of an output port, and both lists are kept. The
//! constructors here write the two directions together, which is why they
//! cannot be recorded apart; a rewriter that re-points one end by hand and
//! forgets the other is what [`Graph::check`] is for, and it is caught at
//! the rewrite rather than surviving as a graph that reads back wrong.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fmt;

use bytecode::SentenceIndex;

use crate::term::{Arity, Prim};

// ---- the graph ----------------------------------------------------------------

/// A box in a graph: an index into its [`Graph`]'s node list.
///
/// Meaningful only against the graph that issued it, and only while that
/// node is live — a rewrite deletes nodes, and an id is not reused.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(u32);

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id at a position, for anything that indexes a graph's boxes by
    /// their own order — [`rules`](crate::diagram2::rules) does, since a rule's side deletes
    /// nothing and so has dense ids.
    pub fn at(index: usize) -> NodeId {
        NodeId(u32::try_from(index).expect("a graph fits in u32"))
    }
}

/// Which branch a [`NodeKind::Fork`] and a [`NodeKind::Select`] are the two
/// ends of.
///
/// The pairing is recorded rather than inferred, for the same reason a link
/// is written at both ends: a rule that wants the arm a value belongs to
/// should read the fact, not reconstruct it by walking the graph and hoping
/// the walk agrees with what the builder meant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BranchId(pub(crate) u32);

impl BranchId {
    /// Where this branch sits in the order its graph handed them out, which
    /// is what [`rules`](crate::diagram2::rules) keys a renaming by.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for BranchId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// Where an input port reads from — one producer, always.
///
/// [`Source::Input`] is the graph's own boundary, which is the price of
/// having no wire type: a link to the outside is a variant rather than just
/// another port.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Source {
    /// Boundary input `i`, counted from the deepest.
    Input(usize),
    /// Output port `port` of `node`.
    Port { node: NodeId, port: usize },
}

/// Where an output port is read — none, one, or many.
///
/// The asymmetry against [`Source`] is the cartesian fact itself: a value is
/// produced once and read freely. Before any rewriting every port has
/// exactly one sink; `copy-elim` is what breaks that, and it is the point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sink {
    /// Boundary output `i`, counted from the deepest.
    Output(usize),
    /// Input port `port` of `node`.
    Port { node: NodeId, port: usize },
}

/// What a box is — [`Term`](crate::term::Term)'s leaves, one for one.
///
/// The two operators are what the graph replaces; everything else survives
/// the translation unchanged. `swap` in particular stays an
/// [`Op`][NodeKind::Op]: it is a prim like any other, and the rewriter is
/// where the fact that it is *structural* gets used, not the type.
///
/// `PartialEq` compares a [`BranchId`] as the number it is, which is right
/// for two boxes of one graph and wrong for two graphs — a branch id is
/// graph-local. [`rules::same_kind`](crate::diagram2::rules) is what a match needs, and it
/// carries the renaming.
#[derive(Debug, Clone, PartialEq)]
pub enum NodeKind {
    /// `id(n)`: `n` in, the same `n` out.
    Id(usize),
    /// `copy(n)`: block-wise, so output `i` and output `n + i` both stand
    /// for input `i`.
    Copy(usize),
    /// `drop(n)`: `n` in, nothing out.
    Drop(usize),
    /// One prim, `push` and `swap` included.
    Op(Prim),
    /// A sentence called by name, left unopened; the arity is carried for
    /// the same reason [`Term::Call`](crate::term::Term::Call) carries it.
    Call { target: SentenceIndex, arity: Arity },
    /// `fork(n)`: the two views of the stack a branch's arms get.
    ///
    /// **Input 0 is the condition**, inputs `1..=n` the stack; `2n` out,
    /// the `then` view at `0..n` and the `else` view at `n..2n`, block-wise
    /// exactly as `copy(n)` is. The condition is not used to compute
    /// anything here — a fork hands out both views whatever it says — and
    /// that is the point: it is read so that a **rule anchored at a fork
    /// can see what governs the arms it is splitting**. `specialize-equal`,
    /// where a value that tested `equal` to a literal is that literal in
    /// the then arm, is stated at the fork and needs the `equal` in its
    /// left-hand side; without the condition here the rule could not name
    /// it, because the arms lie between the fork and the `select` and no
    /// local window holds both ends.
    ///
    /// It *is* a copy otherwise, and the only reason it is not one is that
    /// `copy-elim` would delete it. Deleting it costs the one fact no other
    /// part of the graph records: which port is an arm's own view of a
    /// value — the answer `specialize-equal` writes.
    Fork { arity: usize, branch: BranchId },
    /// `select(n)`: the two blocks of an answer, and the condition that
    /// keeps one of them.
    ///
    /// **Input 0 is the condition**, inputs `1..=n` the `then` block and
    /// `n+1..=2n` the `else` block. Output `i` is input `1 + i` when the
    /// condition holds and input `1 + n + i` otherwise: this is the `fork`
    /// it is paired with, read backwards.
    ///
    /// The condition sits at the *bottom* rather than on top, where the
    /// term puts it, so that both ends of a branch read it in the same
    /// place. A rule that wants the condition then finds it at port 0
    /// whichever end it is anchored at, and [`read_back`](crate::diagram2::read_back) pays for it by
    /// hoisting the wire before it writes the `branch`.
    ///
    /// A branch's arms are not in here. They are ordinary boxes in the one
    /// graph between the two ends, so a rule reaches into an arm from
    /// outside and a value reaches out of one. Both arms are computed, which
    /// is the single-arm hoist of
    /// [docs/totality.md](../../docs/totality.md) — sound because every
    /// [`Prim`] is total, has no effect but the stack, and, unlike the
    /// term-level rule, states its arity locally even when it is a
    /// [`NodeKind::Call`].
    Select { arity: usize, branch: BranchId },
}

impl NodeKind {
    /// What this box takes and leaves — the same table
    /// [`Context::arity`](crate::term::Context::arity) keeps for terms.
    pub fn arity(&self) -> Arity {
        match self {
            NodeKind::Id(n) => Arity::new(*n, *n),
            NodeKind::Copy(n) => Arity::new(*n, 2 * n),
            NodeKind::Drop(n) => Arity::new(*n, 0),
            NodeKind::Op(prim) => prim.arity(),
            NodeKind::Call { arity, .. } => *arity,
            NodeKind::Fork { arity, .. } => Arity::new(arity + 1, 2 * arity),
            NodeKind::Select { arity, .. } => Arity::new(2 * arity + 1, *arity),
        }
    }

    /// Whether this is one of the boxes rewriting is here to delete.
    ///
    /// `drop` is not on the list: it goes by `dead-node`, which is about
    /// having no readers rather than about being structural.
    /// Whether a rule deletes this.
    ///
    /// A `fork` is structure by any other reading — it is a `copy` — but it
    /// is not *rewritable* structure, and this predicate is what the rules
    /// and [`no_structure`](../../tests) are asking about. The branch layer
    /// survives on purpose.
    pub fn is_structural(&self) -> bool {
        matches!(
            self,
            NodeKind::Id(_) | NodeKind::Copy(_) | NodeKind::Op(Prim::Swap)
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Node {
    pub(crate) kind: NodeKind,
    /// One source per input port.
    pub(crate) inputs: Vec<Source>,
    /// The readers of each output port.
    pub(crate) outputs: Vec<Vec<Sink>>,
}

/// A program as boxes and the links between them.
///
/// Nodes are only ever deleted, never moved, so a [`NodeId`] stays valid
/// (as a *dead* id, once its node is gone) for the life of the graph.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Graph {
    pub(crate) nodes: Vec<Option<Node>>,
    /// The readers of each boundary input, deepest first.
    pub(crate) inputs: Vec<Vec<Sink>>,
    /// What each boundary output reads, deepest first.
    pub(crate) outputs: Vec<Source>,
    /// Branch ids handed out so far. Never reused, so a `fork` and the
    /// `select` it was built with name each other for the life of the graph.
    pub(crate) branches: u32,
}

impl Graph {
    pub(crate) fn empty(inputs: usize) -> Graph {
        Graph {
            nodes: Vec::new(),
            inputs: vec![Vec::new(); inputs],
            outputs: Vec::new(),
            branches: 0,
        }
    }

    /// A branch id no other pair in this graph holds.
    pub(crate) fn next_branch(&mut self) -> BranchId {
        let id = BranchId(self.branches);
        self.branches += 1;
        id
    }

    /// What the whole graph takes and leaves.
    pub fn arity(&self) -> Arity {
        Arity::new(self.inputs.len(), self.outputs.len())
    }

    /// Whether that node has not been rewritten away.
    pub fn is_live(&self, id: NodeId) -> bool {
        self.nodes.get(id.index()).is_some_and(Option::is_some)
    }

    /// Every live node, in id order.
    pub fn live(&self) -> impl Iterator<Item = (NodeId, &NodeKind)> {
        self.nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| n.as_ref().map(|n| (NodeId(i as u32), &n.kind)))
    }

    /// How many boxes are left.
    pub fn live_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_some()).count()
    }

    pub fn kind(&self, id: NodeId) -> &NodeKind {
        &self.node(id).kind
    }

    /// What a node's input ports read, deepest first.
    pub fn sources(&self, id: NodeId) -> &[Source] {
        &self.node(id).inputs
    }

    /// What the boundary outputs read, deepest first.
    pub fn outputs(&self) -> &[Source] {
        &self.outputs
    }

    /// The readers of one port — the empty slice if the port does not
    /// exist, which only a malformed graph can ask about.
    pub fn sinks(&self, src: Source) -> &[Sink] {
        match src {
            Source::Input(i) => self.inputs.get(i).map(Vec::as_slice).unwrap_or(&[]),
            Source::Port { node, port } => self
                .nodes
                .get(node.index())
                .and_then(Option::as_ref)
                .and_then(|n| n.outputs.get(port))
                .map(Vec::as_slice)
                .unwrap_or(&[]),
        }
    }

    pub(crate) fn node(&self, id: NodeId) -> &Node {
        self.nodes[id.index()]
            .as_ref()
            .expect("a live node was asked for")
    }

    pub(crate) fn node_mut(&mut self, id: NodeId) -> &mut Node {
        self.nodes[id.index()]
            .as_mut()
            .expect("a live node was asked for")
    }

    pub(crate) fn sinks_mut(&mut self, src: Source) -> &mut Vec<Sink> {
        match src {
            Source::Input(i) => &mut self.inputs[i],
            Source::Port { node, port } => &mut self.node_mut(node).outputs[port],
        }
    }

    /// Writes one end of a link: what `sink` reads.
    pub(crate) fn set_source(&mut self, sink: Sink, src: Source) {
        match sink {
            Sink::Output(i) => self.outputs[i] = src,
            Sink::Port { node, port } => self.node_mut(node).inputs[port] = src,
        }
    }

    /// A box, its input ports linked to the sources given. Returns a source
    /// per output port.
    ///
    /// The link is written at both ends here and nowhere else, which is why
    /// the two directions cannot be recorded apart.
    pub(crate) fn add(&mut self, kind: NodeKind, inputs: Vec<Source>) -> Vec<Source> {
        let arity = kind.arity();
        debug_assert_eq!(inputs.len(), arity.inputs, "the caller cuts by arity");
        let id = NodeId(u32::try_from(self.nodes.len()).expect("a graph fits in u32"));
        self.nodes.push(Some(Node {
            kind,
            inputs: inputs.clone(),
            outputs: vec![Vec::new(); arity.outputs],
        }));
        for (port, src) in inputs.into_iter().enumerate() {
            self.sinks_mut(src).push(Sink::Port { node: id, port });
        }
        (0..arity.outputs)
            .map(|port| Source::Port { node: id, port })
            .collect()
    }

    /// A box, as [`Graph::add`], answering with the node rather than its
    /// ports — which is what a caller that has to place a box of no outputs
    /// needs.
    pub(crate) fn add_node(&mut self, kind: NodeKind, inputs: Vec<Source>) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).expect("a graph fits in u32"));
        self.add(kind, inputs);
        id
    }

    /// Closes the graph: these sources are what the boundary leaves.
    pub(crate) fn close(&mut self, sources: Vec<Source>) {
        for (i, &src) in sources.iter().enumerate() {
            self.sinks_mut(src).push(Sink::Output(i));
        }
        self.outputs = sources;
    }

    /// Forgets one recorded reader of a port.
    pub(crate) fn unlink(&mut self, src: Source, sink: Sink) {
        let readers = self.sinks_mut(src);
        if let Some(at) = readers.iter().position(|&s| s == sink) {
            readers.remove(at);
        }
    }
}

// ---- padding ---------------------------------------------------------------------

/// The graph as `id(k) * itself` reads: `k` fresh boundary wires passed
/// straight through beneath it.
///
/// This is the graph-side spelling of [`Context::under`](crate::term::Context::under), and it exists for
/// the same reason: a goal pads its narrower side until the arities agree,
/// and once a side is a graph the padding has to be said on the graph.
pub fn under(graph: &Graph, k: usize) -> Graph {
    if k == 0 {
        return graph.clone();
    }
    let mut out = graph.clone();
    let bump_src = |src: Source| match src {
        Source::Input(i) => Source::Input(i + k),
        port => port,
    };
    let bump_sink = |sink: Sink| match sink {
        Sink::Output(j) => Sink::Output(j + k),
        port => port,
    };
    for node in out.nodes.iter_mut().flatten() {
        for src in &mut node.inputs {
            *src = bump_src(*src);
        }
        for readers in &mut node.outputs {
            for sink in readers.iter_mut() {
                *sink = bump_sink(*sink);
            }
        }
    }
    let mut inputs: Vec<Vec<Sink>> = (0..k).map(|i| vec![Sink::Output(i)]).collect();
    inputs.extend(
        std::mem::take(&mut out.inputs)
            .into_iter()
            .map(|readers| readers.into_iter().map(bump_sink).collect::<Vec<_>>()),
    );
    out.inputs = inputs;
    let mut outputs: Vec<Source> = (0..k).map(Source::Input).collect();
    outputs.extend(std::mem::take(&mut out.outputs).into_iter().map(bump_src));
    out.outputs = outputs;
    debug_assert!(out.check().is_ok(), "padding moved no box and broke a link");
    out
}

// ---- whether two graphs are one diagram ------------------------------------------

/// Whether the two graphs are the same diagram: a bijection of live boxes
/// preserving every kind (modulo a bijection of branch ids) and every link,
/// with both boundaries pinned — input `i` to input `i`, output `j` to
/// output `j`.
///
/// Whole-graph equality, not [`rules::find`](crate::diagram2::rules::find)'s embedding: no window, no
/// reader-split, nothing left to a choice. Dead slots and the numbers ids
/// happen to hold do not count — a graph that rewrote and a graph that was
/// built are one diagram if their live boxes wire up alike.
///
/// Search, held to account the way the matcher is: a candidate bijection is
/// verified link by link before `true` is answered, so a bug here costs a
/// wrong `false` — a goal that fails to close — never a wrong `true`.
pub fn isomorphic(a: &Graph, b: &Graph) -> bool {
    if a.arity() != b.arity() || a.live_count() != b.live_count() {
        return false;
    }
    // The multiset of box shapes must agree before any search is worth
    // running — and this is what keeps the common "no" cheap.
    let census = |g: &Graph| {
        let mut kinds: Vec<String> = g.live().map(|(_, kind)| erased(kind)).collect();
        kinds.sort_unstable();
        kinds
    };
    if census(a) != census(b) {
        return false;
    }
    let mut iso = Iso {
        a,
        b,
        map: vec![None; a.nodes.len()],
        used: HashSet::new(),
        branches: HashMap::new(),
        branch_used: HashSet::new(),
    };
    iso.walk()
}

/// A box's shape with its branch id erased — what a bijection may compare
/// directly, the pairing being its own business.
fn erased(kind: &NodeKind) -> String {
    match kind {
        NodeKind::Fork { arity, .. } => format!("fork({})", arity),
        NodeKind::Select { arity, .. } => format!("select({})", arity),
        other => format!("{:?}", other),
    }
}

struct Iso<'g> {
    a: &'g Graph,
    b: &'g Graph,
    /// Image of `a`'s boxes in `b`, by `a`'s own index.
    map: Vec<Option<NodeId>>,
    used: HashSet<NodeId>,
    branches: HashMap<BranchId, BranchId>,
    branch_used: HashSet<BranchId>,
}

impl Iso<'_> {
    fn walk(&mut self) -> bool {
        let Some(x) = self.pick() else {
            return self.verify();
        };
        for y in self.candidates(x) {
            if let Some(bound) = self.assign(x, y) {
                if self.walk() {
                    return true;
                }
                self.unassign(x, y, bound);
            }
        }
        false
    }

    /// The next box to place: one with a placed neighbour if there is one,
    /// so the search rides the wiring instead of trying products — a box
    /// with no anchor at all (a literal nothing placed reads yet) comes
    /// last, when its readers have pinned it down.
    fn pick(&self) -> Option<NodeId> {
        let unassigned = || {
            self.a
                .live()
                .map(|(id, _)| id)
                .filter(|id| self.map[id.index()].is_none())
        };
        unassigned()
            .find(|&x| self.has_placed_neighbour(x))
            .or_else(|| unassigned().next())
    }

    fn has_placed_neighbour(&self, x: NodeId) -> bool {
        let placed = |id: NodeId| self.map[id.index()].is_some();
        let feeds = self
            .a
            .sources(x)
            .iter()
            .any(|src| matches!(*src, Source::Port { node, .. } if placed(node)));
        let read = (0..self.a.kind(x).arity().outputs).any(|port| {
            self.a
                .sinks(Source::Port { node: x, port })
                .iter()
                .any(|sink| matches!(*sink, Sink::Port { node, .. } if placed(node)))
        });
        feeds || read
    }

    /// The `b` boxes worth trying for `x`: a placed producer narrows to its
    /// image's readers, a placed reader pins the candidate outright, and
    /// only a box touching nothing placed falls back on the sweep.
    fn candidates(&self, x: NodeId) -> Vec<NodeId> {
        for (port, src) in self.a.sources(x).iter().enumerate() {
            if let Source::Port { node, port: q } = *src
                && let Some(m) = self.map[node.index()]
            {
                let mut out: Vec<NodeId> = self
                    .b
                    .sinks(Source::Port { node: m, port: q })
                    .iter()
                    .filter_map(|sink| match *sink {
                        Sink::Port { node, port: p } if p == port => Some(node),
                        _ => None,
                    })
                    .collect();
                out.sort_unstable();
                out.dedup();
                return out;
            }
        }
        for port in 0..self.a.kind(x).arity().outputs {
            for sink in self.a.sinks(Source::Port { node: x, port }) {
                if let Sink::Port { node, port: r } = *sink
                    && let Some(m) = self.map[node.index()]
                {
                    return match self.b.sources(m).get(r) {
                        Some(&Source::Port { node, port: q }) if q == port => vec![node],
                        _ => Vec::new(),
                    };
                }
            }
        }
        self.b.live().map(|(id, _)| id).collect()
    }

    /// Pins `x` to `y`, answering the branch pairing it bound — the undo
    /// log — or `None` if they cannot correspond. Edges whose other end is
    /// not yet placed defer to [`Iso::verify`].
    fn assign(&mut self, x: NodeId, y: NodeId) -> Option<Option<BranchId>> {
        if self.used.contains(&y) {
            return None;
        }
        let bound = match (self.a.kind(x), self.b.kind(y)) {
            (
                NodeKind::Fork { arity, branch },
                NodeKind::Fork {
                    arity: n,
                    branch: to,
                },
            )
            | (
                NodeKind::Select { arity, branch },
                NodeKind::Select {
                    arity: n,
                    branch: to,
                },
            ) => {
                if arity != n {
                    return None;
                }
                match self.branches.get(branch) {
                    Some(held) if held != to => return None,
                    Some(_) => None,
                    None => {
                        if self.branch_used.contains(to) {
                            return None;
                        }
                        self.branches.insert(*branch, *to);
                        self.branch_used.insert(*to);
                        Some(*branch)
                    }
                }
            }
            (NodeKind::Fork { .. } | NodeKind::Select { .. }, _)
            | (_, NodeKind::Fork { .. } | NodeKind::Select { .. }) => return None,
            (p, q) if p == q => None,
            _ => return None,
        };
        for (src, dst) in self.a.sources(x).iter().zip(self.b.sources(y)) {
            let fits = match (*src, *dst) {
                (Source::Input(i), Source::Input(j)) => i == j,
                (Source::Port { node, port }, Source::Port { node: m, port: q }) => {
                    port == q && self.map[node.index()].is_none_or(|held| held == m)
                }
                _ => false,
            };
            if !fits {
                self.rollback(bound);
                return None;
            }
        }
        self.map[x.index()] = Some(y);
        self.used.insert(y);
        Some(bound)
    }

    fn rollback(&mut self, bound: Option<BranchId>) {
        if let Some(branch) = bound {
            let to = self.branches.remove(&branch).expect("bound above");
            self.branch_used.remove(&to);
        }
    }

    fn unassign(&mut self, x: NodeId, y: NodeId, bound: Option<BranchId>) {
        self.map[x.index()] = None;
        self.used.remove(&y);
        self.rollback(bound);
    }

    /// Every box placed; hold the whole claim to agreeing — the deferred
    /// edges, and the boundary.
    fn verify(&self) -> bool {
        let image = |src: Source| match src {
            Source::Input(i) => Some(Source::Input(i)),
            Source::Port { node, port } => {
                self.map[node.index()].map(|m| Source::Port { node: m, port })
            }
        };
        for (x, _) in self.a.live() {
            let Some(y) = self.map[x.index()] else {
                return false;
            };
            for (src, dst) in self.a.sources(x).iter().zip(self.b.sources(y)) {
                if image(*src) != Some(*dst) {
                    return false;
                }
            }
        }
        self.a
            .outputs()
            .iter()
            .zip(self.b.outputs())
            .all(|(src, dst)| image(*src) == Some(*dst))
    }
}

// ---- well-formedness ------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Colour {
    White,
    Grey,
    Black,
}

impl Graph {
    /// Whether every node's ports match its kind, every link agrees at both
    /// ends, and nothing feeds itself.
    ///
    /// The both-ends check is what the linked form buys: a rule that
    /// re-points one end and forgets the other is caught here, where it
    /// happened, rather than surviving as a graph that reads back wrong.
    pub fn check(&self) -> Result<(), Error> {
        for (id, kind) in self.live() {
            let arity = kind.arity();
            let node = self.node(id);
            if node.inputs.len() != arity.inputs || node.outputs.len() != arity.outputs {
                return Err(Error::Width {
                    node: id,
                    expected: arity,
                    inputs: node.inputs.len(),
                    outputs: node.outputs.len(),
                });
            }
        }
        // A branch is two boxes that name each other, so a graph holding
        // two forks — or two selects — for one branch is a builder bug, and
        // this is where it surfaces rather than in whatever rule later reads
        // the pairing and gets the wrong end.
        let mut ends: HashMap<(BranchId, bool), NodeId> = HashMap::new();
        for (id, kind) in self.live() {
            let end = match kind {
                NodeKind::Fork { branch, .. } => (*branch, true),
                NodeKind::Select { branch, .. } => (*branch, false),
                _ => continue,
            };
            if let Some(&first) = ends.get(&end) {
                return Err(Error::BranchTwice {
                    branch: end.0,
                    fork: end.1,
                    first,
                    second: id,
                });
            }
            ends.insert(end, id);
        }
        // Every reader names a source that lists it back...
        for (id, _) in self.live() {
            for (port, &src) in self.node(id).inputs.iter().enumerate() {
                self.listed(src, Sink::Port { node: id, port })?;
            }
        }
        for (i, &src) in self.outputs.iter().enumerate() {
            self.listed(src, Sink::Output(i))?;
        }
        // ...and every listed reader names that source back.
        for i in 0..self.inputs.len() {
            self.reads_back(Source::Input(i))?;
        }
        for (id, kind) in self.live() {
            for port in 0..kind.arity().outputs {
                self.reads_back(Source::Port { node: id, port })?;
            }
        }
        self.acyclic()
    }

    /// Whether every port has exactly one reader — true of a freshly
    /// [`build`](crate::diagram2::build)t graph, and false from the first `copy-elim` onwards.
    pub fn is_monogamous(&self) -> bool {
        let ports = self
            .inputs
            .iter()
            .map(Vec::as_slice)
            .chain(self.live().flat_map(|(id, kind)| {
                (0..kind.arity().outputs)
                    .map(move |port| self.sinks(Source::Port { node: id, port }))
            }));
        ports.into_iter().all(|readers| readers.len() == 1)
    }

    pub(crate) fn valid(&self, src: Source) -> bool {
        match src {
            Source::Input(i) => i < self.inputs.len(),
            Source::Port { node, port } => {
                self.is_live(node) && port < self.kind(node).arity().outputs
            }
        }
    }

    fn listed(&self, src: Source, sink: Sink) -> Result<(), Error> {
        if !self.valid(src) {
            return Err(Error::Dangling { source: src, sink });
        }
        if self.sinks(src).iter().filter(|&&s| s == sink).count() != 1 {
            return Err(Error::Torn { source: src, sink });
        }
        Ok(())
    }

    fn reads_back(&self, src: Source) -> Result<(), Error> {
        for &sink in self.sinks(src) {
            let names = match sink {
                Sink::Output(i) => self.outputs.get(i).copied(),
                Sink::Port { node, port } => self
                    .nodes
                    .get(node.index())
                    .and_then(Option::as_ref)
                    .and_then(|n| n.inputs.get(port))
                    .copied(),
            };
            if names != Some(src) {
                return Err(Error::Torn { source: src, sink });
            }
        }
        Ok(())
    }

    fn acyclic(&self) -> Result<(), Error> {
        let mut colour = vec![Colour::White; self.nodes.len()];
        for (id, _) in self.live() {
            self.descend(id, &mut colour)?;
        }
        Ok(())
    }

    fn descend(&self, id: NodeId, colour: &mut Vec<Colour>) -> Result<(), Error> {
        match colour[id.index()] {
            Colour::Black => return Ok(()),
            Colour::Grey => return Err(Error::Cyclic(id)),
            Colour::White => {}
        }
        colour[id.index()] = Colour::Grey;
        for port in 0..self.node(id).inputs.len() {
            if let Source::Port { node, .. } = self.node(id).inputs[port] {
                self.descend(node, colour)?;
            }
        }
        colour[id.index()] = Colour::Black;
        Ok(())
    }
}

/// A graph that does not hold together.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A node's port counts disagree with its kind.
    Width {
        node: NodeId,
        expected: Arity,
        inputs: usize,
        outputs: usize,
    },
    /// A reader naming a port that is not there.
    Dangling { source: Source, sink: Sink },
    /// A link recorded at one end and not the other — the bug the
    /// representation exists to make loud.
    Torn { source: Source, sink: Sink },
    /// A node that reaches itself.
    Cyclic(NodeId),
    /// Two nodes claiming to be the same end of one branch.
    BranchTwice {
        branch: BranchId,
        fork: bool,
        first: NodeId,
        second: NodeId,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Width {
                node,
                expected,
                inputs,
                outputs,
            } => write!(
                f,
                "node {} is {} -> {} where its kind is {}",
                node, inputs, outputs, expected
            ),
            Error::Dangling { source, sink } => {
                write!(f, "{} reads {}, which is not a port", sink, source)
            }
            Error::Torn { source, sink } => write!(
                f,
                "the link between {} and {} is recorded at one end only",
                source, sink
            ),
            Error::Cyclic(node) => write!(f, "node {} reaches itself", node),
            Error::BranchTwice {
                branch,
                fork,
                first,
                second,
            } => write!(
                f,
                "nodes {} and {} are both the {} of branch {}",
                first,
                second,
                if *fork { "fork" } else { "select" },
                branch
            ),
        }
    }
}

impl std::error::Error for Error {}

// ---- an order to run them in -----------------------------------------------------

/// The live nodes in an order that runs producers first, smallest id first
/// among those ready — which is roughly the order they were built in, so
/// the term that comes out reads like the term that went in.
pub(crate) fn schedule(graph: &Graph) -> Vec<NodeId> {
    let mut waiting: HashMap<NodeId, usize> = graph
        .live()
        .map(|(id, _)| {
            let unmet = graph
                .node(id)
                .inputs
                .iter()
                .filter(|src| matches!(src, Source::Port { .. }))
                .count();
            (id, unmet)
        })
        .collect();
    let mut ready: BinaryHeap<Reverse<u32>> = waiting
        .iter()
        .filter(|&(_, &unmet)| unmet == 0)
        .map(|(id, _)| Reverse(id.0))
        .collect();
    let mut order = Vec::with_capacity(waiting.len());
    while let Some(Reverse(raw)) = ready.pop() {
        let id = NodeId(raw);
        order.push(id);
        for port in 0..graph.kind(id).arity().outputs {
            for &sink in graph.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink {
                    let unmet = waiting.get_mut(&node).expect("a live reader");
                    *unmet -= 1;
                    if *unmet == 0 {
                        ready.push(Reverse(node.0));
                    }
                }
            }
        }
    }
    debug_assert_eq!(order.len(), waiting.len(), "the graph is acyclic");
    order
}

// ---- printing --------------------------------------------------------------------

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// `in2` for the boundary, `#3.1` for output port 1 of node 3.
impl fmt::Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Source::Input(i) => write!(f, "in{}", i),
            Source::Port { node, port } => write!(f, "{}.{}", node, port),
        }
    }
}

/// `out2` for the boundary, `#3:1` for *input* port 1 of node 3 — the colon
/// is what says which side of a box the port is on.
impl fmt::Display for Sink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sink::Output(i) => write!(f, "out{}", i),
            Sink::Port { node, port } => write!(f, "{}:{}", node, port),
        }
    }
}

impl fmt::Display for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Id(n) => write!(f, "id({})", n),
            NodeKind::Copy(n) => write!(f, "copy({})", n),
            NodeKind::Drop(n) => write!(f, "drop({})", n),
            NodeKind::Op(prim) => write!(f, "{}", prim),
            NodeKind::Call { target, .. } => write!(f, "call #{}", usize::from(*target)),
            NodeKind::Fork { arity, branch } => write!(f, "fork({}){}", arity, branch),
            NodeKind::Select { arity, branch } => write!(f, "select({}){}", arity, branch),
        }
    }
}

/// A graph as a box per line: what each one reads, and what reads it.
///
/// One flat listing, however many branches it holds — there is no longer
/// anything nested to indent.
impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "inputs {}", self.inputs.len())?;
        for (id, kind) in self.live() {
            write!(f, "  {} {} <-", id, kind)?;
            if self.node(id).inputs.is_empty() {
                write!(f, " ()")?;
            }
            for src in &self.node(id).inputs {
                write!(f, " {}", src)?;
            }
            let readers: usize = (0..kind.arity().outputs)
                .map(|port| self.sinks(Source::Port { node: id, port }).len())
                .sum();
            writeln!(f, "   [{} reader(s)]", readers)?;
        }
        write!(f, "outputs")?;
        if self.outputs.is_empty() {
            write!(f, " ()")?;
        }
        for src in &self.outputs {
            write!(f, " {}", src)?;
        }
        writeln!(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::rules;
    use crate::diagram2::tests::built;

    #[test]
    fn padding_slides_wires_underneath() {
        let (_terms, graph) = built("not");
        let padded = under(&graph, 2);
        padded.check().unwrap();
        assert_eq!(padded.arity(), Arity::new(3, 3));
        // The fresh wires pass straight through beneath...
        assert_eq!(padded.outputs()[0], Source::Input(0));
        assert_eq!(padded.outputs()[1], Source::Input(1));
        // ...and the box now reads the shifted boundary.
        let (not, _) = padded.live().next().unwrap();
        assert_eq!(padded.sources(not), [Source::Input(2)]);
        assert!(isomorphic(&graph, &under(&graph, 0)));
    }

    #[test]
    fn two_graphs_are_one_diagram_or_they_are_not() {
        let (_t, a) = built("push 1 push 2 add");
        let (_t, b) = built("push 1 push 2 add");
        assert!(isomorphic(&a, &b));
        let (_t, c) = built("push 1 push 3 add");
        assert!(
            !isomorphic(&a, &c),
            "a different literal is a different program"
        );
        let (_t, d) = built("not");
        assert!(!isomorphic(&a, &d));
        let (_t, e) = built("branch { add } { add }");
        let (_t, f) = built("branch { add } { add }");
        assert!(isomorphic(&e, &f), "branch ids pair, they are not compared");
        let (_t, g) = built("branch { add } { sub }");
        assert!(!isomorphic(&e, &g));
    }

    /// Dead slots and the numbers ids hold are not part of what a graph
    /// says: a graph that rewrote its boxes away is the wires it left.
    #[test]
    fn sameness_ignores_the_graveyard() {
        let (_t, mut rewritten) = built("swap swap");
        for _ in 0..2 {
            let (id, _) = rewritten.live().next().expect("a swap to spend");
            let step = rules::propose(&rewritten, &[rules::Law::SwapElim], id)
                .into_iter()
                .next()
                .expect("swap-elim fires");
            rules::apply(&mut rewritten, &step).unwrap();
        }
        assert_eq!(rewritten.live_count(), 0);
        let mut wires = Graph::empty(2);
        wires.close(vec![Source::Input(0), Source::Input(1)]);
        assert!(isomorphic(&rewritten, &wires));
        let mut crossed = Graph::empty(2);
        crossed.close(vec![Source::Input(1), Source::Input(0)]);
        assert!(!isomorphic(&rewritten, &crossed), "the boundary is pinned");
    }
}
