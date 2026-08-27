//! Graphs, and rewriting one by another: boxes, the links between them,
//! what can be asked of the pair, and how a piece of one is swapped for a
//! piece of another.
//!
//! This is the layer [`crate::diagram2`] is an engine over, kept apart from
//! it because the two are different things. A graph knows what a box takes
//! and leaves, what reads what, whether it holds together, and whether
//! another graph is the same diagram. It knows nothing about terms, laws,
//! tactics or proofs; the traffic in that direction is all diagram2's, which
//! [`build`](crate::diagram2::build)s one from a term and
//! [`read_back`](crate::diagram2::read_back)s one out again.
//!
//! Nothing here is generic, and that is deliberate. A [`NodeKind`] is a
//! Hanoi [`Prim`], a call into a Hanoi library, or one of the structural
//! boxes the term language has. The point of the split is that the graph is
//! its own layer, not that it is anybody's graph.
//!
//! ## Two invariants, and where they are kept
//!
//! **A link is written at both ends**: a [`Source`] names the one producer
//! an input port reads, a [`Sink`] names one reader of an output port, and
//! both lists are kept. The constructors here write the two directions
//! together, which is why they cannot be recorded apart; a rewriter that
//! re-points one end and forgets the other is what [`Graph::check`] is for,
//! and it is caught at the rewrite rather than surviving as a graph that
//! reads back wrong.
//!
//! **A rewrite is a [`Pair`], put down where a [`Match`] says.** A pair is
//! two graphs offered as interchangeable; a match is the claim that one of
//! them *is* some part of a host graph. [`Pair::apply`] takes both and does
//! the swap — and it checks first, because a match is a claim anyone may
//! state and [`check_match`] is what makes it true.
//!
//! The check is **stricter than substitution**, and that strictness is the
//! whole safety story. A pattern is a window with loose ends: the sources
//! its boundary inputs stand for, the outside readers its boundary outputs
//! serve. A splice re-points exactly those, so the match has to account for
//! exactly those — every reader of every exported port, and no link from the
//! window's own boundary back into the window. Anything unaccounted for
//! would be left dangling, so nothing is spliced until all of it adds up.
//! The splice itself is private, and [`Pair::apply`] is the only way to
//! reach it.
//!
//! What a pair *means* — which law it spells, whether anything proved its
//! two sides equal — is not asked here. [`rules`](crate::diagram2::rules) is
//! what produces pairs of equivalent graphs, and once it has, every rewrite
//! in this crate is one of them applied somewhere.
//!
//! ## Embeddings compose
//!
//! A match is a map: this graph's boxes, boundary and branches, read as
//! another's. [`Embedding`] is that map kept in a form that outlives a
//! rewrite, and [`Embedding::carry`] composes two of them — a match against
//! an inner graph, said against the outer one.
//!
//! That is what lets a rewrite stated about one graph be spent inside
//! another, and a whole *run* of them likewise: each step makes boxes on
//! both sides, [`Embedding::extend`] pairs them up, and the next step can
//! name them. [`transplant`](crate::diagram2::rules::transplant) is that
//! loop, and what it answers with is the run said in the host's coordinates
//! — a proof about the host, replayable on its own.

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
pub struct BranchId(u32);

impl BranchId {
    /// Where this branch sits in the order its graph handed them out, which
    /// is what [`rules`](crate::diagram2::rules) keys a renaming by.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id at a position — what a caller naming a branch of a graph it is
    /// building needs, the same way [`NodeId::at`] names a box.
    pub fn at(index: usize) -> BranchId {
        BranchId(u32::try_from(index).expect("a graph fits in u32"))
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
    /// [docs/totality.md](../../../docs/totality.md) — sound because every
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
    /// and [`no_structure`](../../../hana) are asking about. The branch layer
    /// survives on purpose.
    pub fn is_structural(&self) -> bool {
        matches!(
            self,
            NodeKind::Id(_) | NodeKind::Copy(_) | NodeKind::Op(Prim::Swap)
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Node {
    kind: NodeKind,
    /// One source per input port.
    inputs: Vec<Source>,
    /// The readers of each output port.
    outputs: Vec<Vec<Sink>>,
}

/// A program as boxes and the links between them.
///
/// Nodes are only ever deleted, never moved, so a [`NodeId`] stays valid
/// (as a *dead* id, once its node is gone) for the life of the graph.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Graph {
    nodes: Vec<Option<Node>>,
    /// The readers of each boundary input, deepest first.
    inputs: Vec<Vec<Sink>>,
    /// What each boundary output reads, deepest first.
    outputs: Vec<Source>,
    /// Branch ids handed out so far. Never reused, so a `fork` and the
    /// `select` it was built with name each other for the life of the graph.
    branches: u32,
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

    /// The window one box fills: its input ports reading the boundary, every
    /// output port exported in order.
    ///
    /// The pattern side of every one-box rewrite, and the shape a caller
    /// replacing a single box states its [`Match`] against.
    pub(crate) fn of_box(kind: NodeKind) -> Graph {
        let arity = kind.arity();
        let mut graph = Graph::empty(arity.inputs);
        let kind = graph.refresh(kind);
        let ports = graph.add(kind, (0..arity.inputs).map(Source::Input).collect());
        graph.close(ports);
        graph
    }

    /// The same box with a branch id of this graph's own — a branch id off
    /// another graph names nothing here, which is why a pattern built out of
    /// a host's boxes mints its own and lets [`Match::branches`] carry the
    /// correspondence back.
    pub(crate) fn refresh(&mut self, kind: NodeKind) -> NodeKind {
        match kind {
            NodeKind::Fork { arity, .. } => NodeKind::Fork {
                arity,
                branch: self.next_branch(),
            },
            NodeKind::Select { arity, .. } => NodeKind::Select {
                arity,
                branch: self.next_branch(),
            },
            other => other,
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

    /// How many branch ids this graph has handed out.
    ///
    /// What a caller building a graph that must agree with another on which
    /// branch is which needs: ids are never reused, so a count is a name for
    /// the next one.
    pub fn branch_count(&self) -> usize {
        self.branches as usize
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

    fn node(&self, id: NodeId) -> &Node {
        self.nodes[id.index()]
            .as_ref()
            .expect("a live node was asked for")
    }

    fn node_mut(&mut self, id: NodeId) -> &mut Node {
        self.nodes[id.index()]
            .as_mut()
            .expect("a live node was asked for")
    }

    fn sinks_mut(&mut self, src: Source) -> &mut Vec<Sink> {
        match src {
            Source::Input(i) => &mut self.inputs[i],
            Source::Port { node, port } => &mut self.node_mut(node).outputs[port],
        }
    }

    /// Writes one end of a link: what `sink` reads.
    fn set_source(&mut self, sink: Sink, src: Source) {
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
        // A box put down carrying a branch id this graph has not handed out
        // is a graph built by *renumbering* another's boxes — a region
        // lifted out, a graph implanted. Counting it here is what keeps
        // `next_branch` clear of the ids the graph already holds, wherever
        // they came from.
        if let NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } = &kind {
            self.branches = self.branches.max(branch.0 + 1);
        }
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
    fn unlink(&mut self, src: Source, sink: Sink) {
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
/// Whole-graph equality, not [`find`]'s embedding: no window, no
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

    fn valid(&self, src: Source) -> bool {
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

// ---- a pair, an embedding, and the splice ----------------------------------------

/// Which side of a [`Pair`] to match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Match the left-hand side, leave the right.
    Forward,
    /// Match the right-hand side, leave the left.
    Backward,
}

impl Direction {
    pub fn flipped(self) -> Direction {
        match self {
            Direction::Forward => Direction::Backward,
            Direction::Backward => Direction::Forward,
        }
    }
}

/// Why two graphs are not a [`Pair`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unpaired {
    /// They do not take and leave the same thing, so no rewrite by them
    /// could keep a graph's arity.
    Interface(Arity, Arity),
    /// One of them is not a graph, and a side that is not a graph cannot be
    /// looked for or put down.
    Broken(Error),
}

impl fmt::Display for Unpaired {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unpaired::Interface(l, r) => write!(
                f,
                "relates a {} graph and a {} one, which is no equation",
                l, r
            ),
            Unpaired::Broken(e) => write!(f, "has a side that is not a graph: {}", e),
        }
    }
}

impl std::error::Error for Unpaired {}

/// Two graphs offered as interchangeable: wherever one is found, the other
/// may stand in its place.
///
/// This is the whole of what a rewrite needs. Where the pair *came from* —
/// which law it spells, whether anything proved the two sides equal — is
/// [`crate::diagram2::rules`]'s business and none of this module's: a
/// `Pair` is checked for being splice-able and nothing more, so the one
/// thing it guarantees is that a rewrite by it leaves a graph that still
/// holds together and still takes and leaves what it did.
///
/// Both sides pass [`Graph::check`] and they share an arity, both settled
/// once at construction so that [`Pair::apply`] can index either side
/// without asking again. The two also share a **branch-id namespace**: a
/// [`BranchId`] means the same branch on both sides, which is what lets a
/// rewrite carry a branch across rather than only make or delete one.
#[derive(Debug, Clone, PartialEq)]
pub struct Pair {
    lhs: Graph,
    rhs: Graph,
}

impl Pair {
    /// The two graphs as a pair, or why they are not one.
    pub fn new(lhs: Graph, rhs: Graph) -> Result<Pair, Unpaired> {
        if lhs.arity() != rhs.arity() {
            return Err(Unpaired::Interface(lhs.arity(), rhs.arity()));
        }
        lhs.check().map_err(Unpaired::Broken)?;
        rhs.check().map_err(Unpaired::Broken)?;
        Ok(Pair { lhs, rhs })
    }

    pub fn lhs(&self) -> &Graph {
        &self.lhs
    }

    pub fn rhs(&self) -> &Graph {
        &self.rhs
    }

    /// What this direction takes out, and what it puts in.
    pub fn sides(&self, dir: Direction) -> (&Graph, &Graph) {
        match dir {
            Direction::Forward => (&self.lhs, &self.rhs),
            Direction::Backward => (&self.rhs, &self.lhs),
        }
    }

    /// The side a direction looks for.
    pub fn pattern(&self, dir: Direction) -> &Graph {
        self.sides(dir).0
    }

    /// Every embedding of the pattern side in `graph` — see [`find`] for
    /// what it declines to look for.
    pub fn find(&self, graph: &Graph, dir: Direction) -> Vec<Match> {
        find(graph, self.pattern(dir))
    }

    /// Whether `at` really points at a subgraph this direction may replace.
    pub fn check(&self, graph: &Graph, dir: Direction, at: &Match) -> Result<(), Mismatch> {
        check_match(graph, self.pattern(dir), at)
    }

    /// One rewrite: the subgraph `at` points at, replaced by the other
    /// side.
    ///
    /// The whole of the checking is here, and none of it searches. The match
    /// is held to being an isomorphism onto an **induced** subgraph with
    /// every loose end accounted for — [`check_match`] is what that means,
    /// and it is stricter than a substitution needs to be, because a
    /// substitution that is not induced strands a link. Only then is the
    /// subgraph deleted and the other side put in its place.
    ///
    /// The answer is the **embedding of what went in**, which is where the
    /// way back lands. This is the one place a graph cannot copy a term: a
    /// path survived a rewrite unchanged, but a [`Match`] names host
    /// [`NodeId`]s and the replacement's boxes are freshly allocated, so the
    /// inverse has to be handed over rather than derived by flipping a bit.
    ///
    /// A refusal changes nothing: the check runs to completion before the
    /// first box is deleted.
    pub fn apply(&self, graph: &mut Graph, dir: Direction, at: &Match) -> Result<Match, Mismatch> {
        let (pattern, replacement) = self.sides(dir);
        check_match(graph, pattern, at)?;
        Ok(splice(graph, replacement, at))
    }
}

/// A subgraph, pointed at: the claim that this part of a host graph *is*
/// some pattern graph.
///
/// Not a path. A term's subterm has a name in the term; a graph's subgraph
/// has none, so the embedding itself is the name — which box is which, what
/// the pattern's boundary stands for outside, and who reads what it leaves.
///
/// It is a **claim**, not a proof: nothing about a `Match` is true until
/// [`check_match`] has said so, which is why every field is public and
/// anyone may state one. [`Pair::apply`] checks before it splices, so a
/// wrong claim costs a [`Mismatch`] rather than a wrong graph.
///
/// [`outputs`](Match::outputs) is the one field that is a **choice** rather
/// than a reading. When two of a pattern's boundary outputs name one port,
/// nothing in the host says which of that port's outside readers belong to
/// which; the split is whoever states the match's business, and the check
/// only holds it to being consistent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    /// Image of the pattern's boxes, indexed by the pattern's own node
    /// index. A pattern deletes nothing, so those indices are dense.
    pub nodes: Vec<NodeId>,
    /// What the pattern's boundary input `i` stands for in the host.
    pub inputs: Vec<Source>,
    /// The host sinks the pattern's boundary output `j` serves.
    pub outputs: Vec<Vec<Sink>>,
    /// Image of the pattern's branch ids, by the pattern's own id. A branch
    /// id is graph-local, so the correspondence is recorded rather than
    /// compared.
    pub branches: Vec<BranchId>,
}

impl Match {
    /// This match said again in terms of the boxes that stand where its own
    /// used to.
    ///
    /// What undoing a run of rewrites needs: undoing a step puts boxes
    /// **back**, and a box put back is a new box with a new [`NodeId`], so
    /// every match still to be undone has to be said again in the ids the
    /// undo before it handed out.
    pub fn rebase(&self, moved: &HashMap<NodeId, NodeId>) -> Match {
        let now = |id: NodeId| moved.get(&id).copied().unwrap_or(id);
        let port = |src: Source| match src {
            Source::Port { node, port } => Source::Port {
                node: now(node),
                port,
            },
            boundary => boundary,
        };
        let reader = |sink: Sink| match sink {
            Sink::Port { node, port } => Sink::Port {
                node: now(node),
                port,
            },
            boundary => boundary,
        };
        Match {
            nodes: self.nodes.iter().map(|&id| now(id)).collect(),
            inputs: self.inputs.iter().map(|&src| port(src)).collect(),
            outputs: self
                .outputs
                .iter()
                .map(|sinks| sinks.iter().map(|&sink| reader(sink)).collect())
                .collect(),
            branches: self.branches.clone(),
        }
    }
}

/// One graph's names read in another, kept as a map so it can survive both
/// of them being rewritten.
///
/// A [`Match`] is a claim about one moment: its [`nodes`](Match::nodes) are
/// indexed by the pattern's own dense box order, which stops being a reading
/// the first time that pattern is itself rewritten. An `Embedding` is the
/// same correspondence written so it can be **extended**, which is what
/// carrying a whole run of rewrites across needs — every step makes boxes on
/// both sides, and they have to be paired up before the next step can be
/// said.
///
/// Composition is [`Embedding::carry`]. Given a match of `P` in `G` and an
/// embedding of `G` in `H`, it answers the match of `P` in `H`, which is
/// what lets a rewrite stated about `G` be spent inside `H` instead. That
/// the answer is still a *claim* is the usual discipline: it goes through
/// [`Pair::apply`] like any other, so a wrongly carried match is refused
/// rather than believed.
///
/// It carries the boundary too, and that is the part worth saying out loud.
/// A boundary input of `G` is a source in `H` — whatever `G`'s window reads
/// there — and a boundary *output* of `G` is a **list** of sinks in `H`,
/// since one port of a window may be read by several boxes outside it. A
/// match that hands one of its ports to `G`'s boundary therefore hands it,
/// in `H`, to every reader that boundary stood for; anything less would
/// strand a link, and [`check_match`] would refuse it.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Embedding {
    /// What the outer graph has where the inner one has this box.
    nodes: HashMap<NodeId, NodeId>,
    /// What the inner graph's boundary input `i` reads in the outer one.
    inputs: Vec<Source>,
    /// The outer sinks the inner graph's boundary output `j` serves.
    outputs: Vec<Vec<Sink>>,
    /// What the outer graph calls the inner one's branch.
    branches: HashMap<BranchId, BranchId>,
}

impl Embedding {
    /// The correspondence a match states, in a form that outlives it.
    ///
    /// The match's pattern is the inner graph and its host the outer one, so
    /// this is only as true as the match is — [`check_match`] is what says
    /// so, and a caller that has not asked is carrying claims rather than
    /// readings.
    pub fn of(at: &Match) -> Embedding {
        Embedding {
            nodes: at
                .nodes
                .iter()
                .enumerate()
                .map(|(i, &to)| (NodeId::at(i), to))
                .collect(),
            inputs: at.inputs.clone(),
            outputs: at.outputs.clone(),
            branches: at
                .branches
                .iter()
                .enumerate()
                .map(|(i, &to)| (BranchId::at(i), to))
                .collect(),
        }
    }

    /// A match against the inner graph, said against the outer one.
    ///
    /// `None` where the match names a box, a boundary or a branch this
    /// embedding does not carry — which, for an embedding kept up to date by
    /// [`Embedding::extend`], means the match is not about the inner graph
    /// at all.
    pub fn carry(&self, at: &Match) -> Option<Match> {
        let source = |src: Source| match src {
            Source::Input(i) => self.inputs.get(i).copied(),
            Source::Port { node, port } => self
                .nodes
                .get(&node)
                .map(|&node| Source::Port { node, port }),
        };
        // One inner sink is a *list* of outer ones: a boundary output stands
        // for every reader outside the window.
        let readers = |sink: Sink| match sink {
            Sink::Output(j) => self.outputs.get(j).cloned(),
            Sink::Port { node, port } => self
                .nodes
                .get(&node)
                .map(|&node| vec![Sink::Port { node, port }]),
        };
        Some(Match {
            nodes: at
                .nodes
                .iter()
                .map(|id| self.nodes.get(id).copied())
                .collect::<Option<_>>()?,
            inputs: at
                .inputs
                .iter()
                .map(|&src| source(src))
                .collect::<Option<_>>()?,
            outputs: at
                .outputs
                .iter()
                .map(|sinks| {
                    let carried: Option<Vec<Vec<Sink>>> =
                        sinks.iter().map(|&sink| readers(sink)).collect();
                    carried.map(|lists| lists.concat())
                })
                .collect::<Option<_>>()?,
            branches: at
                .branches
                .iter()
                .map(|b| self.branches.get(b).copied())
                .collect::<Option<_>>()?,
        })
    }

    /// What one rewrite, run on both sides, added to the correspondence.
    ///
    /// Both arguments are the answer [`Pair::apply`] gave — the embedding of
    /// what it put down — `inner` from the run on the inner graph and
    /// `outer` from the run on the outer one. The same replacement went down
    /// in both, so its boxes and its branches line up in order, and that is
    /// the whole of the pairing.
    ///
    /// Nothing is taken away. A box a rewrite deleted is a box no later
    /// rewrite can name — an id is never reused — so a stale entry is
    /// unreachable rather than wrong.
    pub fn extend(&mut self, inner: &Match, outer: &Match) {
        debug_assert_eq!(
            (inner.nodes.len(), inner.branches.len()),
            (outer.nodes.len(), outer.branches.len()),
            "one replacement went down on both sides"
        );
        for (&here, &there) in inner.nodes.iter().zip(&outer.nodes) {
            self.nodes.insert(here, there);
        }
        for (&here, &there) in inner.branches.iter().zip(&outer.branches) {
            self.branches.insert(here, there);
        }
    }

    /// What the outer graph has where the inner one has this box.
    pub fn node(&self, id: NodeId) -> Option<NodeId> {
        self.nodes.get(&id).copied()
    }
}

/// How a claimed embedding failed to be one. Every variant names the port
/// that disagreed, because that is the whole content of the check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mismatch {
    /// The match names a different number of boxes, inputs, outputs or
    /// branches than the pattern has, or names one box twice.
    Shape,
    /// A box the match names is not there.
    Gone(NodeId),
    /// The box at that node is not the one the pattern has in its place.
    Kind(NodeId),
    /// That input port reads something other than what the pattern says.
    Edge(Sink),
    /// That port's readers are not the ones the match accounts for — a
    /// reader the pattern does not export, or one it claims twice, or one it
    /// claims that reads something else.
    Readers(Source),
    /// A link the pattern does not have: the match sends a boundary of its
    /// own into the very subgraph it is matching, so what it points at is
    /// not isomorphic to the pattern but to the pattern plus an edge.
    Induced(Source),
}

/// Said without naming the pattern, since the pattern is whatever the caller
/// was matching; [`crate::diagram2::rules`] puts the law's name in front of
/// this when the pattern was a law's side.
impl fmt::Display for Mismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mismatch::Shape => write!(f, "the match is not the shape of the pattern"),
            Mismatch::Gone(node) => write!(f, "the match names {}, which is not there", node),
            Mismatch::Kind(node) => {
                write!(f, "{} is not the box the pattern has in its place", node)
            }
            Mismatch::Edge(sink) => write!(
                f,
                "{} reads something the pattern does not say it reads",
                sink
            ),
            Mismatch::Readers(src) => write!(
                f,
                "the readers of {} are not the ones the match claims",
                src
            ),
            Mismatch::Induced(src) => write!(
                f,
                "{} is inside the match, so what it points at is the pattern plus a link",
                src
            ),
        }
    }
}

impl std::error::Error for Mismatch {}

/// Whether the match points at a subgraph isomorphic to the pattern, and so
/// whether replacing it is safe.
///
/// This is **stricter than substitution**, and the strictness is the point.
/// A pattern is a window with loose ends — the sources its boundary inputs
/// stand for, the outside readers its boundary outputs serve — and a splice
/// re-points exactly those. Anything the match does not account for would
/// be left dangling, so the check accounts for all of it before a box is
/// touched.
///
/// Five conditions, and between them they say "isomorphic onto an induced
/// subgraph, with every loose end accounted for":
///
/// 1. **Shape** — one image per box, one source per boundary input, one
///    reader list per boundary output, and no box named twice.
/// 2. **Kinds** — the same box, modulo the branch renaming the match
///    carries.
/// 3. **Edges** — every input port of a matched box reads what the pattern
///    says it reads.
/// 4. **Fullness** — every output port's readers in the host are *exactly*
///    the pattern's own readers plus the ones the match hands to the
///    boundary. A port the pattern does not export therefore has no reader
///    at all, which is what makes `dead-node` a rule rather than a test, and
///    a reader nobody claimed is a loose end the rewrite would strand.
/// 5. **Inducedness** — no boundary of the match points back inside it.
///
/// The indexing here is unchecked on purpose: a pattern comes from a
/// [`Pair`], which holds it to [`Graph::check`], so every source it names is
/// a source it has. What is *not* trusted is the match, and every field of
/// it is measured against the pattern before it is used to index anything.
pub fn check_match(graph: &Graph, pattern: &Graph, at: &Match) -> Result<(), Mismatch> {
    debug_assert!(
        pattern.nodes.iter().all(Option::is_some),
        "a pattern deletes nothing, so its boxes are dense"
    );
    let boxes = pattern.nodes.len();
    if at.nodes.len() != boxes
        || at.inputs.len() != pattern.inputs.len()
        || at.outputs.len() != pattern.outputs.len()
        || at.branches.len() != pattern.branches as usize
    {
        return Err(Mismatch::Shape);
    }
    let inside: HashSet<NodeId> = at.nodes.iter().copied().collect();
    if inside.len() != at.nodes.len()
        || at.branches.iter().collect::<HashSet<_>>().len() != at.branches.len()
    {
        return Err(Mismatch::Shape);
    }
    for &id in &at.nodes {
        if !graph.is_live(id) {
            return Err(Mismatch::Gone(id));
        }
    }
    // A pattern source, read in the host.
    let image = |src: Source| match src {
        Source::Input(i) => at.inputs[i],
        Source::Port { node, port } => Source::Port {
            node: at.nodes[node.index()],
            port,
        },
    };

    for i in 0..boxes {
        let here = NodeId::at(i);
        let host = at.nodes[i];
        if !same_kind(pattern.kind(here), graph.kind(host), &at.branches) {
            return Err(Mismatch::Kind(host));
        }
        // Edges.
        for (port, &src) in pattern.sources(here).iter().enumerate() {
            let sink = Sink::Port { node: host, port };
            if graph.sources(host).get(port) != Some(&image(src)) {
                return Err(Mismatch::Edge(sink));
            }
        }
        // Fullness.
        for port in 0..pattern.kind(here).arity().outputs {
            let mine = Source::Port { node: here, port };
            let theirs = Source::Port { node: host, port };
            let mut want: Vec<Sink> = Vec::new();
            for &sink in pattern.sinks(mine) {
                match sink {
                    Sink::Port { node, port } => want.push(Sink::Port {
                        node: at.nodes[node.index()],
                        port,
                    }),
                    Sink::Output(j) => want.extend(at.outputs[j].iter().copied()),
                }
            }
            if !same_readers(&want, graph.sinks(theirs)) {
                return Err(Mismatch::Readers(theirs));
            }
        }
    }

    // Every reader the match hands to a boundary output really does read
    // what that output names — which is the whole check for an output that
    // names a boundary *input*, since no box's port covers those.
    for (j, &src) in pattern.outputs().iter().enumerate() {
        let want = image(src);
        for &sink in &at.outputs[j] {
            if reads(graph, sink) != Some(want) {
                return Err(Mismatch::Readers(want));
            }
            if let Sink::Port { node, .. } = sink
                && inside.contains(&node)
            {
                return Err(Mismatch::Induced(want));
            }
        }
    }
    for &src in &at.inputs {
        if let Source::Port { node, .. } = src
            && inside.contains(&node)
        {
            return Err(Mismatch::Induced(src));
        }
    }
    Ok(())
}

/// The subgraph out, the replacement in, and the embedding of what went in —
/// which is where the way back lands.
///
/// Unchecked: [`check_match`] is what makes this safe, and [`Pair::apply`]
/// is where the two are put together. Nothing else calls it.
fn splice(graph: &mut Graph, replacement: &Graph, at: &Match) -> Match {
    let inside: HashSet<NodeId> = at.nodes.iter().copied().collect();

    // Out. A link to a box that is also going away needs no unlinking: the
    // list it would be removed from goes with it.
    for &id in &at.nodes {
        let sources = graph.node(id).inputs.clone();
        for (port, &src) in sources.iter().enumerate() {
            let doomed = matches!(src, Source::Port { node, .. } if inside.contains(&node));
            if !doomed {
                graph.unlink(src, Sink::Port { node: id, port });
            }
        }
    }
    for &id in &at.nodes {
        graph.nodes[id.index()] = None;
    }

    // A branch the replacement keeps is the one the match named; a branch it
    // introduces is new to the host.
    let mut branches = at.branches.clone();
    while branches.len() < replacement.branches as usize {
        branches.push(graph.next_branch());
    }

    // In. A pattern builds its boxes producers-first, so its own order is
    // one the host can add them in.
    let mut fresh: Vec<NodeId> = Vec::with_capacity(replacement.nodes.len());
    let carry = |src: Source, at: &Match, fresh: &[NodeId]| match src {
        Source::Input(i) => at.inputs[i],
        Source::Port { node, port } => Source::Port {
            node: fresh[node.index()],
            port,
        },
    };
    for slot in &replacement.nodes {
        let node = slot.as_ref().expect("a pattern deletes nothing");
        let kind = rename(&node.kind, &branches);
        let inputs = node.inputs.iter().map(|&s| carry(s, at, &fresh)).collect();
        fresh.push(graph.add_node(kind, inputs));
    }

    // And the loose ends, re-pointed: everything the match handed to a
    // boundary output now names what the replacement leaves there. This is
    // the one move that grows a port's readers, and where `copy-elim` turns
    // a wiring diagram into a cartesian one.
    for (j, &src) in replacement.outputs().iter().enumerate() {
        let target = carry(src, at, &fresh);
        for &sink in &at.outputs[j] {
            // Whatever the reader named before has to be told it is no
            // longer read there — unless it was one of the boxes that just
            // went away, which took its reader list with it. A rule whose
            // side exports a boundary *input* is where this bites: the
            // source survives the rewrite, so the stale link would too.
            if let Some(old) = reads(graph, sink)
                && graph.valid(old)
            {
                graph.unlink(old, sink);
            }
            graph.set_source(sink, target);
            graph.sinks_mut(target).push(sink);
        }
    }

    Match {
        nodes: fresh,
        // The pattern's boundary was outside the match and is untouched, and
        // the readers that were handed to output `j` now read the
        // replacement's output `j` — so the way back is the same embedding
        // over the other side.
        inputs: at.inputs.clone(),
        outputs: at.outputs.clone(),
        branches: branches[..replacement.branches as usize].to_vec(),
    }
}

/// The same box, modulo the branch renaming — which is what a derived
/// `PartialEq` on [`NodeKind`] cannot be, since a branch id is graph-local
/// and two graphs that mean the same thing need not have hit on the same
/// numbers.
fn same_kind(pattern: &NodeKind, host: &NodeKind, branches: &[BranchId]) -> bool {
    let named = |b: &BranchId| branches.get(b.index()).copied();
    match (pattern, host) {
        (
            NodeKind::Fork { arity, branch },
            NodeKind::Fork {
                arity: n,
                branch: b,
            },
        ) => arity == n && named(branch) == Some(*b),
        (
            NodeKind::Select { arity, branch },
            NodeKind::Select {
                arity: n,
                branch: b,
            },
        ) => arity == n && named(branch) == Some(*b),
        (NodeKind::Fork { .. } | NodeKind::Select { .. }, _) => false,
        (_, NodeKind::Fork { .. } | NodeKind::Select { .. }) => false,
        (a, b) => a == b,
    }
}

/// The same box **ignoring** branch ids — what the search prunes on, since
/// it binds the renaming as it goes and `same_kind` is what holds the
/// binding it settled on. Also what a caller looking for boxes a pattern
/// *could* match wants, before any renaming is settled.
pub fn kinds_fit(pattern: &NodeKind, host: &NodeKind) -> bool {
    match (pattern, host) {
        (NodeKind::Fork { arity, .. }, NodeKind::Fork { arity: n, .. })
        | (NodeKind::Select { arity, .. }, NodeKind::Select { arity: n, .. }) => arity == n,
        (NodeKind::Fork { .. } | NodeKind::Select { .. }, _) => false,
        (_, NodeKind::Fork { .. } | NodeKind::Select { .. }) => false,
        (a, b) => a == b,
    }
}

/// A replacement's box, with its branch ids read as the host's.
fn rename(kind: &NodeKind, branches: &[BranchId]) -> NodeKind {
    match kind {
        NodeKind::Fork { arity, branch } => NodeKind::Fork {
            arity: *arity,
            branch: branches[branch.index()],
        },
        NodeKind::Select { arity, branch } => NodeKind::Select {
            arity: *arity,
            branch: branches[branch.index()],
        },
        other => other.clone(),
    }
}

/// Two reader lists holding the same sinks the same number of times. Order
/// is not part of what a port's readers are.
fn same_readers(want: &[Sink], have: &[Sink]) -> bool {
    if want.len() != have.len() {
        return false;
    }
    let mut tally: HashMap<Sink, isize> = HashMap::new();
    for &s in want {
        *tally.entry(s).or_default() += 1;
    }
    for &s in have {
        *tally.entry(s).or_default() -= 1;
    }
    tally.values().all(|&n| n == 0)
}

/// What one sink reads, or `None` if it is not a port of this graph.
fn reads(graph: &Graph, sink: Sink) -> Option<Source> {
    match sink {
        Sink::Output(i) => graph.outputs().get(i).copied(),
        Sink::Port { node, port } => {
            if !graph.is_live(node) {
                return None;
            }
            graph.sources(node).get(port).copied()
        }
    }
}

impl Graph {
    /// Another graph's boxes added to this one, its boundary inputs standing
    /// for the sources given, answering with the sources its boundary
    /// outputs name.
    ///
    /// This is what lets a piece of a program be **carried** rather than
    /// spelled out. A rule about a whole branch cannot name its arms — they
    /// are whatever the program put there — so it carries them, exactly as
    /// the term version carried subterms, and implants them where they go.
    ///
    /// The graph implanted keeps its own branches: its ids are moved clear
    /// of the ones this graph has already handed out, so nothing it carries
    /// collides with anything already here.
    pub(crate) fn implant(&mut self, arm: &Graph, inputs: &[Source]) -> Vec<Source> {
        debug_assert_eq!(inputs.len(), arm.inputs.len(), "one source per input");
        let base = self.branches;
        let mut fresh: Vec<NodeId> = Vec::with_capacity(arm.nodes.len());
        let carry = |src: Source, fresh: &[NodeId]| match src {
            Source::Input(i) => inputs[i],
            Source::Port { node, port } => Source::Port {
                node: fresh[node.index()],
                port,
            },
        };
        for slot in &arm.nodes {
            let node = slot
                .as_ref()
                .expect("an implanted graph keeps every box it builds");
            let takes = node.inputs.iter().map(|&s| carry(s, &fresh)).collect();
            fresh.push(self.add_node(lift(&node.kind, base), takes));
        }
        self.branches = self.branches.max(base + arm.branches);
        arm.outputs.iter().map(|&s| carry(s, &fresh)).collect()
    }
}

/// An implanted graph's own branch ids, moved clear of the ones its host has
/// already handed out.
fn lift(kind: &NodeKind, base: u32) -> NodeKind {
    match kind {
        NodeKind::Fork { arity, branch } => NodeKind::Fork {
            arity: *arity,
            branch: BranchId(base + branch.0),
        },
        NodeKind::Select { arity, branch } => NodeKind::Select {
            arity: *arity,
            branch: BranchId(base + branch.0),
        },
        other => other.clone(),
    }
}

// ---- finding one, which is not the checker's business ----------------------------

/// Every embedding of `pattern` in `graph`.
///
/// Search, and wrong the way a guess is wrong: everything it does is checked
/// by [`check_match`] anyway, so a matcher with a bug makes a rewrite that
/// is refused rather than one that changes what a program means.
///
/// It **declines** — answers with nothing, for every graph — where a pattern
/// does not pin its own match:
///
/// - a pattern with no boxes has nothing to anchor on, which is most of the
///   right-hand sides in [`rules`](crate::diagram2::rules)' table;
/// - a pattern that exports one port twice, or that exports a boundary
///   input, leaves the split of that source's outside readers a choice.
///
/// Those are the matches a caller has to *state* rather than read, and
/// [`Match`] is where it states them.
pub fn find(graph: &Graph, pattern: &Graph) -> Vec<Match> {
    graph
        .live()
        .map(|(id, _)| id)
        .flat_map(|seed| find_at(graph, pattern, seed))
        .collect()
}

/// [`find`], with the pattern's first box pinned to one node — what a
/// caller that read its pattern off that very box wants.
pub fn find_at(graph: &Graph, pattern: &Graph, seed: NodeId) -> Vec<Match> {
    find_pinned(graph, pattern, 0, seed)
}

/// [`find_at`], with pattern box `pat` — not necessarily the first —
/// pinned to `host`.
///
/// This is what lets a driver anchor a pattern at the box its *query* bound
/// rather than the box the pattern happens to begin with: a pattern is
/// built producers-first, so the box it is naturally *about* need not be
/// its first. The walk starts at `pat` and the answer is unchanged —
/// a [`Match`] is indexed by the pattern's own order whatever order the
/// search visited it in.
pub fn find_pinned(graph: &Graph, pattern: &Graph, pat: usize, host: NodeId) -> Vec<Match> {
    if !pins_itself(pattern) || pat >= pattern.nodes.len() || !graph.is_live(host) {
        return Vec::new();
    }
    let mut order: Vec<usize> = (0..pattern.nodes.len()).collect();
    order.remove(pat);
    order.insert(0, pat);
    let mut search = Search {
        graph,
        pattern,
        order,
        nodes: vec![None; pattern.nodes.len()],
        inputs: vec![None; pattern.inputs.len()],
        branches: vec![None; pattern.branches as usize],
        used: HashSet::new(),
        seed: host,
        found: Vec::new(),
    };
    search.walk(0);
    search.found
}

/// Whether a pattern says enough about itself to be looked for — what
/// [`find`] and its kin answer nothing for.
///
/// The conditions: at least one
/// box to anchor on, no source exported twice or exported straight from
/// the boundary, no boundary input nothing in the pattern reads, and no
/// branch id that no box witnesses.
///
/// The branch decline is what a pair that **skips** branch ids costs — the
/// skipping is how a [`BranchId`] means the same branch on both sides, and
/// an id no fork or select carries cannot be read off a match: its image in
/// the host is a choice, exactly as a reader-split is, so the pattern has to
/// be stated rather than searched for. The unread-input decline is the same
/// story one step over: a window that stands for a wire it never touches
/// cannot say which wire that is.
pub fn pins_itself(pattern: &Graph) -> bool {
    if pattern.nodes.is_empty() {
        return false;
    }
    if pattern.inputs.iter().any(|readers| readers.is_empty()) {
        return false;
    }
    let mut witnessed: HashSet<BranchId> = HashSet::new();
    for (_, kind) in pattern.live() {
        if let NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } = kind {
            witnessed.insert(*branch);
        }
    }
    if witnessed.len() != pattern.branches as usize {
        return false;
    }
    let mut seen = HashSet::new();
    pattern
        .outputs()
        .iter()
        .all(|src| matches!(src, Source::Port { .. }) && seen.insert(*src))
}

struct Search<'g> {
    graph: &'g Graph,
    pattern: &'g Graph,
    /// The order the walk visits pattern boxes in — the pinned box first,
    /// the rest in index order. [`Match::nodes`](Match) stays in pattern order;
    /// only the visiting changes.
    order: Vec<usize>,
    nodes: Vec<Option<NodeId>>,
    inputs: Vec<Option<Source>>,
    branches: Vec<Option<BranchId>>,
    used: HashSet<NodeId>,
    seed: NodeId,
    found: Vec<Match>,
}

impl Search<'_> {
    fn walk(&mut self, pos: usize) {
        if pos == self.order.len() {
            self.finish();
            return;
        }
        let i = self.order[pos];
        for host in self.candidates(pos) {
            let undo = self.assign(i, host);
            if let Some(undo) = undo {
                self.walk(pos + 1);
                self.undo(i, host, undo);
            }
        }
    }

    /// The host boxes worth trying for the box visited at `pos`.
    ///
    /// Once one box is fixed, its neighbours are: a port whose source is
    /// already known has only that source's readers to offer. Only a box
    /// nothing so far touches falls back on the whole graph, which is why
    /// two unconnected boxes still cost one sweep rather than a product.
    fn candidates(&self, pos: usize) -> Vec<NodeId> {
        if pos == 0 {
            return vec![self.seed];
        }
        let here = NodeId::at(self.order[pos]);
        for (port, &src) in self.pattern.sources(here).iter().enumerate() {
            let known = match src {
                Source::Input(l) => self.inputs[l],
                Source::Port { node, port } => {
                    self.nodes[node.index()].map(|n| Source::Port { node: n, port })
                }
            };
            if let Some(known) = known {
                return self
                    .graph
                    .sinks(known)
                    .iter()
                    .filter_map(|&sink| match sink {
                        Sink::Port { node, port: p } if p == port => Some(node),
                        _ => None,
                    })
                    .collect();
            }
        }
        self.graph.live().map(|(id, _)| id).collect()
    }

    /// Pins the pattern's box `i` to a host box, answering with the boundary
    /// inputs and the branch the assignment bound — the undo log, since a
    /// search that took them back by recomputing would be a second copy of
    /// this.
    fn assign(&mut self, i: usize, host: NodeId) -> Option<(Vec<usize>, Option<usize>)> {
        if self.used.contains(&host) {
            return None;
        }
        let here = NodeId::at(i);
        let kind = self.pattern.kind(here);
        let branch = match (kind, self.graph.kind(host)) {
            (NodeKind::Fork { branch, .. }, NodeKind::Fork { branch: b, .. })
            | (NodeKind::Select { branch, .. }, NodeKind::Select { branch: b, .. }) => {
                match self.branches[branch.index()] {
                    Some(held) if held != *b => return None,
                    Some(_) => None,
                    None => {
                        self.branches[branch.index()] = Some(*b);
                        Some(branch.index())
                    }
                }
            }
            _ => None,
        };
        if !kinds_fit(kind, self.graph.kind(host)) {
            if let Some(slot) = branch {
                self.branches[slot] = None;
            }
            return None;
        }
        let mut fixed = Vec::new();
        for (port, &src) in self.pattern.sources(here).iter().enumerate() {
            let Some(&hsrc) = self.graph.sources(host).get(port) else {
                self.rollback(&fixed, branch);
                return None;
            };
            match src {
                Source::Input(l) => match self.inputs[l] {
                    Some(held) if held != hsrc => {
                        self.rollback(&fixed, branch);
                        return None;
                    }
                    Some(_) => {}
                    None => {
                        self.inputs[l] = Some(hsrc);
                        fixed.push(l);
                    }
                },
                Source::Port { node, port } => {
                    // A producer not yet placed is not a mismatch: the walk
                    // visits the pinned box first, so a consumer can come
                    // before what feeds it, and `check_match` holds every
                    // edge at the end either way. In pattern order this arm
                    // never defers — a pattern is built producers-first.
                    match self.nodes[node.index()] {
                        None => {}
                        Some(n) if hsrc == (Source::Port { node: n, port }) => {}
                        Some(_) => {
                            self.rollback(&fixed, branch);
                            return None;
                        }
                    }
                }
            }
        }
        self.nodes[i] = Some(host);
        self.used.insert(host);
        Some((fixed, branch))
    }

    fn rollback(&mut self, fixed: &[usize], branch: Option<usize>) {
        for &l in fixed {
            self.inputs[l] = None;
        }
        if let Some(slot) = branch {
            self.branches[slot] = None;
        }
    }

    fn undo(&mut self, i: usize, host: NodeId, (fixed, branch): (Vec<usize>, Option<usize>)) {
        self.nodes[i] = None;
        self.used.remove(&host);
        self.rollback(&fixed, branch);
    }

    /// Every box placed. What is left is to read off who reads what the
    /// pattern leaves, and to hold the whole thing to the checker.
    fn finish(&mut self) {
        let nodes: Vec<NodeId> = match self.nodes.iter().copied().collect() {
            Some(nodes) => nodes,
            None => return,
        };
        let inputs: Vec<Source> = match self.inputs.iter().copied().collect() {
            Some(inputs) => inputs,
            None => return,
        };
        let branches: Vec<BranchId> = match self.branches.iter().copied().collect() {
            Some(branches) => branches,
            None => return,
        };
        let mut outputs = Vec::with_capacity(self.pattern.outputs().len());
        for &src in self.pattern.outputs() {
            let Source::Port { node, port } = src else {
                return;
            };
            let host = Source::Port {
                node: nodes[node.index()],
                port,
            };
            // Whoever reads that port and is not one of the pattern's own
            // readers is reading it from outside, and that is what the
            // boundary output stands for.
            let mut left: Vec<Sink> = self.graph.sinks(host).to_vec();
            for &sink in self.pattern.sinks(src) {
                let Sink::Port { node, port } = sink else {
                    continue;
                };
                let theirs = Sink::Port {
                    node: nodes[node.index()],
                    port,
                };
                match left.iter().position(|&s| s == theirs) {
                    Some(k) => {
                        left.remove(k);
                    }
                    None => return,
                }
            }
            outputs.push(left);
        }
        let found = Match {
            nodes,
            inputs,
            outputs,
            branches,
        };
        if check_match(self.graph, self.pattern, &found).is_ok() {
            self.found.push(found);
        }
    }
}

/// Every embedding of `pattern` that puts *some* box of it at `host`.
///
/// [`find_pinned`] over each of the pattern's boxes in turn, deduplicated —
/// what a driver anchoring a rewrite at one box wants, since which box of
/// the pattern lands there is the pattern's business and not the driver's.
pub fn find_over(graph: &Graph, pattern: &Graph, host: NodeId) -> Vec<Match> {
    let mut out: Vec<Match> = Vec::new();
    for pat in 0..pattern.nodes.len() {
        for at in find_pinned(graph, pattern, pat, host) {
            if !out.contains(&at) {
                out.push(at);
            }
        }
    }
    out
}

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

    // ---- a pair, put down somewhere ----

    /// The whole of what this module offers a rewriter, with no law in
    /// sight: a graph, a pair of graphs, and a match saying where the first
    /// of the pair sits.
    #[test]
    fn a_pair_replaces_what_it_is_found_at() {
        let (_t, mut host) = built("push 1 push 2 add");
        let pair = Pair::new(
            Graph::of_box(NodeKind::Op(Prim::Add)),
            Graph::of_box(NodeKind::Op(Prim::Subtract)),
        )
        .expect("two one-box windows of one arity");

        let found = pair.find(&host, Direction::Forward);
        assert_eq!(found.len(), 1, "one add to point at:\n{}", host);

        let back = pair
            .apply(&mut host, Direction::Forward, &found[0])
            .expect("the match is the one the search just read");
        host.check().unwrap_or_else(|e| panic!("{}\n{}", e, host));

        let (_t, want) = built("push 1 push 2 sub");
        assert!(isomorphic(&host, &want), "\n{}\n{}", host, want);

        // And the way back is the embedding it handed over, not a bit
        // flipped: the `sub` it put down is a box the host had never seen.
        pair.apply(&mut host, Direction::Backward, &back)
            .expect("the answer names where the replacement landed");
        let (_t, again) = built("push 1 push 2 add");
        assert!(isomorphic(&host, &again));
    }

    /// A pair is held to the one thing a splice needs of it.
    #[test]
    fn two_graphs_of_different_arities_are_no_pair() {
        let why = Pair::new(
            Graph::of_box(NodeKind::Op(Prim::Add)),
            Graph::of_box(NodeKind::Op(Prim::Not)),
        )
        .expect_err("2 -> 1 against 1 -> 1");
        assert_eq!(why, Unpaired::Interface(Arity::new(2, 1), Arity::new(1, 1)));
    }

    /// A match is a claim, and a wrong claim costs a refusal rather than a
    /// torn graph. The check runs to completion before a box is touched, so
    /// what it refuses it also leaves alone.
    #[test]
    fn a_stated_match_that_is_not_one_is_refused() {
        let (_t, host) = built("push 1 push 2 add");
        let pair = Pair::new(
            Graph::of_box(NodeKind::Op(Prim::Add)),
            Graph::of_box(NodeKind::Op(Prim::Subtract)),
        )
        .unwrap();
        let (add, _) = host
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Add)))
            .expect("an add");

        // A box that is not the one the pattern has in its place.
        let (push, _) = host
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(_))))
            .expect("a literal");
        let wrong = Match {
            nodes: vec![push],
            inputs: host.sources(add).to_vec(),
            outputs: vec![Vec::new()],
            branches: Vec::new(),
        };
        let mut spoiled = host.clone();
        assert_eq!(
            pair.apply(&mut spoiled, Direction::Forward, &wrong),
            Err(Mismatch::Kind(push))
        );
        assert_eq!(spoiled, host, "a refusal changes nothing");

        // The right box, with a reader left unaccounted for. This is the
        // condition a plain substitution would not ask about, and the one
        // that would strand a link.
        let stranded = Match {
            nodes: vec![add],
            inputs: host.sources(add).to_vec(),
            outputs: vec![Vec::new()],
            branches: Vec::new(),
        };
        let mut spoiled = host.clone();
        assert!(matches!(
            pair.apply(&mut spoiled, Direction::Forward, &stranded),
            Err(Mismatch::Readers(_))
        ));
        assert_eq!(spoiled, host, "a refusal changes nothing");

        // The right box, named twice.
        let doubled = Match {
            nodes: vec![add, add],
            inputs: host.sources(add).to_vec(),
            outputs: vec![vec![Sink::Output(0)]],
            branches: Vec::new(),
        };
        let mut spoiled = host.clone();
        assert_eq!(
            pair.apply(&mut spoiled, Direction::Forward, &doubled),
            Err(Mismatch::Shape)
        );
        assert_eq!(spoiled, host, "a refusal changes nothing");
    }

    // ---- one embedding read through another ----

    /// Composition, on its own: a match of `P` in `G` and an embedding of
    /// `G` in `H` make a match of `P` in `H` — and the answer is a real
    /// match, which is to say the checker takes it.
    #[test]
    fn a_match_read_through_an_embedding_is_a_match() {
        // `H`: `not ; not ; not`. `G`: the deepest two of them.
        let mut host = Graph::empty(1);
        let a = host.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let b = host.add(NodeKind::Op(Prim::Not), a.clone());
        let c = host.add(NodeKind::Op(Prim::Not), b);
        host.close(c);
        host.check().unwrap();

        let mut inner = Graph::empty(1);
        let first = inner.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let second = inner.add(NodeKind::Op(Prim::Not), first);
        inner.close(second);

        let outer = find(&host, &inner)
            .into_iter()
            .find(|at| at.nodes[0] == NodeId::at(0))
            .expect("the deepest pair");
        let carried = Embedding::of(&outer);

        // `P`: one `not`, matched at the *second* box of `G`. Its port is
        // exported, and in `G` the only thing reading it is `G`'s boundary.
        let one = Graph::of_box(NodeKind::Op(Prim::Not));
        let there = find(&inner, &one)
            .into_iter()
            .find(|at| at.outputs[0] == [Sink::Output(0)])
            .expect("the shallower of the two");

        let here = carried.carry(&there).expect("the embedding covers it");
        assert_eq!(here.nodes, vec![NodeId::at(1)]);
        // The boundary is where the composition earns its keep: `G`'s output
        // stood for the third `not`, so that is who reads this one now.
        assert_eq!(here.inputs, [a[0]], "the deepest `not` feeds it");
        assert_eq!(
            here.outputs,
            vec![vec![Sink::Port {
                node: NodeId::at(2),
                port: 0
            }]],
            "and the shallowest reads it"
        );
        check_match(&host, &one, &here).expect("a composed match is a match");
    }

    /// An embedding says nothing about what it does not cover.
    #[test]
    fn an_embedding_carries_only_what_it_holds() {
        let mut inner = Graph::empty(1);
        let only = inner.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        inner.close(only);
        let carried = Embedding::of(&Match {
            nodes: vec![NodeId::at(7)],
            inputs: vec![Source::Input(3)],
            outputs: vec![vec![Sink::Output(2)]],
            branches: Vec::new(),
        });
        assert_eq!(carried.node(NodeId::at(0)), Some(NodeId::at(7)));
        assert_eq!(carried.node(NodeId::at(1)), None);

        let stranger = Match {
            nodes: vec![NodeId::at(1)],
            inputs: vec![Source::Input(0)],
            outputs: vec![vec![Sink::Output(0)]],
            branches: Vec::new(),
        };
        assert_eq!(carried.carry(&stranger), None, "box 1 is not covered");
    }
}
