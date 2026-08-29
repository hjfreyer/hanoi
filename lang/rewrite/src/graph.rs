//! Values, and rewriting one graph of them by another: what a box is, what
//! it reads, whether two graphs are the same program, and how an equation
//! is spent against one.
//!
//! This is the layer [`crate::diagram2`] is an engine over, kept apart from
//! it because the two are different things. A graph knows what a box takes
//! and leaves, what reads what, whether it holds together, and whether
//! another graph is the same program. It knows nothing about terms, laws,
//! tactics or proofs; the traffic in that direction is all diagram2's,
//! which [`build`](crate::diagram2::build)s one from a term and never turns
//! one back.
//!
//! ## A box is what it computes
//!
//! **Identity is content.** A node is its kind and the sources its input
//! ports read, and [`Graph::add`] hands back the node that already says
//! that if one does. So two boxes computing the same thing on the same
//! operands are not two boxes — there is no way to write that down — and
//! the graph is maximally shared at every moment, by construction rather
//! than by any rewrite.
//!
//! That one decision is why the wiring layer is not here. `id`, `copy` and
//! `drop` were boxes when a graph was a picture of a *stack program*; a
//! value read twice is now two references, a value read never is a node
//! nothing reaches, and a crossing is two names in the other order. So
//! `id-elim`, `swap-elim`, `copy-elim`, `dead-node` and `dedup` are not
//! laws that fire — they are things the representation cannot say, which is
//! the strongest form of "already done".
//!
//! **A node is immutable.** Its content is its name, so nothing edits one;
//! a rewrite makes new nodes and re-roots. Which means links are recorded
//! one way only — [`Graph::sources`] down, and no reader lists to keep in
//! step. [`Graph::sinks`] answers by reading, and answers about the
//! **reachable** graph: a node no boundary output reaches is not part of
//! the program, and reachability is the whole of what deletion means.
//!
//! ## A rewrite replaces a value, not a subgraph
//!
//! **A rewrite is a [`Pair`], spent where a [`Match`] says.** A pair is two
//! graphs offered as interchangeable; a match is the claim that one of them
//! *is* some part of a host graph — which boxes, and what its boundary
//! inputs stand for. [`Pair::apply`] checks the claim and then does the one
//! thing there is to do: it builds the other side, and **substitutes** its
//! outputs for the ones the pattern exported, rebuilding everything that
//! read them.
//!
//! Nothing is deleted, and that is why nothing has to be accounted for. The
//! old splice had to know every reader of every port it was about to
//! strand, so a law could not fire wherever its window was shared —
//! `not-not` declined on a first `not` somebody else read, and the fix was
//! to unshare first. Substitution has no such condition: a reader outside
//! the window keeps reading the node it always read, because that node is
//! still there and still means what it meant. The three conditions
//! [`check_match`] is left with are that the boxes are the right boxes,
//! that they read what the pattern says, and that the answer does not read
//! itself.
//!
//! ## Two graphs are one program by looking
//!
//! Content addressing canonicalises, so [`isomorphic`] is not a search: the
//! two graphs are walked from their boundary outputs and compared. Equality
//! on [`Graph`] is that same reading, which is why a graph that rewrote and
//! a graph that was built compare equal when they say the same thing, and
//! why the boxes a rewrite left behind count for nothing.
//!
//! ## Embeddings compose
//!
//! A match is a map: this graph's boxes and boundary, read as another's.
//! [`Embedding`] is that map kept in a form that outlives a rewrite, and
//! [`Embedding::carry`] composes two of them — a match against an inner
//! graph, said against the outer one. That is what lets a rewrite stated
//! about one graph be spent inside another, and a whole *run* of them
//! likewise.

use std::collections::{HashMap, HashSet};
use std::fmt;

use bytecode::SentenceIndex;

use crate::term::{Arity, Prim};

// ---- the graph ----------------------------------------------------------------

/// A box in a graph: an index into its [`Graph`]'s node list.
///
/// Meaningful only against the graph that issued it. An id is never reused
/// and a node is never edited, so an id names the same computation for the
/// life of the graph — what changes is whether the boundary still reaches
/// it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(u32);

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id at a position, for anything that indexes a graph's boxes by
    /// their own order — [`rules`](crate::diagram2::rules) does, since a
    /// rule's side is built once and never rewritten.
    pub fn at(index: usize) -> NodeId {
        NodeId(u32::try_from(index).expect("a graph fits in u32"))
    }
}

/// Where an input port reads from — one producer, always.
///
/// [`Source::Input`] is the graph's own boundary, which is the price of
/// having no wire type: a link to the outside is a variant rather than just
/// another port.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Source {
    /// Boundary input `i`, counted from the deepest.
    Input(usize),
    /// Output port `port` of `node`.
    Port { node: NodeId, port: usize },
}

/// Where an output port is read — none, one, or many.
///
/// The asymmetry against [`Source`] is the cartesian fact itself: a value
/// is produced once and read freely. It is a *reading* rather than a
/// record — [`Graph::sinks`] computes it — because a node holds only what
/// it reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sink {
    /// Boundary output `i`, counted from the deepest.
    Output(usize),
    /// Input port `port` of `node`.
    Port { node: NodeId, port: usize },
}

/// What a box is: an operation, a call, or a branch.
///
/// Three, where there were six. `Id`, `Copy` and `Drop` were the stack
/// program showing through — a graph of values reads a wire twice by naming
/// it twice, and drops one by naming it nowhere — and `Op(Prim::Swap)` went
/// with them, since a crossing is two sources in the other order.
/// [`build`](crate::diagram2::build) is where that translation happens, and
/// it is the only place that ever knew about the stack.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /// One prim, `push` included.
    Op(Prim),
    /// A sentence called by name, left unopened; the arity is carried for
    /// the same reason [`Term::Call`](crate::term::Term::Call) carries it.
    Call { target: SentenceIndex, arity: Arity },
    /// `select(n)`: the two blocks of an answer, and the condition that
    /// keeps one of them. A branch is this box and nothing else.
    ///
    /// **Input 0 is the condition**, inputs `1..=n` the `then` block and
    /// `n+1..=2n` the `else` block. Output `i` is input `1 + i` when the
    /// condition holds and input `1 + n + i` otherwise.
    ///
    /// The arms are not in here. They are ordinary boxes upstream of the
    /// blocks, and what makes a box an arm's own is that nothing but that
    /// side's blocks reads it — a fact about the whole graph, not something
    /// any box records. Both arms are computed, which is the single-arm
    /// hoist of [docs/totality.md](../../../docs/totality.md) — sound
    /// because every [`Prim`] is total and has no effect but the stack.
    Select { arity: usize },
}

impl NodeKind {
    /// What this box takes and leaves — the same table
    /// [`Context::arity`](crate::term::Context::arity) keeps for terms.
    pub fn arity(&self) -> Arity {
        match self {
            NodeKind::Op(prim) => prim.arity(),
            NodeKind::Call { arity, .. } => *arity,
            NodeKind::Select { arity } => Arity::new(2 * arity + 1, *arity),
        }
    }
}

/// A box, which is to say a value: what it computes and what it computes it
/// from. Hashed and compared by exactly that, which is what makes it the
/// key a graph interns on.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Node {
    kind: NodeKind,
    /// One source per input port.
    inputs: Vec<Source>,
}

/// A program as values and what each is made of.
///
/// Nodes accumulate and are never removed; the program is what the boundary
/// outputs reach. `intern` is what makes a node's content its name.
#[derive(Debug, Clone, Default)]
pub struct Graph {
    nodes: Vec<Node>,
    /// The one id each distinct box has.
    intern: HashMap<Node, NodeId>,
    /// How many boundary inputs.
    inputs: usize,
    /// What each boundary output reads, deepest first.
    outputs: Vec<Source>,
}

/// Two graphs are equal when they are the same program: what the boundary
/// reaches, read from the outputs down. Boxes nothing reaches — what a
/// rewrite left behind — count for nothing, and neither do the numbers the
/// ids happen to hold.
impl PartialEq for Graph {
    fn eq(&self, other: &Self) -> bool {
        self.arity() == other.arity() && self.canon() == other.canon()
    }
}

impl Graph {
    pub(crate) fn empty(inputs: usize) -> Graph {
        Graph {
            nodes: Vec::new(),
            intern: HashMap::new(),
            inputs,
            outputs: Vec::new(),
        }
    }

    /// The window one box fills: its input ports reading the boundary,
    /// every output port exported in order.
    ///
    /// The pattern side of every one-box rewrite, and the shape a caller
    /// replacing a single box states its [`Match`] against.
    pub(crate) fn of_box(kind: NodeKind) -> Graph {
        let arity = kind.arity();
        let mut graph = Graph::empty(arity.inputs);
        let ports = graph.add(kind, (0..arity.inputs).map(Source::Input).collect());
        graph.close(ports);
        graph
    }

    /// What the whole graph takes and leaves.
    pub fn arity(&self) -> Arity {
        Arity::new(self.inputs, self.outputs.len())
    }

    /// Whether the boundary reaches that node — which is the whole of what
    /// being part of the program means here.
    pub fn is_live(&self, id: NodeId) -> bool {
        self.reachable().contains(&id)
    }

    /// Every box the boundary reaches, in id order — which is producers
    /// first, since a node is only ever made after what it reads.
    pub fn live(&self) -> impl Iterator<Item = (NodeId, &NodeKind)> {
        let reachable = self.reachable();
        (0..self.nodes.len())
            .map(NodeId::at)
            .filter(move |id| reachable.contains(id))
            .map(|id| (id, &self.nodes[id.index()].kind))
    }

    /// How many boxes the program is.
    pub fn live_count(&self) -> usize {
        self.reachable().len()
    }

    pub fn kind(&self, id: NodeId) -> &NodeKind {
        &self.nodes[id.index()].kind
    }

    /// What a node's input ports read, deepest first.
    pub fn sources(&self, id: NodeId) -> &[Source] {
        &self.nodes[id.index()].inputs
    }

    /// What the boundary outputs read, deepest first.
    pub fn outputs(&self) -> &[Source] {
        &self.outputs
    }

    /// Who reads that port, among the boxes the program reaches and the
    /// boundary.
    ///
    /// Computed rather than kept: a node records what it reads and nothing
    /// records what reads it, so this is a sweep. It is the one place the
    /// distinction between a box and a box the boundary reaches is
    /// load-bearing — a rewrite leaves its old boxes standing, and they
    /// read what they always read, so counting them would be counting
    /// ghosts.
    pub fn sinks(&self, src: Source) -> Vec<Sink> {
        let mut out: Vec<Sink> = self
            .outputs
            .iter()
            .enumerate()
            .filter(|&(_, &s)| s == src)
            .map(|(i, _)| Sink::Output(i))
            .collect();
        for (id, _) in self.live() {
            for (port, &s) in self.sources(id).iter().enumerate() {
                if s == src {
                    out.push(Sink::Port { node: id, port });
                }
            }
        }
        out
    }

    /// A box, its input ports reading the sources given — or the box that
    /// already says that.
    ///
    /// The interning is the model: a value is named by what it is, so
    /// asking for one twice asks for the same one. The whole wiring
    /// theory is settled here, before there is anything to rewrite.
    pub(crate) fn add(&mut self, kind: NodeKind, inputs: Vec<Source>) -> Vec<Source> {
        let arity = kind.arity();
        debug_assert_eq!(inputs.len(), arity.inputs, "the caller cuts by arity");
        let id = self.add_node(kind, inputs);
        (0..arity.outputs)
            .map(|port| Source::Port { node: id, port })
            .collect()
    }

    /// [`Graph::add`], answering with the node rather than its ports.
    pub(crate) fn add_node(&mut self, kind: NodeKind, inputs: Vec<Source>) -> NodeId {
        debug_assert!(
            inputs.iter().all(|&src| self.valid(src)),
            "a box reads what is already there"
        );
        let node = Node { kind, inputs };
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = NodeId::at(self.nodes.len());
        self.intern.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// Closes the graph: these sources are what the boundary leaves.
    pub(crate) fn close(&mut self, sources: Vec<Source>) {
        self.outputs = sources;
    }

    /// Every box the boundary reaches.
    fn reachable(&self) -> HashSet<NodeId> {
        let mut seen = HashSet::new();
        let mut todo: Vec<Source> = self.outputs.clone();
        while let Some(src) = todo.pop() {
            if let Source::Port { node, .. } = src
                && seen.insert(node)
            {
                todo.extend(self.nodes[node.index()].inputs.iter().copied());
            }
        }
        seen
    }

    /// The program, renumbered by a walk that reads only structure: the
    /// boundary outputs in order, each one's producers before itself.
    ///
    /// Two graphs saying the same thing land on the same answer whatever
    /// order they were built in, which is what makes both equality and
    /// [`isomorphic`] a reading rather than a search.
    fn canon(&self) -> (Vec<(NodeKind, Vec<Source>)>, Vec<Source>) {
        let mut place: HashMap<NodeId, usize> = HashMap::new();
        let mut order: Vec<NodeId> = Vec::new();
        for &out in &self.outputs {
            self.walk_canon(out, &mut place, &mut order);
        }
        let named = |src: Source| match src {
            Source::Input(i) => Source::Input(i),
            Source::Port { node, port } => Source::Port {
                node: NodeId::at(place[&node]),
                port,
            },
        };
        let nodes = order
            .iter()
            .map(|&id| {
                let node = &self.nodes[id.index()];
                (
                    node.kind.clone(),
                    node.inputs.iter().map(|&s| named(s)).collect(),
                )
            })
            .collect();
        (nodes, self.outputs.iter().map(|&s| named(s)).collect())
    }

    fn walk_canon(&self, src: Source, place: &mut HashMap<NodeId, usize>, order: &mut Vec<NodeId>) {
        let Source::Port { node, .. } = src else {
            return;
        };
        if place.contains_key(&node) {
            return;
        }
        // Marked before the descent would be wrong for a cycle and
        // impossible without one: a node only ever reads what was already
        // there.
        for &input in &self.nodes[node.index()].inputs {
            self.walk_canon(input, place, order);
        }
        place.insert(node, order.len());
        order.push(node);
    }

    fn valid(&self, src: Source) -> bool {
        match src {
            Source::Input(i) => i < self.inputs,
            Source::Port { node, port } => {
                node.index() < self.nodes.len() && port < self.kind(node).arity().outputs
            }
        }
    }

    /// Whether every source names a port that is there.
    ///
    /// Short, because the representation admits so little: there are no
    /// reader lists to fall out of step, a node's ports are its kind's by
    /// construction, and nothing can reach itself, since a node is built
    /// after what it reads.
    pub fn check(&self) -> Result<(), Error> {
        for (i, node) in self.nodes.iter().enumerate() {
            if node.inputs.len() != node.kind.arity().inputs {
                return Err(Error::Width {
                    node: NodeId::at(i),
                    expected: node.kind.arity(),
                    inputs: node.inputs.len(),
                });
            }
            for (port, &src) in node.inputs.iter().enumerate() {
                let ahead = matches!(src, Source::Port { node, .. } if node.index() >= i);
                if !self.valid(src) || ahead {
                    return Err(Error::Dangling {
                        source: src,
                        sink: Sink::Port {
                            node: NodeId::at(i),
                            port,
                        },
                    });
                }
            }
        }
        for (i, &src) in self.outputs.iter().enumerate() {
            if !self.valid(src) {
                return Err(Error::Dangling {
                    source: src,
                    sink: Sink::Output(i),
                });
            }
        }
        Ok(())
    }

    /// Another graph's boxes added to this one, its boundary inputs
    /// standing for the sources given, answering with the sources its
    /// boundary outputs name.
    ///
    /// This is what lets a piece of a program be **carried** rather than
    /// spelled out. A rule about a region cannot name what is in it — that
    /// is whatever the program put there — so it carries it and implants it
    /// where it goes. Interning means an implant of something already here
    /// adds nothing at all.
    pub(crate) fn implant(&mut self, arm: &Graph, inputs: &[Source]) -> Vec<Source> {
        debug_assert_eq!(inputs.len(), arm.inputs, "one source per input");
        let mut fresh: Vec<NodeId> = Vec::with_capacity(arm.nodes.len());
        let carry = |src: Source, fresh: &[NodeId]| match src {
            Source::Input(i) => inputs[i],
            Source::Port { node, port } => Source::Port {
                node: fresh[node.index()],
                port,
            },
        };
        for node in &arm.nodes {
            let takes = node.inputs.iter().map(|&s| carry(s, &fresh)).collect();
            fresh.push(self.add_node(node.kind.clone(), takes));
        }
        arm.outputs.iter().map(|&s| carry(s, &fresh)).collect()
    }

    /// Every reader of every key rebuilt to read the value instead, and the
    /// boundary with them.
    ///
    /// The whole of what a rewrite does. Boxes are immutable, so "rebuilt"
    /// means made afresh from mapped sources — and interning means a
    /// rebuild that lands on something already here lands on the box
    /// itself. Walking in id order is walking producers first, so every
    /// source is already mapped when the box that reads it comes up; the
    /// boxes made along the way get higher ids than anything in the sweep,
    /// so the sweep never has to consider them.
    fn substitute(&mut self, sigma: &HashMap<Source, Source>) {
        let mut map = sigma.clone();
        let mut here: Vec<NodeId> = self.reachable().into_iter().collect();
        here.sort_unstable();
        for id in here {
            let node = &self.nodes[id.index()];
            let takes: Vec<Source> = node
                .inputs
                .iter()
                .map(|src| map.get(src).copied().unwrap_or(*src))
                .collect();
            if takes == node.inputs {
                continue;
            }
            let kind = node.kind.clone();
            let outs = kind.arity().outputs;
            let made = self.add_node(kind, takes);
            for port in 0..outs {
                // A port `sigma` already speaks for keeps what it said:
                // the replacement is the answer for that one, and this
                // rebuild is only for the ports it left alone.
                map.entry(Source::Port { node: id, port })
                    .or_insert(Source::Port { node: made, port });
            }
        }
        self.outputs = self
            .outputs
            .iter()
            .map(|src| map.get(src).copied().unwrap_or(*src))
            .collect();
    }

    /// Everything a source reads, transitively.
    fn upstream(&self, src: Source) -> HashSet<Source> {
        let mut seen = HashSet::new();
        let mut todo = vec![src];
        while let Some(src) = todo.pop() {
            if !seen.insert(src) {
                continue;
            }
            if let Source::Port { node, .. } = src {
                for &input in &self.nodes[node.index()].inputs {
                    todo.push(input);
                }
                // Every port of a box is upstream of anything the box is,
                // since replacing one is replacing what the box computes.
                for port in 0..self.kind(node).arity().outputs {
                    todo.push(Source::Port { node, port });
                }
            }
        }
        seen
    }
}

// ---- padding ---------------------------------------------------------------------

/// The graph as `id(k) * itself` reads: `k` fresh boundary wires passed
/// straight through beneath it.
///
/// This is the graph-side spelling of
/// [`Context::under`](crate::term::Context::under), and it exists for the
/// same reason: a goal pads its narrower side until the arities agree, and
/// once a side is a graph the padding has to be said on the graph. Every
/// box is rebuilt, since a box that reads `Input(i)` is a different box
/// once that input is `Input(i + k)`.
pub fn under(graph: &Graph, k: usize) -> Graph {
    if k == 0 {
        return graph.clone();
    }
    let mut out = Graph::empty(graph.inputs + k);
    let shifted: Vec<Source> = (0..graph.inputs).map(|i| Source::Input(i + k)).collect();
    let mut outputs: Vec<Source> = (0..k).map(Source::Input).collect();
    outputs.extend(out.implant(graph, &shifted));
    out.close(outputs);
    debug_assert!(out.check().is_ok(), "padding rebuilt every box");
    out
}

// ---- whether two graphs are one program ------------------------------------------

/// Whether the two graphs are the same program.
///
/// Not a search. Content addressing has already canonicalised each side, so
/// the answer is a walk from the boundary outputs comparing what it finds —
/// which is what [`Graph::canon`] does, and what `==` is.
pub fn isomorphic(a: &Graph, b: &Graph) -> bool {
    a == b
}

// ---- a graph that does not hold together -----------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A node's port count disagrees with its kind.
    Width {
        node: NodeId,
        expected: Arity,
        inputs: usize,
    },
    /// A source naming a port that is not there — or one that is not there
    /// *yet*, which is the same mistake: a box reads what was built before
    /// it, and that is why nothing can reach itself.
    Dangling { source: Source, sink: Sink },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Width {
                node,
                expected,
                inputs,
            } => write!(
                f,
                "node {} takes {} where its kind takes {}",
                node, inputs, expected
            ),
            Error::Dangling { source, sink } => {
                write!(
                    f,
                    "{} reads {}, which is not a port it may read",
                    sink, source
                )
            }
        }
    }
}

impl std::error::Error for Error {}

// ---- pairs, matches, and spending one against the other --------------------------

/// Which way round an equation is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Direction {
    /// Left to right: the left side is the pattern.
    Forward,
    /// Right to left.
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

/// Why two graphs are not an equation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unpaired {
    /// The two sides do not take and leave the same.
    Interface(Arity, Arity),
    /// A side that is not a graph.
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
/// Where the pair *came from* — which law it spells, whether anything
/// proved the two sides equal — is [`crate::diagram2::rules`]'s business
/// and none of this module's.
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

    /// Whether `at` really points at a part of the graph this direction may
    /// replace.
    pub fn check(&self, graph: &Graph, dir: Direction, at: &Match) -> Result<(), Mismatch> {
        check_match(graph, self.pattern(dir), at)
    }

    /// One rewrite: what the pattern's boundary outputs stand for, replaced
    /// by what the other side's do.
    ///
    /// Three moves, and no deletion among them. The replacement is
    /// **built** on what the match says the pattern's inputs stand for —
    /// interning, so a replacement the graph already contains costs
    /// nothing. Its outputs are then paired with the ones the pattern
    /// exports, which is the equation said in the host's own values. And
    /// everything that read the one is rebuilt to read the other.
    ///
    /// Nothing here has to account for a reader the pattern never
    /// mentioned: that reader goes on reading the box it always read,
    /// which is still there and still means what it meant. So a law fires
    /// in a window other things read into, which is what it always meant.
    /// The one thing to refuse is a replacement that is *already* part of
    /// what it replaces — an equation spent on its own answer, which says
    /// nothing and would only grow the graph.
    ///
    /// The answer is the **embedding of what went in**, which is where the
    /// way back lands: a [`Match`] names host [`NodeId`]s, so the inverse
    /// has to be handed over rather than derived by flipping a bit.
    ///
    /// A refusal changes nothing: everything is checked before the first
    /// box is made.
    pub fn apply(&self, graph: &mut Graph, dir: Direction, at: &Match) -> Result<Match, Mismatch> {
        let (pattern, replacement) = self.sides(dir);
        check_match(graph, pattern, at)?;

        let image = |src: Source| match src {
            Source::Input(i) => at.inputs[i],
            Source::Port { node, port } => Source::Port {
                node: at.nodes[node.index()],
                port,
            },
        };
        let before = graph.reachable();

        // The other side, built where the match says it goes.
        let mut fresh: Vec<NodeId> = Vec::with_capacity(replacement.nodes.len());
        let carry = |src: Source, fresh: &[NodeId]| match src {
            Source::Input(i) => at.inputs[i],
            Source::Port { node, port } => Source::Port {
                node: fresh[node.index()],
                port,
            },
        };
        for node in &replacement.nodes {
            let takes = node.inputs.iter().map(|&s| carry(s, &fresh)).collect();
            fresh.push(graph.add_node(node.kind.clone(), takes));
        }
        let leaves: Vec<Source> = replacement
            .outputs
            .iter()
            .map(|&s| carry(s, &fresh))
            .collect();

        // The equation, in the host's values: this source is that one.
        let mut sigma: HashMap<Source, Source> = HashMap::new();
        for (j, &src) in pattern.outputs.iter().enumerate() {
            let key = image(src);
            if key == leaves[j] {
                continue;
            }
            match sigma.insert(key, leaves[j]) {
                Some(other) if other != leaves[j] => return Err(Mismatch::Conflict(key)),
                _ => {}
            }
        }
        // A replacement the graph already held, and that reads what it is
        // standing in for, would be rebuilt into a reading of itself.
        for (&key, &val) in &sigma {
            let standing = matches!(val, Source::Port { node, .. } if before.contains(&node));
            if standing && graph.upstream(val).iter().any(|s| sigma.contains_key(s)) {
                return Err(Mismatch::Circular(key));
            }
        }
        graph.substitute(&sigma);

        Ok(Match {
            nodes: fresh,
            inputs: at.inputs.clone(),
        })
    }
}

/// A part of a host graph, pointed at: the claim that some pattern graph
/// *is* these boxes, reading these sources.
///
/// Not a path. A term's subterm has a name in the term; a graph's does not,
/// so the embedding itself is the name — which box is which, and what the
/// pattern's boundary inputs stand for outside.
///
/// It is a **claim**, not a proof: nothing about a `Match` is true until
/// [`check_match`] has said so, which is why every field is public and
/// anyone may state one. [`Pair::apply`] checks before it builds, so a
/// wrong claim costs a [`Mismatch`] rather than a wrong graph.
///
/// Two fields, and no choice among them: both are readings of the host.
/// A substitution re-points *every* reader of the value it replaces and
/// leaves every reader of anything else alone, so a match never has to
/// say which of a port's outside readers belong to the window.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    /// Image of the pattern's boxes, indexed by the pattern's own node
    /// index, which is dense.
    pub nodes: Vec<NodeId>,
    /// What the pattern's boundary input `i` stands for in the host.
    pub inputs: Vec<Source>,
}

impl Match {
    /// This match said again in terms of the boxes that stand where its
    /// own stood.
    pub fn rebase(&self, moved: &HashMap<NodeId, NodeId>) -> Match {
        let now = |id: NodeId| moved.get(&id).copied().unwrap_or(id);
        Match {
            nodes: self.nodes.iter().map(|&id| now(id)).collect(),
            inputs: self
                .inputs
                .iter()
                .map(|&src| match src {
                    Source::Port { node, port } => Source::Port {
                        node: now(node),
                        port,
                    },
                    boundary => boundary,
                })
                .collect(),
        }
    }
}

/// One graph's names read in another, kept as a map so it can survive both
/// of them being rewritten.
///
/// Composition is [`Embedding::carry`]: given a match of `P` in `G` and an
/// embedding of `G` in `H`, it answers the match of `P` in `H`, which is
/// what lets a rewrite stated about `G` be spent inside `H` instead. That
/// the answer is still a *claim* is the usual discipline — it goes through
/// [`Pair::apply`] like any other.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Embedding {
    /// What the outer graph has where the inner one has this box.
    nodes: HashMap<NodeId, NodeId>,
    /// What the inner graph's boundary input `i` reads in the outer one.
    inputs: Vec<Source>,
}

impl Embedding {
    /// The correspondence a match states, in a form that outlives it.
    pub fn of(at: &Match) -> Embedding {
        Embedding {
            nodes: at
                .nodes
                .iter()
                .enumerate()
                .map(|(i, &to)| (NodeId::at(i), to))
                .collect(),
            inputs: at.inputs.clone(),
        }
    }

    /// A match against the inner graph, said against the outer one.
    ///
    /// `None` where the match names a box or a boundary this embedding does
    /// not carry — which, for an embedding kept up to date by
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
        })
    }

    /// What one rewrite, run on both sides, added to the correspondence.
    ///
    /// Both arguments are the answer [`Pair::apply`] gave — the embedding
    /// of what it put down — `inner` from the run on the inner graph and
    /// `outer` from the run on the outer one. The same replacement went
    /// down in both, so its boxes line up in order.
    pub fn extend(&mut self, inner: &Match, outer: &Match) {
        debug_assert_eq!(
            inner.nodes.len(),
            outer.nodes.len(),
            "one replacement went down on both sides"
        );
        for (&here, &there) in inner.nodes.iter().zip(&outer.nodes) {
            self.nodes.insert(here, there);
        }
    }

    /// What the outer graph has where the inner one has this box.
    pub fn node(&self, id: NodeId) -> Option<NodeId> {
        self.nodes.get(&id).copied()
    }
}

/// How a claimed embedding failed to be one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Mismatch {
    /// The match names a different number of boxes or inputs than the
    /// pattern has.
    Shape,
    /// A box the match names is not part of the program.
    Gone(NodeId),
    /// The box there is not the one the pattern has in its place.
    Kind(NodeId),
    /// That input port reads something other than what the pattern says.
    Edge(Sink),
    /// The pattern exports one value twice and the match sends it two
    /// ways, which is two answers to one question.
    Conflict(Source),
    /// The replacement is already part of what it replaces, so putting it
    /// in would be reading it out of itself.
    Circular(Source),
}

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
            Mismatch::Conflict(src) => {
                write!(f, "{} is answered two ways by one match", src)
            }
            Mismatch::Circular(src) => write!(
                f,
                "what would stand for {} already reads it, so the step says nothing",
                src
            ),
        }
    }
}

impl std::error::Error for Mismatch {}

/// Whether the match points at boxes that really are the pattern.
///
/// Three conditions, and between them "these boxes are that pattern":
///
/// 1. **Shape** — one image per box, one source per boundary input.
/// 2. **Kinds** — the same box.
/// 3. **Edges** — every input port of a matched box reads what the pattern
///    says it reads.
///
/// Nothing about who reads what the pattern *leaves*. Accounting for that
/// is the price of destroying things, and a substitution destroys
/// nothing — which is why a law fires in a window other things read into,
/// which is what a law always meant.
pub fn check_match(graph: &Graph, pattern: &Graph, at: &Match) -> Result<(), Mismatch> {
    let boxes = pattern.nodes.len();
    if at.nodes.len() != boxes || at.inputs.len() != pattern.inputs {
        return Err(Mismatch::Shape);
    }
    for &id in &at.nodes {
        if !graph.is_live(id) {
            return Err(Mismatch::Gone(id));
        }
    }
    for &src in &at.inputs {
        if !graph.valid(src) {
            return Err(Mismatch::Shape);
        }
    }
    let image = |src: Source| match src {
        Source::Input(i) => at.inputs[i],
        Source::Port { node, port } => Source::Port {
            node: at.nodes[node.index()],
            port,
        },
    };
    for i in 0..boxes {
        let host = at.nodes[i];
        if pattern.nodes[i].kind != *graph.kind(host) {
            return Err(Mismatch::Kind(host));
        }
        for (port, &src) in pattern.nodes[i].inputs.iter().enumerate() {
            if graph.sources(host).get(port) != Some(&image(src)) {
                return Err(Mismatch::Edge(Sink::Port { node: host, port }));
            }
        }
    }
    Ok(())
}

// ---- finding one -----------------------------------------------------------------

/// Every embedding of `pattern` in `graph`, in a deterministic order.
///
/// Search, and untrusted like all search: what it answers goes through
/// [`check_match`] before anything is done with it.
pub fn find(graph: &Graph, pattern: &Graph) -> Vec<Match> {
    let mut out: Vec<Match> = Vec::new();
    for (seed, _) in graph.live() {
        for at in find_at(graph, pattern, seed) {
            if !out.contains(&at) {
                out.push(at);
            }
        }
    }
    out
}

/// [`find`], with the pattern's first box pinned to one node.
pub fn find_at(graph: &Graph, pattern: &Graph, seed: NodeId) -> Vec<Match> {
    find_pinned(graph, pattern, 0, seed)
}

/// [`find_at`], with pattern box `pat` — not necessarily the first —
/// pinned to `host`.
///
/// This is what lets a driver anchor a pattern at the box its *query* bound
/// rather than the box the pattern happens to begin with.
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
        inputs: vec![None; pattern.inputs],
        seed: host,
        found: Vec::new(),
    };
    search.walk(0);
    search.found
}

/// Every embedding of `pattern` that puts *some* box of it at `host`.
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

/// Whether a pattern says enough about itself to be looked for.
///
/// Two conditions: at least one box to anchor on, and no boundary input
/// that nothing in the pattern reads — a window standing for a wire it
/// never touches cannot say which wire that is.
///
/// A pattern that exports one port twice is searchable like any other,
/// which is what makes a right-hand side searchable and a backward step a
/// step like any other: nothing in the host has to say which of that
/// port's readers belong to which export, because a substitution asks no
/// such question.
pub fn pins_itself(pattern: &Graph) -> bool {
    if pattern.nodes.is_empty() {
        return false;
    }
    (0..pattern.inputs).all(|i| {
        pattern
            .nodes
            .iter()
            .any(|node| node.inputs.contains(&Source::Input(i)))
    })
}

struct Search<'g> {
    graph: &'g Graph,
    pattern: &'g Graph,
    /// The order the walk visits pattern boxes in — the pinned box first,
    /// the rest in index order. [`Match::nodes`] stays in pattern order.
    order: Vec<usize>,
    nodes: Vec<Option<NodeId>>,
    inputs: Vec<Option<Source>>,
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
            if let Some(undo) = self.assign(i, host) {
                self.walk(pos + 1);
                self.undo(i, undo);
            }
        }
    }

    /// The host boxes worth trying for the box visited at `pos`.
    ///
    /// Content addressing makes this nearly a lookup: once every source a
    /// pattern box reads is known, the host box that reads them is the one
    /// the intern table holds, or there is none. Only a box some of whose
    /// sources are still open falls back on the neighbours — the readers of
    /// a source already placed — and only one touching nothing placed at
    /// all costs a sweep.
    fn candidates(&self, pos: usize) -> Vec<NodeId> {
        if pos == 0 {
            return vec![self.seed];
        }
        let here = NodeId::at(self.order[pos]);
        let known = |src: Source| match src {
            Source::Input(l) => self.inputs[l],
            Source::Port { node, port } => {
                self.nodes[node.index()].map(|n| Source::Port { node: n, port })
            }
        };
        let sources = &self.pattern.nodes[here.index()].inputs;
        let settled: Option<Vec<Source>> = sources.iter().map(|&src| known(src)).collect();
        if let Some(inputs) = settled {
            let node = Node {
                kind: self.pattern.nodes[here.index()].kind.clone(),
                inputs,
            };
            return self
                .graph
                .intern
                .get(&node)
                .copied()
                .filter(|&id| self.graph.is_live(id))
                .into_iter()
                .collect();
        }
        for (port, &src) in sources.iter().enumerate() {
            if let Some(src) = known(src) {
                return self
                    .graph
                    .sinks(src)
                    .into_iter()
                    .filter_map(|sink| match sink {
                        Sink::Port { node, port: p } if p == port => Some(node),
                        _ => None,
                    })
                    .collect();
            }
        }
        self.graph.live().map(|(id, _)| id).collect()
    }

    /// Pins the pattern's box `i` to a host box, answering with the
    /// boundary inputs the assignment bound — the undo log.
    fn assign(&mut self, i: usize, host: NodeId) -> Option<Vec<usize>> {
        let here = &self.pattern.nodes[i];
        if here.kind != *self.graph.kind(host) {
            return None;
        }
        let mut fixed = Vec::new();
        for (port, &src) in here.inputs.iter().enumerate() {
            let Some(&hsrc) = self.graph.sources(host).get(port) else {
                self.rollback(&fixed);
                return None;
            };
            match src {
                Source::Input(l) => match self.inputs[l] {
                    Some(held) if held != hsrc => {
                        self.rollback(&fixed);
                        return None;
                    }
                    Some(_) => {}
                    None => {
                        self.inputs[l] = Some(hsrc);
                        fixed.push(l);
                    }
                },
                // A producer not yet placed is not a mismatch: the walk
                // visits the pinned box first, so a consumer can come
                // before what feeds it, and `check_match` holds every edge
                // at the end either way.
                Source::Port { node, port } => match self.nodes[node.index()] {
                    None => {}
                    Some(n) if hsrc == (Source::Port { node: n, port }) => {}
                    Some(_) => {
                        self.rollback(&fixed);
                        return None;
                    }
                },
            }
        }
        self.nodes[i] = Some(host);
        Some(fixed)
    }

    fn rollback(&mut self, fixed: &[usize]) {
        for &l in fixed {
            self.inputs[l] = None;
        }
    }

    fn undo(&mut self, i: usize, fixed: Vec<usize>) {
        self.nodes[i] = None;
        self.rollback(&fixed);
    }

    /// Every box placed; hold the whole claim to the checker.
    fn finish(&mut self) {
        let Some(nodes): Option<Vec<NodeId>> = self.nodes.iter().copied().collect() else {
            return;
        };
        let Some(inputs): Option<Vec<Source>> = self.inputs.iter().copied().collect() else {
            return;
        };
        let found = Match { nodes, inputs };
        if check_match(self.graph, self.pattern, &found).is_ok() && !self.found.contains(&found) {
            self.found.push(found);
        }
    }
}

// ---- an order to run them in -----------------------------------------------------

/// The live nodes in an order that runs producers first.
///
/// Only an evaluator wants this: a graph says what depends on what and
/// nothing about when. Ids are handed out producers-first and never
/// reordered, so the order is the ids' own.
#[cfg(test)]
pub(crate) fn schedule(graph: &Graph) -> Vec<NodeId> {
    graph.live().map(|(id, _)| id).collect()
}

// ---- printing --------------------------------------------------------------------

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl fmt::Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Source::Input(i) => write!(f, "in{}", i),
            Source::Port { node, port } => write!(f, "{}.{}", node, port),
        }
    }
}

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
            NodeKind::Op(prim) => write!(f, "{}", prim),
            NodeKind::Call { target, .. } => write!(f, "call #{}", usize::from(*target)),
            NodeKind::Select { arity } => write!(f, "select({})", arity),
        }
    }
}

/// A graph as a box per line: what each one reads, and how many read it.
impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "inputs {}", self.inputs)?;
        for (id, kind) in self.live() {
            write!(f, "  {} {} <-", id, kind)?;
            if self.nodes[id.index()].inputs.is_empty() {
                write!(f, " ()")?;
            }
            for src in &self.nodes[id.index()].inputs {
                write!(f, " {}", src)?;
            }
            let readers = (0..kind.arity().outputs)
                .map(|port| self.sinks(Source::Port { node: id, port }).len())
                .sum::<usize>();
            writeln!(f, "   [{} reader(s)]", readers)?;
        }
        write!(f, "outputs")?;
        for src in &self.outputs {
            write!(f, " {}", src)?;
        }
        writeln!(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn two_graphs_are_one_program_or_they_are_not() {
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
        assert!(isomorphic(&e, &f), "one term built twice is one program");
        let (_t, g) = built("branch { add } { subtract }");
        assert!(!isomorphic(&e, &g));
    }

    /// A box is its kind and what it reads, so asking for one twice asks
    /// for the same one — before anything has had a chance to rewrite.
    #[test]
    fn a_value_said_twice_is_said_once() {
        let mut g = Graph::empty(1);
        let a = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let b = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        assert_eq!(a, b, "one `not` of one wire is one box");
        g.close(vec![a[0], b[0]]);
        assert_eq!(g.live_count(), 1);
        assert_eq!(g.sinks(a[0]), [Sink::Output(0), Sink::Output(1)]);

        // A different operand is a different box.
        let mut h = Graph::empty(2);
        let x = h.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let y = h.add(NodeKind::Op(Prim::Not), vec![Source::Input(1)]);
        assert_ne!(x, y);
        h.close(vec![x[0], y[0]]);
        assert_eq!(h.live_count(), 2);
    }

    /// What a rewrite leaves behind is not part of the program: the
    /// boundary stops naming it, and that is the whole of being deleted.
    #[test]
    fn sameness_ignores_the_graveyard() {
        let (_t, mut host) = built("not not");
        assert_eq!(host.live_count(), 2);
        let pair = Pair::new(
            {
                let mut g = Graph::empty(1);
                let first = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
                let second = g.add(NodeKind::Op(Prim::Not), first);
                g.close(second);
                g
            },
            Graph::of_box(NodeKind::Op(Prim::AsBool)),
        )
        .unwrap();
        let found = pair.find(&host, Direction::Forward);
        pair.apply(&mut host, Direction::Forward, &found[0])
            .unwrap();
        host.check().unwrap();

        let (_t, want) = built("as_bool");
        assert!(
            isomorphic(&host, &want),
            "the two `not`s are still in the arena and count for nothing:\n{}",
            host
        );
        assert_eq!(host.live_count(), 1);
    }

    // ---- a pair, put down somewhere ----

    /// The whole of what this module offers a rewriter, with no law in
    /// sight: a graph, a pair of graphs, and a match saying where the
    /// first of the pair sits.
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

        let (_t, want) = built("push 1 push 2 subtract");
        assert!(isomorphic(&host, &want), "\n{}\n{}", host, want);

        // And the way back is the embedding it handed over, not a bit
        // flipped: the `subtract` it put down is a box the host had never
        // seen.
        pair.apply(&mut host, Direction::Backward, &back)
            .expect("the answer names where the replacement landed");
        let (_t, again) = built("push 1 push 2 add");
        assert!(isomorphic(&host, &again));
    }

    /// A rewrite replaces a **value**, so every reader of it is rebuilt —
    /// including ones the window never mentioned.
    ///
    /// Nothing is deleted, so nothing is stranded: a match whose boxes
    /// have readers it never accounts for is a match like any other.
    #[test]
    fn a_reader_the_window_never_named_is_no_obstacle() {
        // `not(x)` read by a second `not` *and* by the boundary.
        let mut host = Graph::empty(1);
        let inner = host.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let outer = host.add(NodeKind::Op(Prim::Not), inner.clone());
        host.close(vec![outer[0], inner[0]]);
        host.check().unwrap();

        let pair = Pair::new(
            {
                let mut g = Graph::empty(1);
                let first = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
                let second = g.add(NodeKind::Op(Prim::Not), first);
                // The middle port is not exported, and nothing about
                // that holds the rule to an unshared window.
                g.close(second);
                g
            },
            Graph::of_box(NodeKind::Op(Prim::AsBool)),
        )
        .unwrap();

        let found = pair.find(&host, Direction::Forward);
        assert_eq!(found.len(), 1, "the shared window is still a window");
        pair.apply(&mut host, Direction::Forward, &found[0])
            .expect("a shared window is a window");
        host.check().unwrap();
        assert_eq!(host.live_count(), 2, "\n{}", host);
        assert!(
            host.live()
                .any(|(_, kind)| matches!(kind, NodeKind::Op(Prim::AsBool))),
            "the coercion landed:\n{}",
            host
        );
        assert!(
            host.live()
                .any(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Not))),
            "and the `not` the boundary still reads is still there:\n{}",
            host
        );
    }

    /// A pair is held to the one thing a rewrite needs of it.
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
    /// torn graph. Everything is checked before a box is made, so what it
    /// refuses it also leaves alone.
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
        };
        let mut spoiled = host.clone();
        assert_eq!(
            pair.apply(&mut spoiled, Direction::Forward, &wrong),
            Err(Mismatch::Kind(push))
        );
        assert_eq!(spoiled, host, "a refusal changes nothing");

        // The right box, named twice.
        let doubled = Match {
            nodes: vec![add, add],
            inputs: host.sources(add).to_vec(),
        };
        let mut spoiled = host.clone();
        assert_eq!(
            pair.apply(&mut spoiled, Direction::Forward, &doubled),
            Err(Mismatch::Shape)
        );
        assert_eq!(spoiled, host, "a refusal changes nothing");
    }

    /// The one refusal substitution has of its own: a replacement the
    /// graph already holds, that reads the very value it would stand for.
    ///
    /// `promised-bool` says `op = op ; as_bool`, and where the `as_bool`
    /// is already standing the step says nothing — putting it in would
    /// rebuild it into a reading of itself.
    #[test]
    fn a_replacement_that_reads_what_it_replaces_is_refused() {
        let mut host = Graph::empty(1);
        let test = host.add(NodeKind::Op(Prim::IsBool), vec![Source::Input(0)]);
        let coerced = host.add(NodeKind::Op(Prim::AsBool), test.clone());
        host.close(coerced);
        host.check().unwrap();

        let pair = Pair::new(Graph::of_box(NodeKind::Op(Prim::IsBool)), {
            let mut g = Graph::empty(1);
            let answer = g.add(NodeKind::Op(Prim::IsBool), vec![Source::Input(0)]);
            let promised = g.add(NodeKind::Op(Prim::AsBool), answer);
            g.close(promised);
            g
        })
        .unwrap();

        let at = Match {
            nodes: vec![
                host.live()
                    .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::IsBool)))
                    .expect("the test")
                    .0,
            ],
            inputs: vec![Source::Input(0)],
        };
        let before = host.clone();
        assert_eq!(
            pair.apply(&mut host, Direction::Forward, &at),
            Err(Mismatch::Circular(test[0]))
        );
        assert_eq!(host, before, "a refusal changes nothing");
    }

    // ---- one embedding read through another ----

    /// Composition, on its own: a match of `P` in `G` and an embedding of
    /// `G` in `H` make a match of `P` in `H` — and the answer is a real
    /// match, which is to say the checker takes it.
    #[test]
    fn a_match_read_through_an_embedding_is_a_match() {
        // `H`: `not ; negate ; not`. `G`: the deepest two of them.
        let mut host = Graph::empty(1);
        let a = host.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let b = host.add(NodeKind::Op(Prim::Negate), a.clone());
        let c = host.add(NodeKind::Op(Prim::Not), b);
        host.close(c);
        host.check().unwrap();

        let mut inner = Graph::empty(1);
        let first = inner.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let second = inner.add(NodeKind::Op(Prim::Negate), first);
        inner.close(second);

        let outer = find(&host, &inner)
            .into_iter()
            .find(|at| at.nodes[0] == NodeId::at(0))
            .expect("the deepest pair");
        let carried = Embedding::of(&outer);

        // `P`: one `negate`, matched at the second box of `G`.
        let one = Graph::of_box(NodeKind::Op(Prim::Negate));
        let there = find(&inner, &one).into_iter().next().expect("the negate");

        let here = carried.carry(&there).expect("the embedding covers it");
        assert_eq!(here.nodes, vec![NodeId::at(1)]);
        assert_eq!(here.inputs, [a[0]], "the deepest `not` feeds it");
        check_match(&host, &one, &here).expect("a composed match is a match");
    }

    /// An embedding says nothing about what it does not cover.
    #[test]
    fn an_embedding_carries_only_what_it_holds() {
        let carried = Embedding::of(&Match {
            nodes: vec![NodeId::at(7)],
            inputs: vec![Source::Input(3)],
        });
        assert_eq!(carried.node(NodeId::at(0)), Some(NodeId::at(7)));
        assert_eq!(carried.node(NodeId::at(1)), None);

        let stranger = Match {
            nodes: vec![NodeId::at(1)],
            inputs: vec![Source::Input(0)],
        };
        assert_eq!(carried.carry(&stranger), None, "box 1 is not covered");
    }
}
