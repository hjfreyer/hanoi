//! The literal diagram: a term as a graph of boxes, rewritten until the
//! connections are direct.
//!
//! [`crate::diagram`] is called a string-diagram engine, but it never builds
//! a diagram. Its `normalize` *evaluates* a term on a stack of symbolic
//! wires and lands in the answer — an interned value-DAG under an ordered
//! case tree — so the structural layer of
//! [docs/algebra.md](../../docs/algebra.md) is "representation" in the
//! strongest sense: it is never data at all. That is exactly why the whole
//! layer is free there, and exactly why there is nothing to point at, and
//! nothing for a rewrite to act on.
//!
//! This module takes the other road. A term becomes a graph **one leaf at a
//! time**, `id`, `swap`, `copy` and `drop` each getting a box of their own,
//! and only then does anything get simplified — by rewriting. Four rules,
//! and every one of them is the same move: delete a node and join what it
//! was standing between.
//!
//! A branch is not a box either, and that is the one place this is not a
//! literal reading of the term. Its arms are emitted **into the same
//! graph**: a `copy(n)` hands each arm its own view of the stack, both run,
//! and a `select(n)` at the end keeps one of the two answers. That `copy`
//! is exactly the `(pick (n-1))^n` of the single-arm hoist in
//! [docs/totality.md](../../docs/totality.md), and the hoist is why the
//! translation is allowed: every prim is total and has no effect but the
//! stack, so work on the path not taken costs an answer nobody reads rather
//! than a failure. The gain is that nothing is opaque any more — a rule
//! reaches into an arm from outside, and a value reaches out of one.
//!
//! - `id-elim` — the readers of an `id`'s output read its input instead.
//! - `swap-elim` — the two lines cross by being re-pointed, and the
//!   crossing stops existing. σ involutive, σ-natural and Yang–Baxter all
//!   fall out of the fact that nothing recorded the crossing afterwards.
//! - `copy-elim` — both of a `copy`'s outputs come to name the port it was
//!   reading, and that port acquires a *second reader*. This is the one
//!   rule that changes the shape of the data rather than shrinking it, and
//!   it is where the cartesian structure enters: a value is produced once
//!   and read freely.
//! - `dead-node` — a node nothing reads is deleted, and its own producers
//!   are asked the same question. `drop(n)` has no outputs at all, so it is
//!   this rule's base case rather than a rule of its own; the language is
//!   total and pure, which is what licenses deleting the work underneath —
//!   the same license that lets both arms of a branch run.
//!
//! What the rules leave is a DAG of `Op`s, `Call`s and `Select`s whose
//! ports fan out where a `copy` used to be — the same shape `diagram`
//! arrives at by construction, reached instead by named deletions over data
//! that existed the whole way.
//!
//! **Ports link to ports; there is no wire.** An input names the one output
//! port it reads ([`Source`]) and an output names the input ports that read
//! it ([`Sink`]), so a rewrite is a re-pointing rather than a declaration
//! that two names are equivalent. Nothing accumulates: after each step the
//! graph is already in its final state, which is what makes `dead-node` an
//! O(1) test and lets [`Graph::check`] hold every link to agreeing at both
//! ends — a half-updated link is caught where it happens rather than
//! surviving as a wrong answer.
//!
//! **Three things are deliberately absent**, and none of them is an
//! oversight:
//!
//! - **Equality.** Two graphs are never asked to be the same. `push 9 ;
//!   copy(1)` rewrites to one `push` node read twice and `push 9 ; push 9`
//!   to two nodes, and nothing here identifies them — that is δ-naturality,
//!   which `diagram` buys by interning and this module has not bought. So
//!   this decides nothing, judges nothing, and is not wired into
//!   [`crate::strategy`]; `diagram` remains the prover's engine. Nor do the
//!   tests borrow its judgement: what they claim about *meaning* they claim
//!   by evaluating both programs with **every operation left opaque** and
//!   comparing the graphs of applications that come out. `add` on two wires
//!   stays `add(x, y)` and never becomes `7`, so that oracle decides nothing
//!   either — it holds the wiring to account and stops there.
//! - **Dedup.** The one structural rule that is not a local deletion —
//!   deciding two nodes compute the same thing means comparing kinds and
//!   then, transitively, everything they read. It would buy δ-naturality
//!   and a smaller graph; with no equality operation to serve, it waits.
//! - **The value folds and the branch layer.** No literal window runs, no
//!   commutative operand sorts, no condition selects its arm, no case tree
//!   is ordered. Layers 2 and 3 of the algebra sheet are untouched, so
//!   `push 1 ; push 2 ; add` keeps all three of its boxes. `select` is now
//!   where the third of those would go — a literal condition would pick a
//!   block and the node would vanish — which makes the absence a missing
//!   rule on one node rather than a missing layer.
//!
//! [`read_back`] is the other half of the translation: a graph is scheduled
//! onto a stack, and the routing between one step and the next is *layered*
//! — one `*`-product of `copy`/`id`/`drop` to get the multiplicities right,
//! then a `*`-product of `swap`s per transposition round to get the order
//! right. A box is placed where its operands already sit rather than on
//! top, so the survivors pass either side of it and nothing is dragged up
//! and put back; `pick 1` comes back as `copy(1) * id(1) ; id(1) * swap`.
//! That is a choice about legibility and nothing more. What comes back is
//! *a* term meaning what the graph means, not the term it was built from —
//! a branch in particular reads back as both arms run flat and then a
//! branch that throws one answer away, which is what the graph now says a
//! branch is.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fmt;

use bytecode::SentenceIndex;

use crate::term::{Arity, Context, Prim, Term, TermIndex};

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

/// What a box is — [`Term`]'s leaves, one for one.
///
/// The two operators are what the graph replaces; everything else survives
/// the translation unchanged. `swap` in particular stays an
/// [`Op`][NodeKind::Op]: it is a prim like any other, and the rewriter is
/// where the fact that it is *structural* gets used, not the type.
#[derive(Debug, Clone)]
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
    /// the same reason [`Term::Call`] carries it.
    Call { target: SentenceIndex, arity: Arity },
    /// `select(n)`: the two blocks of an answer, and the condition that
    /// keeps one of them.
    ///
    /// Inputs `0..n` are the `then` block, inputs `n..2n` the `else` block,
    /// and input `2n` — the topmost, where the condition sits in the term —
    /// chooses. Output `i` is input `i` when the condition holds and input
    /// `n + i` otherwise, blockwise exactly as `copy(n)` is, and this is
    /// that `copy` read backwards.
    ///
    /// A branch's arms are not in here. They are ordinary boxes in the one
    /// graph, wired from a `copy(n)` that hands each arm its own view of the
    /// stack, and this node is only the last step, where the two answers
    /// meet and one is let go. So both arms are computed, which is the
    /// single-arm hoist of [docs/totality.md](../../docs/totality.md) —
    /// sound because every [`Prim`] is total, has no effect but the stack,
    /// and, unlike the term-level rule, states its arity locally even when
    /// it is a [`NodeKind::Call`].
    Select(usize),
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
            NodeKind::Select(n) => Arity::new(2 * n + 1, *n),
        }
    }

    /// Whether this is one of the boxes rewriting is here to delete.
    ///
    /// `drop` is not on the list: it goes by `dead-node`, which is about
    /// having no readers rather than about being structural.
    pub fn is_structural(&self) -> bool {
        matches!(
            self,
            NodeKind::Id(_) | NodeKind::Copy(_) | NodeKind::Op(Prim::Swap)
        )
    }
}

#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, Default)]
pub struct Graph {
    nodes: Vec<Option<Node>>,
    /// The readers of each boundary input, deepest first.
    inputs: Vec<Vec<Sink>>,
    /// What each boundary output reads, deepest first.
    outputs: Vec<Source>,
}

impl Graph {
    fn empty(inputs: usize) -> Graph {
        Graph {
            nodes: Vec::new(),
            inputs: vec![Vec::new(); inputs],
            outputs: Vec::new(),
        }
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
    fn add(&mut self, kind: NodeKind, inputs: Vec<Source>) -> Vec<Source> {
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

    /// Closes the graph: these sources are what the boundary leaves.
    fn close(&mut self, sources: Vec<Source>) {
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

    /// Everything that read output `port` of `node` reads `src` instead —
    /// the whole of "make the connection direct", in one move.
    fn redirect(&mut self, node: NodeId, port: usize, src: Source) {
        let moved = std::mem::take(&mut self.node_mut(node).outputs[port]);
        for &sink in &moved {
            self.set_source(sink, src);
        }
        self.sinks_mut(src).extend(moved);
    }

    /// Deletes a node nothing reads, unlinking it from its producers, and
    /// names those producers — they are the ones that may have just become
    /// unread themselves.
    fn remove(&mut self, id: NodeId) -> Vec<NodeId> {
        let inputs = self.node(id).inputs.clone();
        for (port, &src) in inputs.iter().enumerate() {
            self.unlink(src, Sink::Port { node: id, port });
        }
        self.nodes[id.index()] = None;
        inputs
            .iter()
            .filter_map(|src| match src {
                Source::Port { node, .. } => Some(*node),
                Source::Input(_) => None,
            })
            .collect()
    }
}

// ---- a term, literally ---------------------------------------------------------

/// The graph of a term: one node per leaf, nothing simplified.
///
/// Every law of the structural layer still has a spelling here, which is
/// the difference from [`crate::diagram`] and the whole premise of the
/// module — [`rewrite`] is what spends them.
pub fn build(terms: &Context, term: TermIndex) -> Graph {
    let arity = terms.arity(term);
    let mut graph = Graph::empty(arity.inputs);
    let inputs: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();
    let outputs = emit(&mut graph, terms, term, inputs);
    graph.close(outputs);
    graph
}

/// One term on the sources standing for its inputs, deepest first,
/// answering with the sources standing for its outputs.
fn emit(graph: &mut Graph, terms: &Context, term: TermIndex, inputs: Vec<Source>) -> Vec<Source> {
    debug_assert_eq!(
        inputs.len(),
        terms.arity(term).inputs,
        "the caller cuts by arity"
    );
    match terms.get(term) {
        Term::Id(n) => graph.add(NodeKind::Id(*n), inputs),
        Term::Copy(n) => graph.add(NodeKind::Copy(*n), inputs),
        Term::Drop(n) => graph.add(NodeKind::Drop(*n), inputs),
        Term::Op(prim) => graph.add(NodeKind::Op(prim.clone()), inputs),
        Term::Call { target, arity } => graph.add(
            NodeKind::Call {
                target: *target,
                arity: *arity,
            },
            inputs,
        ),
        // `;` is not a node: sequencing is one box's output port being
        // another's input.
        Term::Compose(first, then) => {
            let middle = emit(graph, terms, *first, inputs);
            emit(graph, terms, *then, middle)
        }
        // `*` is not a node either: side by side is two boxes sharing no
        // ports. The second argument gets the top, as it does in the term.
        Term::Par(deep, top) => {
            let mut inputs = inputs;
            let above = inputs.split_off(inputs.len() - terms.arity(*top).inputs);
            let mut outputs = emit(graph, terms, *deep, inputs);
            outputs.extend(emit(graph, terms, *top, above));
            outputs
        }
        // A branch is not a node either, and this is the change from the
        // arms-in-a-box it used to be: the condition is set aside, a
        // `copy(n)` hands each arm its own view of the stack, both arms are
        // emitted into this same graph, and a `select` at the end keeps one
        // of the two answers. What was a boundary is now just wiring, so
        // every rule reaches through it.
        Term::Branch { if_true, if_false } => {
            let mut inputs = inputs;
            let cond = inputs.pop().expect("a branch reads its condition");
            // `copy(n)` is block-wise, which is exactly the fork wanted
            // here — and exactly the `(pick (n-1))^n` the hoist rule spells
            // out. Nothing to duplicate is no box.
            let (if_true_in, if_false_in) = if inputs.is_empty() {
                (Vec::new(), Vec::new())
            } else {
                let n = inputs.len();
                let mut blocks = graph.add(NodeKind::Copy(n), inputs);
                let above = blocks.split_off(n);
                (blocks, above)
            };
            let mut ports = emit(graph, terms, *if_true, if_true_in);
            ports.extend(emit(graph, terms, *if_false, if_false_in));
            ports.push(cond);
            graph.add(NodeKind::Select(terms.arity(*if_true).outputs), ports)
        }
    }
}

// ---- rewriting -----------------------------------------------------------------

/// Every structural box deleted, at every depth.
///
/// A worklist rather than repeated passes, which the back-links are what
/// make possible: firing a rule leaves the graph already correct, so the
/// only thing to reconsider is the handful of nodes the deletion could have
/// affected — the producers of what went away, which may now be unread.
/// Every rule strictly decreases the live node count, so it drains.
pub fn rewrite(graph: &mut Graph) {
    rewrite_watching(graph, &mut |_| {});
}

/// [`rewrite`], with a witness run against the graph after every single
/// firing. The tests use it to hold [`Graph::check`] at each step rather
/// than only at the fixpoint.
fn rewrite_watching(graph: &mut Graph, after: &mut dyn FnMut(&Graph)) {
    let mut work: Vec<NodeId> = (0..graph.nodes.len())
        .map(|i| NodeId(i as u32))
        .filter(|&id| graph.is_live(id))
        .collect();
    while let Some(id) = work.pop() {
        if !graph.is_live(id) {
            continue;
        }
        if let Some(again) = fire(graph, id) {
            after(graph);
            work.extend(again);
        }
    }
}

/// One node, and whichever rule it answers to. `None` is a node no rule
/// reaches; `Some` names what to reconsider.
fn fire(graph: &mut Graph, id: NodeId) -> Option<Vec<NodeId>> {
    // `dead-node`, and with it `drop-elim`: a box nothing reads is nothing,
    // because the language is total and pure. A `drop(n)` has no outputs at
    // all, so it is always the first thing this sees.
    if graph.node(id).outputs.iter().all(Vec::is_empty) {
        return Some(graph.remove(id));
    }
    // The rest are one shape: for each output port, the input port whose
    // source its readers should name instead.
    let carries: Vec<(usize, usize)> = match graph.kind(id) {
        NodeKind::Id(n) => (0..*n).map(|i| (i, i)).collect(),
        NodeKind::Op(Prim::Swap) => vec![(0, 1), (1, 0)],
        NodeKind::Copy(n) => {
            let n = *n;
            (0..n).flat_map(|i| [(i, i), (n + i, i)]).collect()
        }
        _ => return None,
    };
    for (out_port, in_port) in carries {
        let src = graph.node(id).inputs[in_port];
        graph.redirect(id, out_port, src);
    }
    Some(graph.remove(id))
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
    /// [`build`]t graph, and false from the first `copy-elim` onwards.
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
        }
    }
}

impl std::error::Error for Error {}

// ---- reading a graph back as a term ----------------------------------------------

/// The graph as a [`Term`] again.
///
/// A graph has no stack, so one has to be reimposed: the nodes are put in a
/// topological order and run one at a time, with a **routing** step between
/// them that gathers what the next box reads and lets go of what nothing
/// wants any more. A [`Source`] is a stable name for a value — one producer
/// port — which is exactly what a stack slot needs to be keyed by.
///
/// Two things keep the result readable, and they are where this differs
/// from `diagram`'s reify. The routing is **layered**: one `*`-product to
/// fix the multiplicities, then one per transposition round to fix the
/// order, instead of a bubble chain per value. And a box is placed **where
/// its operands already are** rather than on top, so the survivors pass
/// either side of it and a term written `X * id(1)` comes back as
/// `X * id(1)` rather than as the roll pair it is equal to.
///
/// Both are about legibility. Many terms mean what a given graph means and
/// this picks one of them; it does not undo [`build`], and a branch is where
/// that shows plainest — the arms were flattened into the graph and are
/// scheduled like any other work, so what comes back runs both of them and
/// then chooses.
pub fn read_back(graph: &Graph, terms: &mut Context) -> TermIndex {
    let order = schedule(graph);
    // What is still wanted at or after each step, the boundary included.
    let mut wanted: Vec<HashSet<Source>> = vec![HashSet::new(); order.len() + 1];
    wanted[order.len()] = graph.outputs.iter().copied().collect();
    for k in (0..order.len()).rev() {
        let mut set = wanted[k + 1].clone();
        set.extend(graph.node(order[k]).inputs.iter().copied());
        wanted[k] = set;
    }

    let mut steps: Vec<TermIndex> = Vec::new();
    let mut stack: Vec<Source> = (0..graph.inputs.len()).map(Source::Input).collect();
    for (k, &id) in order.iter().enumerate() {
        let sources: Vec<Source> = graph.node(id).inputs.clone();
        let keep: Vec<Source> = stack
            .iter()
            .copied()
            .filter(|src| wanted[k + 1].contains(src))
            .collect();
        // Where the box goes. Not the top: a box sits just above whatever
        // it reads that lies deepest, so one that only touches the middle
        // of the stack stays in the middle instead of dragging its operands
        // up and the survivors back down afterwards. Putting everything on
        // top would mean the same thing and read far worse — `X * id(1)`
        // would come back as the roll pair it is equal to — and legibility
        // is the whole of the reason. A box that reads nothing has nothing
        // to sit above, so it lands on top.
        let anchor = sources
            .iter()
            .filter_map(|src| stack.iter().position(|held| held == src))
            .min()
            .unwrap_or(stack.len());
        let below = stack[..anchor]
            .iter()
            .filter(|src| wanted[k + 1].contains(src))
            .count();
        let above = keep.len() - below;

        let mut want: Vec<Source> = keep[..below].to_vec();
        want.extend(sources.iter().copied());
        want.extend(keep[below..].iter().copied());
        steps.extend(route(terms, &stack, &want));

        // The survivors pass either side of the box, so a step spans the
        // whole stack — which is what lets the fold below be a plain
        // `compose`, and a width mismatch a loud one.
        let step = box_term(terms, graph.kind(id));
        let step = terms.under(step, below);
        let step = if above > 0 {
            let untouched = terms.id(above);
            terms.par(step, untouched)
        } else {
            step
        };
        steps.push(step);

        let mut next: Vec<Source> = keep[..below].to_vec();
        next.extend(
            (0..graph.kind(id).arity().outputs).map(|port| Source::Port { node: id, port }),
        );
        next.extend(keep[below..].iter().copied());
        stack = next;
    }
    steps.extend(route(terms, &stack, &graph.outputs));

    let mut steps = steps.into_iter();
    // Nothing to do at all is the identity on the inputs, not on nothing.
    let Some(first) = steps.next() else {
        return terms.id(graph.inputs.len());
    };
    steps.fold(first, |acc, next| {
        terms
            .compose(acc, next)
            .expect("every step spans the whole stack")
    })
}

/// The term one box stands for; a branch answers with its arms read back.
fn box_term(terms: &mut Context, kind: &NodeKind) -> TermIndex {
    match kind {
        NodeKind::Id(n) => terms.id(*n),
        NodeKind::Copy(n) => terms.copy(*n),
        NodeKind::Drop(n) => terms.drop(*n),
        NodeKind::Op(prim) => terms.op(prim.clone()),
        NodeKind::Call { target, arity } => terms.call(*target, *arity),
        // Both blocks are already on the stack by the time this runs — the
        // arms were scheduled like any other work — so the branch left to
        // write is only the choice between them: keep one block, let the
        // other go.
        NodeKind::Select(n) => {
            let (keep, lose) = (terms.id(*n), terms.drop(*n));
            let if_true = terms.par(keep, lose);
            let (lose, keep) = (terms.drop(*n), terms.id(*n));
            let if_false = terms.par(lose, keep);
            terms
                .branch(if_true, if_false)
                .expect("each arm keeps one block of two")
        }
    }
}

/// The live nodes in an order that runs producers first, smallest id first
/// among those ready — which is roughly the order they were built in, so
/// the term that comes out reads like the term that went in.
fn schedule(graph: &Graph) -> Vec<NodeId> {
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

/// The steps taking a stack of *distinct* sources to `want`, which may
/// repeat what it takes and leave out what it does not.
///
/// Two layers, and each is one `;`-step: the multiplicities first, then the
/// order. Both are `*`-products over the whole width, so a step reads as a
/// row of the diagram rather than as a chain of moves.
fn route(terms: &mut Context, have: &[Source], want: &[Source]) -> Vec<TermIndex> {
    debug_assert!(
        want.iter().all(|w| have.contains(w)),
        "routing cannot conjure a value the stack does not hold"
    );
    let copies: Vec<usize> = have
        .iter()
        .map(|h| want.iter().filter(|w| *w == h).count())
        .collect();

    let mut steps = Vec::new();
    // The copy layer: one factor per slot, `drop(1)` for a value nothing
    // wants, `id(1)` for one that is wanted once, a short chain otherwise.
    if copies.iter().any(|&k| k != 1) {
        let mut layer: Option<TermIndex> = None;
        for &k in &copies {
            let factor = duplicate(terms, k);
            layer = Some(match layer {
                None => factor,
                Some(acc) => terms.par(acc, factor),
            });
        }
        if let Some(layer) = layer {
            steps.push(layer);
        }
    }

    // Where each of the duplicated slots has to end up.
    let mut spread: Vec<Source> = Vec::new();
    for (j, &h) in have.iter().enumerate() {
        spread.extend(std::iter::repeat_n(h, copies[j]));
    }
    let mut taken = vec![false; want.len()];
    let mut places: Vec<usize> = Vec::with_capacity(spread.len());
    for &src in &spread {
        let slot = want
            .iter()
            .enumerate()
            .find(|&(i, &w)| !taken[i] && w == src)
            .map(|(i, _)| i)
            .expect("the copy layer produced exactly what is wanted");
        taken[slot] = true;
        places.push(slot);
    }

    // The permutation layer: odd–even transposition rounds, each a
    // `*`-product of `swap`s and the identities between them. `swap` is the
    // only reordering the term language has, so a sequence of rounds is
    // what a permutation costs — but each round is one flat row.
    let width = places.len();
    for round in 0..width {
        let crossings: Vec<usize> = (round % 2..width.saturating_sub(1))
            .step_by(2)
            .filter(|&i| places[i] > places[i + 1])
            .collect();
        if crossings.is_empty() {
            continue;
        }
        for &i in &crossings {
            places.swap(i, i + 1);
        }
        let mut layer: Option<TermIndex> = None;
        let mut slot = 0;
        while slot < width {
            let factor = if crossings.contains(&slot) {
                slot += 2;
                terms.op(Prim::Swap)
            } else {
                slot += 1;
                terms.id(1)
            };
            layer = Some(match layer {
                None => factor,
                Some(acc) => terms.par(acc, factor),
            });
        }
        if let Some(layer) = layer {
            steps.push(layer);
        }
    }
    debug_assert!(
        places.windows(2).all(|pair| pair[0] < pair[1]),
        "the rounds sort"
    );
    steps
}

/// `1 -> k`: the value dropped, passed through, or copied that many times.
fn duplicate(terms: &mut Context, k: usize) -> TermIndex {
    match k {
        0 => terms.drop(1),
        1 => terms.id(1),
        _ => {
            let mut chain = terms.copy(1);
            for held in 2..k {
                let more = terms.copy(1);
                let step = terms.under(more, held - 1);
                chain = terms
                    .compose(chain, step)
                    .expect("each link of the chain meets the last");
            }
            chain
        }
    }
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
            NodeKind::Select(n) => write!(f, "select({})", n),
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
    use crate::term::lower;
    use bytecode::{Library, SentenceIndex, assemble};

    // ---- meaning, with the prims left opaque ------------------------------------

    /// A name for one value in the symbolic reading of a program.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    struct SymId(u32);

    /// What a value *is*, with every operation left uninterpreted.
    ///
    /// `add` on two wires is the node `add(x, y)` and never `7`: nothing is
    /// run, so this decides no more equalities than the wiring forces. A
    /// branch is a [`Sym::Choice`] **per output** rather than a fork in
    /// control — which is the same claim the graph makes with `select`, and
    /// the reason there is no case tree here to explode.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Sym {
        /// Boundary input `i`.
        Var(usize),
        /// Output `out` of one opaque operation. `op` indexes [`Meaning::ops`];
        /// a call is opaque too, so nothing is ever opened.
        App {
            op: u32,
            args: Vec<SymId>,
            out: usize,
        },
        /// One of two values, according to `cond`.
        Choice {
            cond: SymId,
            if_true: SymId,
            if_false: SymId,
        },
    }

    /// An interning arena: two programs mean the same thing when they land on
    /// the same [`SymId`].
    ///
    /// Interning identifies `push 9 ; copy(1)` with `push 9 ; push 9`, which is
    /// the δ-naturality the module itself has *not* bought. That only ever
    /// makes an oracle more permissive, so it is safe here — but it is a fact
    /// about this test scaffolding, not a position the engine has changed.
    #[derive(Default)]
    struct Meaning {
        nodes: Vec<Sym>,
        seen: HashMap<Sym, SymId>,
        /// Operations by their printed form, since [`Prim`] is not hashable.
        ops: Vec<String>,
    }

    impl Meaning {
        fn intern(&mut self, node: Sym) -> SymId {
            if let Some(&id) = self.seen.get(&node) {
                return id;
            }
            let id = SymId(self.nodes.len() as u32);
            self.nodes.push(node.clone());
            self.seen.insert(node, id);
            id
        }

        fn var(&mut self, i: usize) -> SymId {
            self.intern(Sym::Var(i))
        }

        fn op(&mut self, name: String) -> u32 {
            match self.ops.iter().position(|held| *held == name) {
                Some(i) => i as u32,
                None => {
                    self.ops.push(name);
                    (self.ops.len() - 1) as u32
                }
            }
        }

        /// One opaque operation applied, answering with all of its outputs.
        fn apply(&mut self, name: String, args: Vec<SymId>, outputs: usize) -> Vec<SymId> {
            let op = self.op(name);
            (0..outputs)
                .map(|out| {
                    self.intern(Sym::App {
                        op,
                        args: args.clone(),
                        out,
                    })
                })
                .collect()
        }

        /// Two blocks of an answer paired position by position.
        fn choose(&mut self, cond: SymId, if_true: &[SymId], if_false: &[SymId]) -> Vec<SymId> {
            assert_eq!(if_true.len(), if_false.len(), "the arms answer alike");
            if_true
                .iter()
                .zip(if_false)
                .map(|(&if_true, &if_false)| {
                    self.intern(Sym::Choice {
                        cond,
                        if_true,
                        if_false,
                    })
                })
                .collect()
        }
    }

    /// The name of the one operation a prim stands for — or, for `swap`, none:
    /// `swap` is routing, and reading it as an opaque box would make the very
    /// cancellation `swap-elim` performs look like a change of meaning.
    fn opaque(prim: &Prim) -> Option<String> {
        match prim {
            Prim::Swap => None,
            other => Some(format!("{:?}", other)),
        }
    }

    /// What a term means, on the symbols standing for its inputs.
    fn eval_term(
        m: &mut Meaning,
        terms: &Context,
        term: TermIndex,
        stack: Vec<SymId>,
    ) -> Vec<SymId> {
        debug_assert_eq!(
            stack.len(),
            terms.arity(term).inputs,
            "the caller cuts by arity"
        );
        match terms.get(term) {
            Term::Id(_) => stack,
            Term::Drop(_) => Vec::new(),
            // Block-wise, as the box is.
            Term::Copy(_) => {
                let mut out = stack.clone();
                out.extend(stack);
                out
            }
            Term::Op(prim) => match opaque(prim) {
                None => vec![stack[1], stack[0]],
                Some(name) => m.apply(name, stack, prim.arity().outputs),
            },
            Term::Call { target, arity } => {
                m.apply(format!("call {:?}", target), stack, arity.outputs)
            }
            // Both spines are walked rather than recursed down. A read-back
            // emits a step per box and folds them left, and a routing layer
            // is a `*`-product over the whole width, so these chains are as
            // long as the graph is wide and deep — recursion overflows a
            // test thread's stack on the corpus.
            Term::Compose(..) => {
                let mut spine = Vec::new();
                let mut head = term;
                while let Term::Compose(first, then) = terms.get(head) {
                    spine.push(*then);
                    head = *first;
                }
                let mut stack = eval_term(m, terms, head, stack);
                for step in spine.into_iter().rev() {
                    stack = eval_term(m, terms, step, stack);
                }
                stack
            }
            Term::Par(..) => {
                let mut spine = Vec::new();
                let mut head = term;
                while let Term::Par(deep, top) = terms.get(head) {
                    spine.push(*top);
                    head = *deep;
                }
                // The stack is cut from the top down, since `spine` holds
                // the topmost factor first.
                let mut stack = stack;
                let parts: Vec<Vec<SymId>> = spine
                    .iter()
                    .map(|&factor| {
                        let width = terms.arity(factor).inputs;
                        stack.split_off(stack.len() - width)
                    })
                    .collect();
                let mut out = eval_term(m, terms, head, stack);
                for (&factor, part) in spine.iter().zip(parts).rev() {
                    out.extend(eval_term(m, terms, factor, part));
                }
                out
            }
            // Both arms on the same stack, and a choice per output. With the
            // prims opaque that *is* what a branch means, so the hoist the
            // graph performs is invisible here — which is exactly what makes
            // this oracle linear where a case tree is not.
            Term::Branch { if_true, if_false } => {
                let mut stack = stack;
                let cond = stack.pop().expect("a branch reads its condition");
                let taken = eval_term(m, terms, *if_true, stack.clone());
                let not = eval_term(m, terms, *if_false, stack);
                m.choose(cond, &taken, &not)
            }
        }
    }

    /// What a graph means — the same reading, one box at a time.
    ///
    /// No `read_back` anywhere in it, which is the point: this can hold
    /// `rewrite` to preserving meaning without the translation in the loop.
    fn eval_graph(m: &mut Meaning, graph: &Graph, inputs: &[SymId]) -> Vec<SymId> {
        let mut ports: HashMap<(NodeId, usize), SymId> = HashMap::new();
        let read = |ports: &HashMap<(NodeId, usize), SymId>, src: Source| match src {
            Source::Input(i) => inputs[i],
            Source::Port { node, port } => ports[&(node, port)],
        };
        for id in schedule(graph) {
            let args: Vec<SymId> = graph
                .node(id)
                .inputs
                .iter()
                .map(|&src| read(&ports, src))
                .collect();
            let outs = match graph.kind(id) {
                NodeKind::Id(_) => args,
                NodeKind::Drop(_) => Vec::new(),
                NodeKind::Copy(_) => {
                    let mut out = args.clone();
                    out.extend(args);
                    out
                }
                NodeKind::Op(prim) => match opaque(prim) {
                    None => vec![args[1], args[0]],
                    Some(name) => m.apply(name, args, prim.arity().outputs),
                },
                NodeKind::Call { target, arity } => {
                    m.apply(format!("call {:?}", target), args, arity.outputs)
                }
                NodeKind::Select(n) => {
                    let cond = args[2 * n];
                    let (taken, not) = args.split_at(*n);
                    m.choose(cond, &taken[..*n], &not[..*n])
                }
            };
            for (port, sym) in outs.into_iter().enumerate() {
                ports.insert((id, port), sym);
            }
        }
        graph.outputs.iter().map(|&src| read(&ports, src)).collect()
    }

    /// Fresh symbols for `n` boundary inputs.
    fn boundary(m: &mut Meaning, n: usize) -> Vec<SymId> {
        (0..n).map(|i| m.var(i)).collect()
    }

    /// The term a sentence written inline lowers to, built in `terms`.
    fn term_of(terms: &mut Context, body: &str) -> TermIndex {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        lower(terms, &library, idx).unwrap()
    }

    /// The graph a body builds, checked, with the arena its term lives in.
    fn built(body: &str) -> (Context, Graph) {
        let mut terms = Context::new();
        let term = term_of(&mut terms, body);
        let graph = build(&terms, term);
        graph.check().unwrap_or_else(|e| panic!("{}\n{}", e, graph));
        (terms, graph)
    }

    /// The same, rewritten to fixpoint.
    fn rewritten(body: &str) -> (Context, Graph) {
        let (terms, mut graph) = built(body);
        rewrite(&mut graph);
        graph.check().unwrap_or_else(|e| panic!("{}\n{}", e, graph));
        (terms, graph)
    }

    /// Every sentence the integration suite compiles, lowered into one
    /// arena — the same corpus `diagram`'s round trip runs on.
    fn corpus() -> (Library, Context, Vec<(SentenceIndex, TermIndex)>) {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the crate sits in the workspace")
            .join("tests");
        let text = std::fs::read_to_string(tests.join("main.hana")).unwrap();
        let mut map = bytecode::SourceMap::new();
        let file = map.add("main.hana", text);
        let library = bytecode::assemble_source(&mut map, file, Some(&tests))
            .unwrap_or_else(|e| panic!("{}", map.render(&e)));
        let mut arena = Context::new();
        let lowered = crate::term::lower_all(&mut arena, &library).unwrap();
        let terms = lowered.iter_enumerated().map(|(i, &t)| (i, t)).collect();
        (library, arena, terms)
    }

    /// Whether no structural box survives — one sweep now, since a
    /// branch's arms are boxes in the same graph as everything else.
    fn no_structure(graph: &Graph) -> bool {
        graph.live().all(|(_, kind)| !kind.is_structural())
    }

    // ---- the literal translation ----

    #[test]
    fn a_term_is_one_box_per_leaf() {
        // `push 1 ; id(1) * push 2 ; add`: four leaves, four boxes. The `;`
        // and the `*` have no spelling — sequencing is one box's output
        // port being another's input, side by side is two boxes sharing no
        // ports — but the `id(1)` the padding introduced is right there as
        // a box, which is the difference from `diagram`.
        let (_terms, graph) = built("push 1 push 2 add");
        assert_eq!(graph.live_count(), 4);
        assert!(
            graph
                .live()
                .any(|(_, kind)| matches!(kind, NodeKind::Id(1))),
            "the padding is data here:\n{}",
            graph
        );
        assert!(graph.is_monogamous());
    }

    #[test]
    fn a_branch_is_its_arms_and_a_select() {
        // The arms are not inside anything: the four boxes of the `then`
        // arm and the one of the `else` arm sit in this graph beside the
        // `select` that picks between their answers. Both arms take
        // nothing, so there is no `copy` to fork the stack either.
        let (_terms, graph) = built("branch { push 1 push 2 add } { push 2 }");
        assert_eq!(graph.live_count(), 6, "{}", graph);

        let (id, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select(1)))
            .expect("the branch ends in a select");
        // Its three inputs: the `then` answer, the `else` answer, and the
        // condition on top, which is the sentence's own input.
        let inputs = graph.node(id).inputs.clone();
        assert_eq!(inputs.len(), 3);
        assert_eq!(inputs[2], Source::Input(0), "the condition is on top");
        assert!(
            matches!(
                (inputs[0], inputs[1]),
                (Source::Port { .. }, Source::Port { .. })
            ),
            "each block is an arm's answer"
        );
    }

    // ---- rewriting: the connections get direct ----

    #[test]
    fn the_boundary_links_straight_through() {
        // Two crossings and nothing left to record them: the outputs name
        // the inputs, which is the whole claim of the module in one line.
        let (_terms, graph) = rewritten("swap swap");
        assert_eq!(graph.live_count(), 0);
        assert_eq!(
            graph.outputs().to_vec(),
            vec![Source::Input(0), Source::Input(1)]
        );

        // The counit: copy, then drop the copy.
        let (_terms, graph) = rewritten("pick 0 drop 0");
        assert_eq!(graph.live_count(), 0);
        assert_eq!(graph.outputs().to_vec(), vec![Source::Input(0)]);
    }

    #[test]
    fn a_permutation_is_the_links_it_leaves() {
        // Yang–Baxter: both spellings of the three-way reversal delete down
        // to no boxes at all, and the links they leave are the same.
        let (_terms, one) = rewritten("swap dip { swap } swap");
        let (_terms, other) = rewritten("dip { swap } swap dip { swap }");
        assert_eq!(one.live_count(), 0);
        assert_eq!(other.live_count(), 0);
        assert_eq!(one.outputs().to_vec(), other.outputs().to_vec());
        assert_eq!(
            one.outputs().to_vec(),
            vec![Source::Input(2), Source::Input(1), Source::Input(0)]
        );
    }

    #[test]
    fn work_nothing_reads_is_no_work() {
        // ε-naturality, by deletion: the `equal` loses its only reader, so
        // it goes, and the copies underneath go with it.
        let (_terms, graph) = rewritten("pick 1 pick 1 equal drop 0");
        assert_eq!(graph.live_count(), 0);
        assert_eq!(
            graph.outputs().to_vec(),
            vec![Source::Input(0), Source::Input(1)]
        );

        let (_terms, graph) = rewritten("add drop 0");
        assert_eq!(graph.live_count(), 0);
        assert!(graph.outputs().is_empty());
    }

    #[test]
    fn a_copy_becomes_a_port_read_twice() {
        let (_terms, graph) = rewritten("push 9 pick 0");
        assert_eq!(graph.live_count(), 1);
        let (id, kind) = graph.live().next().unwrap();
        assert!(matches!(kind, NodeKind::Op(Prim::Push(_))));
        assert_eq!(graph.sinks(Source::Port { node: id, port: 0 }).len(), 2);
        // The moment monogamy breaks is the moment the graph stops being a
        // wiring diagram and starts being cartesian.
        assert!(!graph.is_monogamous());

        // The other spelling is two boxes, and nothing here says the two
        // graphs are one program. That is δ-naturality, which `diagram`
        // buys by interning and this module has not bought.
        let (_terms, twice) = rewritten("push 9 push 9");
        assert_eq!(twice.live_count(), 2);
    }

    #[test]
    fn a_value_reaches_both_arms_directly() {
        // What the flattening buys, in one line. The `copy` that forked the
        // stack for the two arms is gone the same way every other `copy`
        // goes, so both arms read the one port — and the structure inside
        // the `then` arm went with it. Six boxes built, three left: two
        // `not`s and the `select`.
        let (_terms, graph) = rewritten("branch { pick 0 drop 0 not } { not }");
        assert_eq!(graph.live_count(), 3, "{}", graph);
        assert!(no_structure(&graph), "{}", graph);

        let nots: Vec<_> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Not)))
            .map(|(id, _)| id)
            .collect();
        assert_eq!(nots.len(), 2, "one `not` per arm");
        for id in nots {
            assert_eq!(
                graph.node(id).inputs,
                vec![Source::Input(0)],
                "both arms read the one port"
            );
        }
        // Which is a port with two readers: a boundary the rules used to
        // stop at is now just wiring.
        assert_eq!(graph.sinks(Source::Input(0)).len(), 2);
        assert!(!graph.is_monogamous());
    }

    #[test]
    fn a_branch_nothing_reads_is_deleted_whole() {
        let (_terms, graph) = rewritten("branch { push 1 } { push 2 } drop 0");
        assert_eq!(graph.live_count(), 0);
        assert!(graph.outputs().is_empty());
    }

    #[test]
    fn the_fold_layer_is_absent_on_purpose() {
        // No literal window runs here, no operand sorts, no condition takes
        // its arm: layers 2 and 3 of the algebra sheet are untouched, so all
        // three boxes stay. The day that changes, this is what says so.
        let (_terms, graph) = rewritten("push 1 push 2 add");
        assert_eq!(graph.live_count(), 3);
        // A literal condition and a `select` that could read it, and
        // nothing does: `push true`, both arms' pushes, and the select.
        let (_terms, graph) = rewritten("push true branch { push 1 } { push 2 }");
        assert_eq!(graph.live_count(), 4, "{}", graph);
    }

    // ---- routing, the read-back's own layer ----

    #[test]
    fn a_route_is_a_copy_layer_and_then_swap_rounds() {
        let terms = &mut Context::new();
        let have = [Source::Input(0), Source::Input(1)];

        // Nothing to do at all emits nothing.
        assert!(route(terms, &have, &have).is_empty());

        // One flat product handles every multiplicity at once: drop the
        // deep slot, keep two copies of the top one.
        let steps = route(terms, &have, &[Source::Input(1), Source::Input(1)]);
        assert_eq!(steps.len(), 1);
        assert_eq!(format!("{}", terms.display(steps[0])), "drop(1) * copy(1)");

        // A pure exchange is one round of one swap.
        let steps = route(terms, &have, &[Source::Input(1), Source::Input(0)]);
        assert_eq!(steps.len(), 1);
        assert_eq!(format!("{}", terms.display(steps[0])), "swap");
    }

    // ---- the corpus ----

    #[test]
    fn the_whole_corpus_builds() {
        let (library, arena, terms) = corpus();
        assert!(terms.len() > 100, "the corpus should be a real one");
        for (idx, term) in terms {
            let graph = build(&arena, term);
            graph
                .check()
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            assert!(
                graph.is_monogamous(),
                "sentence {} built with a shared port",
                library.names[idx]
            );
            assert_eq!(
                graph.arity(),
                arena.arity(term),
                "sentence {} changed arity in the translation",
                library.names[idx]
            );
        }
    }

    /// The tightest check of [`build`] there is, and the shortest: the graph
    /// means what the term means, with nothing translated back.
    #[test]
    fn a_graph_means_what_its_term_means() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let graph = build(&arena, term);
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let (as_term, as_graph) = (
                eval_term(&mut m, &arena, term, inputs.clone()),
                eval_graph(&mut m, &graph, &inputs),
            );
            assert_eq!(
                as_term, as_graph,
                "sentence {} means something else as a graph",
                library.names[idx]
            );
        }
    }

    /// Build and read back, and ask whether the same program came out.
    ///
    /// Not that the same *term* came out — that property is gone, and was
    /// never worth much. Meaning here is the DAG a program leaves with its
    /// operations left opaque, which is a good deal weaker than what
    /// `diagram` decides and owes it nothing.
    #[test]
    fn build_and_read_back_agree() {
        let (library, mut arena, terms) = corpus();
        for (idx, term) in terms {
            let graph = build(&arena, term);
            let back = read_back(&graph, &mut arena);
            arena
                .check(back)
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            assert_eq!(
                arena.arity(back),
                arena.arity(term),
                "sentence {} changed arity through the read-back",
                library.names[idx]
            );
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let (there, and_back) = (
                eval_term(&mut m, &arena, term, inputs.clone()),
                eval_term(&mut m, &arena, back, inputs),
            );
            assert_eq!(
                there, and_back,
                "sentence {} did not read back as itself",
                library.names[idx]
            );
        }
    }

    /// The load-bearing test: the four rules are meaning-preserving, over
    /// every real program in the corpus.
    #[test]
    fn rewriting_preserves_meaning() {
        let (library, mut arena, terms) = corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            rewrite(&mut graph);
            let back = read_back(&graph, &mut arena);
            arena
                .check(back)
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            assert_eq!(
                arena.arity(back),
                arena.arity(term),
                "sentence {} changed arity through rewriting",
                library.names[idx]
            );
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let (before, after) = (
                eval_term(&mut m, &arena, term, inputs.clone()),
                eval_term(&mut m, &arena, back, inputs),
            );
            assert_eq!(
                before, after,
                "rewriting changed what sentence {} means",
                library.names[idx]
            );
        }
    }

    /// The same claim with the translation out of the loop entirely: the
    /// rules are held to the graph they act on, not to a term that came back
    /// from one.
    #[test]
    fn rewriting_preserves_meaning_in_the_graph() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let before = eval_graph(&mut m, &graph, &inputs);
            rewrite(&mut graph);
            let after = eval_graph(&mut m, &graph, &inputs);
            assert_eq!(
                before, after,
                "rewriting changed what sentence {}'s graph means",
                library.names[idx]
            );
        }
    }

    #[test]
    fn the_structural_layer_is_gone() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            rewrite(&mut graph);
            assert!(
                no_structure(&graph),
                "sentence {} kept a structural box:\n{}",
                library.names[idx],
                graph
            );
        }
    }

    /// Every link agrees at both ends after *every* firing, not only at the
    /// fixpoint — so a rule that re-points one end and forgets the other is
    /// caught where it happens.
    #[test]
    fn every_rewrite_leaves_the_links_agreeing() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            rewrite_watching(&mut graph, &mut |g| {
                g.check()
                    .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            });
        }
    }

    #[test]
    fn rewriting_is_idempotent() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            rewrite(&mut graph);
            let settled = graph.live_count();
            let mut fired = false;
            rewrite_watching(&mut graph, &mut |_| fired = true);
            assert!(
                !fired,
                "sentence {} had a rule left to fire",
                library.names[idx]
            );
            assert_eq!(graph.live_count(), settled);
        }
    }

    // ---- what comes back, on terms small enough to read ----

    #[test]
    fn what_rewriting_leaves_is_the_term_with_the_structure_gone() {
        let read = |body: &str| {
            let mut terms = Context::new();
            let term = term_of(&mut terms, body);
            let mut graph = build(&terms, term);
            rewrite(&mut graph);
            let back = read_back(&graph, &mut terms);
            format!("{}", terms.display(back))
        };

        // A permutation that cancels has nothing left to say.
        assert_eq!(read("swap swap"), "id(2)");
        // A frame taken off reads as the frame rather than as the roll
        // pair it is equal to, because the box sat where its operand
        // already was. Nothing claims that is the only right answer; it is
        // the one that stays legible.
        assert_eq!(read("dip 1 { not }"), "not * id(1)");
        // And a reach reads as the two steps it lowered to, the `id`
        // boxes between them deleted.
        assert_eq!(read("pick 1"), "copy(1) * id(1) ; id(1) * swap");
    }
}
