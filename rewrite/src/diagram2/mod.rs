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
//! and only then does anything get simplified — by rewriting, against the
//! table in [`rules`].
//!
//! A branch is not one box either, and that is the one place this is not a
//! literal reading of the term. It is **two**, with its arms as ordinary
//! boxes in between: a `fork(n)` hands each arm its own view of the stack,
//! both arms run, and the `select(n)` it is paired with keeps one of the
//! two answers. That `fork` is exactly the `(pick (n-1))^n` of the
//! single-arm hoist in [docs/totality.md](../../docs/totality.md), and the
//! hoist is why the translation is allowed: every prim is total and has no
//! effect but the stack, so work on the path not taken costs an answer
//! nobody reads rather than a failure.
//!
//! The gain is that an arm is no longer opaque — a rule reaches into one
//! from outside, and a value reaches out. The price is the fork, which is a
//! `copy` in everything but name and is a separate kind only so that
//! `copy-elim` leaves it alone. Deleting it would cost the one fact nothing
//! else records: which port is an arm's *own* view of a value. A rule that
//! holds on one side of a branch and not the other — `specialize-equal`,
//! where a value that tested `equal` to a literal is that literal in the
//! then arm — has nowhere to write its answer once both arms read the same
//! port.
//!
//! **Both ends read the condition, and both read it at port 0.** A fork
//! does not compute with it; it reads it so that a rule anchored there can
//! *name* it. That matters because a rule is a local window and the arms
//! lie between the two ends, so no window holds both: `specialize-equal`
//! has to be stated at the fork, and its left-hand side has to mention the
//! `equal` that decides the branch. Reading the condition at the same port
//! on both ends is what makes such a rule say the same thing whichever end
//! it is written at. Two readers of one port is a `copy`, which
//! [`build`] emits and `copy-elim` takes back out, so a built graph is
//! still a wiring diagram and the rewritten one still has both ends on the
//! one source.
//!
//! ## The rules
//!
//! Each one is a **pair of graphs** [`rules::sides`] builds from a payload
//! — the whole of what a rule *is* — and a rewrite is pointing at a
//! subgraph isomorphic to the first and putting the second in its place.
//! Four of them delete a box and join what it was standing between:
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
//!   the same license that lets both arms of a branch run. Its side
//!   condition is not tested but *stated*: the left side of the pair
//!   exports no port at all, so a box with a reader is not that graph.
//!
//! One does not, and it is the reason a table is worth having over a
//! `match`:
//!
//! - `dedup` — δ-naturality. Two boxes of one kind reading one set of
//!   sources are one box read twice, so `push 9 ; push 9` and `push 9 ;
//!   copy(1)` settle in the same place. It refuses a `fork`, for the reason
//!   the `fork` exists.
//!
//! What the rules leave is a DAG of `Op`s, `Call`s and `Fork`/`Select`
//! pairs whose
//! ports fan out where a `copy` used to be — the same shape `diagram`
//! arrives at by construction, reached instead by named rewrites over data
//! that existed the whole way.
//!
//! ## Nothing here spends them
//!
//! There was a `rewrite` in this module — a worklist that ran
//! [`rules::structural`] to fixpoint, and the only way a graph ever got
//! smaller. It is gone, and the rules and the laws it spent are untouched.
//! What it decided was fixed: *those* laws, in *that* order, everywhere
//! they fired, chosen here rather than by whoever is proving something. A
//! choice of laws and of where to spend them is a strategy, and strategies
//! are written in [`crate::hant`]; this is a table and the operations that
//! read it, and the driver comes back as a tactic over both.
//!
//! So a graph out of [`build`] is the literal translation and stays that
//! way until something applies a rule to it. [`rules`] is where that
//! happens: [`rules::find`] and [`rules::propose`] say where a law could
//! fire, [`rules::apply`] fires one and hands back its inverse, and
//! [`rules::replay`] runs a list of them.
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
//! **Two things are deliberately absent**, and neither is an
//! oversight:
//!
//! - **Equality.** Two graphs are never asked to be the same. `dedup`
//!   settles a great many pairs into one shape, which is not the same thing
//!   as deciding that two shapes mean one program: `push 1 ; push 2 ; add`
//!   and `push 2 ; push 1 ; add` are three boxes each and nothing here
//!   relates them. So this decides nothing, judges nothing, and is not
//!   wired into [`crate::strategy`]; `diagram` remains the prover's engine.
//!   Nor do the tests borrow its judgement: what they claim about *meaning*
//!   they claim with the `meaning` oracle, which evaluates a program with **every
//!   operation left opaque** and compares the graphs of applications that
//!   come out. `add` on two wires stays `add(x, y)` and never becomes `7`,
//!   so that oracle decides nothing either — it holds the wiring to account
//!   and stops there.
//! - **The value folds, in [`rules::structural`].** No literal window runs
//!   and no commutative operand sorts, so `push 1 ; push 2 ; add` keeps all
//!   three of its boxes however hard the wiring laws are spent. Layer 3 of
//!   the algebra sheet is [`rules::Rule::NotNot`] and nothing else, and that
//!   row is in the table but not in that list.
//!
//!   Layer 2 **is** in the table — [`rules::branching`] folds a literal
//!   condition into its arm, deletes a branch whose arms answer alike,
//!   lifts work both arms do out in front, and writes what a test decided
//!   into the block that tested it. It is not in [`rules::structural`]
//!   either, for two reasons worth keeping apart: three of those
//!   laws turn on what an operation *computes*, which the opaque oracle
//!   cannot judge and `vm` can; and the other three take a branch apart,
//!   which is a strategy, and this module decides no strategy.
//!
//!   A rule that folds a branch carries its **arms as payload**, the way
//!   the term version carried subterms, so the window holds the whole
//!   branch: `select-literal` takes the fork, both arms and the select
//!   together, and no rule leaves one end of a branch standing without the
//!   other. `rules` says which laws hold one end, which hold a whole
//!   branch, and what each can say as a result.
//!
//! [`read_back`] is the other half of the translation: a graph is scheduled
//! onto a stack, and the routing between one step and the next is *layered*
//! — one `*`-product of `copy`/`id`/`drop` to get the multiplicities right,
//! then a `*`-product of `swap`s per transposition round to get the order
//! right. A box is placed where its operands already sit rather than on
//! top, so the survivors pass either side of it and nothing is dragged up
//! and put back; `pick 1` comes back as `copy(1) * id(1) ; id(1) * swap`.
//! That is a choice about legibility and nothing more. What comes back is
//! not the term it was built from — a branch in particular reads back as
//! both arms run flat and then a branch that throws one answer away, which
//! is what the graph now says a branch is.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::fmt;

use bytecode::{Library, SentenceIndex};

use crate::term::{Arity, Context, Prim, Term, TermIndex, lower};

#[cfg(test)]
mod meaning;
pub mod query;
pub mod rules;
pub mod tactic;

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
    /// their own order — [`rules`] does, since a rule's side deletes
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
    /// is what [`rules`] keys a renaming by.
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

/// What a box is — [`Term`]'s leaves, one for one.
///
/// The two operators are what the graph replaces; everything else survives
/// the translation unchanged. `swap` in particular stays an
/// [`Op`][NodeKind::Op]: it is a prim like any other, and the rewriter is
/// where the fact that it is *structural* gets used, not the type.
///
/// `PartialEq` compares a [`BranchId`] as the number it is, which is right
/// for two boxes of one graph and wrong for two graphs — a branch id is
/// graph-local. [`rules::same_kind`](rules) is what a match needs, and it
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
    /// the same reason [`Term::Call`] carries it.
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
    /// whichever end it is anchored at, and [`read_back`] pays for it by
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
    fn empty(inputs: usize) -> Graph {
        Graph {
            nodes: Vec::new(),
            inputs: vec![Vec::new(); inputs],
            outputs: Vec::new(),
            branches: 0,
        }
    }

    /// A branch id no other pair in this graph holds.
    fn next_branch(&mut self) -> BranchId {
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

    /// A box, as [`Graph::add`], answering with the node rather than its
    /// ports — which is what a caller that has to place a box of no outputs
    /// needs.
    fn add_node(&mut self, kind: NodeKind, inputs: Vec<Source>) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).expect("a graph fits in u32"));
        self.add(kind, inputs);
        id
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
}

// ---- a term, literally ---------------------------------------------------------

/// The graph of a term: one node per leaf, nothing simplified.
///
/// Every law of the structural layer still has a spelling here, which is
/// the difference from [`crate::diagram`] and the whole premise of the
/// module — the table in [`rules`] is what spends them.
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
        // arms-in-a-box it used to be: the condition is set aside, a `fork`
        // hands each arm its own view of the stack, both arms are emitted
        // into this same graph, and the `select` it is paired with keeps one
        // of the two answers. What was a boundary is now two boxes with the
        // arms between them, so every rule reaches through it — and the one
        // fact the boundary carried, which arm a value belongs to, is still
        // written down.
        Term::Branch { if_true, if_false } => {
            let mut inputs = inputs;
            let cond = inputs.pop().expect("a branch reads its condition");
            let branch = graph.next_branch();
            // Block-wise, exactly the `(pick (n-1))^n` the hoist rule spells
            // out. Arms that take nothing have no views to tell apart, and
            // then the `select` is the only end there is to read the
            // condition.
            let (if_true_in, if_false_in, chooses) = if inputs.is_empty() {
                (Vec::new(), Vec::new(), cond)
            } else {
                // Both ends read the condition, and two readers of one port
                // is a `copy` — said outright here rather than smuggled in,
                // so a built graph is still monogamous and `copy-elim` is
                // still the one thing that breaks it.
                let views = graph.add(NodeKind::Copy(1), vec![cond]);
                let arity = inputs.len();
                let mut takes = vec![views[0]];
                takes.extend(inputs);
                let mut blocks = graph.add(NodeKind::Fork { arity, branch }, takes);
                let above = blocks.split_off(arity);
                (blocks, above, views[1])
            };
            let mut ports = vec![chooses];
            ports.extend(emit(graph, terms, *if_true, if_true_in));
            ports.extend(emit(graph, terms, *if_false, if_false_in));
            let arity = terms.arity(*if_true).outputs;
            graph.add(NodeKind::Select { arity, branch }, ports)
        }
    }
}

/// The graph as `id(k) * itself` reads: `k` fresh boundary wires passed
/// straight through beneath it.
///
/// This is the graph-side spelling of [`Context::under`], and it exists for
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

/// Opens calls in place: every [`NodeKind::Call`] — or, with `only`, every
/// call to that one sentence — replaced by the graph of its body, its
/// readers re-pointed at what the body leaves.
///
/// Definitional unfolding, not a law: this is [`build`]'s work continued —
/// the same `emit`, into a graph that already exists — and it changes what
/// is provable exactly the way the term version did, which is why it is a
/// proof step and never a rewrite the table proposes. Unlabelled, it opens
/// all the way down (recursion is forbidden, so the walk drains); labelled,
/// one pass, and the opened body's own calls stay shut.
///
/// Answers how many calls it opened — zero is the caller's business to
/// refuse.
pub fn inline(
    graph: &mut Graph,
    terms: &mut Context,
    library: &Library,
    only: Option<SentenceIndex>,
) -> Result<usize, crate::term::Error> {
    let mut opened = 0;
    loop {
        let calls: Vec<(NodeId, SentenceIndex)> = graph
            .live()
            .filter_map(|(id, kind)| match kind {
                NodeKind::Call { target, .. } if only.is_none_or(|t| t == *target) => {
                    Some((id, *target))
                }
                _ => None,
            })
            .collect();
        if calls.is_empty() {
            return Ok(opened);
        }
        for (id, target) in calls {
            let body = lower(terms, library, target)?;
            let inputs = graph.sources(id).to_vec();
            debug_assert_eq!(
                terms.arity(body),
                graph.kind(id).arity(),
                "a call carries its arity for the same reason the term does"
            );
            for (port, &src) in inputs.iter().enumerate() {
                graph.unlink(src, Sink::Port { node: id, port });
            }
            let outs = emit(graph, terms, body, inputs);
            for (port, &out) in outs.iter().enumerate() {
                let readers: Vec<Sink> = graph.sinks(Source::Port { node: id, port }).to_vec();
                for sink in readers {
                    graph.set_source(sink, out);
                    graph.sinks_mut(out).push(sink);
                }
            }
            graph.nodes[id.index()] = None;
            opened += 1;
        }
        if only.is_some() {
            return Ok(opened);
        }
    }
}

// ---- whether two graphs are one diagram ------------------------------------------

/// Whether the two graphs are the same diagram: a bijection of live boxes
/// preserving every kind (modulo a bijection of branch ids) and every link,
/// with both boundaries pinned — input `i` to input `i`, output `j` to
/// output `j`.
///
/// Whole-graph equality, not [`rules::find`]'s embedding: no window, no
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
/// Both are about legibility. This does not undo [`build`], and a branch is
/// where that shows plainest — the arms were flattened into the graph and
/// are scheduled like any other work, so what comes back runs both of them
/// and then chooses.
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
        // The two views of the stack are what a `copy` makes; the node is
        // only distinct so that rewriting leaves it alone. Its condition
        // computes nothing — it is read so that a rule can see it — so what
        // it comes back as is the condition let go of.
        NodeKind::Fork { arity, .. } => {
            let (gone, both) = (terms.drop(1), terms.copy(*arity));
            terms.par(gone, both)
        }
        // Both blocks are already on the stack by the time this runs — the
        // arms were scheduled like any other work — so the branch left to
        // write is only the choice between them: keep one block, let the
        // other go. The condition has to come up from the bottom first,
        // which is what the node's port order costs and the only place it
        // costs anything.
        NodeKind::Select { arity: n, .. } => {
            let up = hoist(terms, 2 * n + 1);
            let (keep, lose) = (terms.id(*n), terms.drop(*n));
            let if_true = terms.par(keep, lose);
            let (lose, keep) = (terms.drop(*n), terms.id(*n));
            let if_false = terms.par(lose, keep);
            let choose = terms
                .branch(if_true, if_false)
                .expect("each arm keeps one block of two");
            terms
                .compose(up, choose)
                .expect("the hoist leaves the width it was given")
        }
    }
}

/// `[a, x₁..x_k] -> [x₁..x_k, a]`: the deepest wire brought to the top, one
/// crossing at a time.
///
/// What a `select` costs at the boundary between a graph, where its
/// condition is port 0, and a term, where a `branch` reads its condition
/// off the top of the stack.
fn hoist(terms: &mut Context, width: usize) -> TermIndex {
    let mut chain: Option<TermIndex> = None;
    for below in 0..width.saturating_sub(1) {
        let swap = terms.op(Prim::Swap);
        let step = terms.under(swap, below);
        let above = width - below - 2;
        let step = if above > 0 {
            let untouched = terms.id(above);
            terms.par(step, untouched)
        } else {
            step
        };
        chain = Some(match chain {
            None => step,
            Some(acc) => terms
                .compose(acc, step)
                .expect("every crossing spans the whole stack"),
        });
    }
    chain.unwrap_or_else(|| terms.id(width))
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
    use super::meaning::{Meaning, boundary, eval_graph, eval_term};
    use super::*;
    use crate::term::lower;
    use bytecode::{Library, SentenceIndex, assemble};

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

    /// Every sentence the integration suite compiles, lowered into one
    /// arena — the same corpus `diagram`'s round trip runs on.
    pub(super) fn corpus() -> (Library, Context, Vec<(SentenceIndex, TermIndex)>) {
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
            .find(|(_, kind)| matches!(kind, NodeKind::Select { arity: 1, .. }))
            .expect("the branch ends in a select");
        // Its three inputs: the condition, which is the sentence's own
        // input and sits at port 0 the way it does on a fork, and then the
        // `then` answer and the `else` answer.
        let inputs = graph.node(id).inputs.clone();
        assert_eq!(inputs.len(), 3);
        assert_eq!(inputs[0], Source::Input(0), "the condition is port 0");
        assert!(
            matches!(
                (inputs[1], inputs[2]),
                (Source::Port { .. }, Source::Port { .. })
            ),
            "each block is an arm's answer"
        );
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

    // ---- padding, opening, and sameness ----

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

    /// A call opened in place is the body's boxes on the call's wires —
    /// the same graph building the opened term would have made.
    #[test]
    fn a_call_opens_in_place() {
        let code = r#"
            #[arity(1,1)] sentence inner { not not }
            #[arity(1,1)] sentence outer { jump crate::inner }
            sentence probe { jump crate::outer }
        "#;
        let library = assemble(code).unwrap();
        let named = |name: &str| {
            library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(idx, _)| idx)
                .unwrap()
        };
        let mut terms = Context::new();
        let term = lower(&mut terms, &library, named("probe")).unwrap();
        let mut graph = build(&terms, term);

        // A labelled inline opens that sentence and leaves what it calls
        // shut.
        let mut labelled = graph.clone();
        let opened = inline(&mut labelled, &mut terms, &library, Some(named("outer"))).unwrap();
        assert_eq!(opened, 1);
        labelled.check().unwrap();
        assert!(matches!(
            labelled.live().next().map(|(_, k)| k),
            Some(NodeKind::Call { target, .. }) if *target == named("inner")
        ));

        // Unlabelled opens all the way down, and lands on the graph the
        // opened term builds.
        let opened = inline(&mut graph, &mut terms, &library, None).unwrap();
        assert_eq!(opened, 2);
        graph.check().unwrap();
        let (_t, flat) = built("not not");
        assert!(isomorphic(&graph, &flat), "\n{}\n{}", graph, flat);
        assert_eq!(inline(&mut graph, &mut terms, &library, None).unwrap(), 0);
    }
}
