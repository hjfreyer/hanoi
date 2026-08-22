//! The table: each law a pair of graphs the module says are the same
//! program, and a rewrite the business of pointing at one and swapping in
//! the other.
//!
//! [`super`] builds a graph and shrinks it, and until now it shrank it by
//! hand — a `match` on [`NodeKind`] that re-pointed ports directly. That
//! works and says nothing: there is no page to read, and no way to add a
//! law without editing the engine. This module is the thing
//! `rewrite/src/rules.rs` was for terms, over graphs instead.
//!
//! ## A rule states its equation; the checker only compares
//!
//! A [`Law`] names one row of the table with its blanks open. A [`Rule`] is
//! that row filled in, and it carries enough to build **both** sides:
//! [`sides`] reads the payload, tests nothing, and takes no graph apart. The
//! two sides are ordinary [`Graph`]s of one interface — the same boundary
//! widths — so a rule is literally *a pair of axiomatically equivalent open
//! graphs*, and a rewrite is finding one of them and putting the other in
//! its place.
//!
//! What a term version could do in one line — build both sides and compare
//! — a graph version cannot: a subterm is named by a path, and a subgraph is
//! named by an **embedding**. So [`Match`] is that embedding written down,
//! and [`apply`] *verifies* it rather than searching for it: every check is
//! local, reads one port at a time, and takes no decisions.
//!
//! Side conditions are not checked, they are **carried by the interface**.
//! `dead-node` is the clearest case: its left side is one box with **no
//! boundary outputs**, so the fullness condition below forces every port of
//! the box it matches to have no reader at all. Nothing asks "is this dead";
//! a match that is not one fails to be a match. `not-not` is the same trick
//! one step along — its middle port is not exported, so the rule cannot fire
//! where something else reads the first `not`.
//!
//! ## Which laws are here
//!
//! Four are the eliminations `super` used to hardcode, restated:
//! [`Law::IdElim`], [`Law::SwapElim`], [`Law::CopyElim`] and
//! [`Law::DeadNode`] (which is `drop-elim` too — a `drop(n)` has no outputs,
//! so it is always dead). Layer 1 of
//! [docs/algebra.md](../../../docs/algebra.md) has no other spelling here:
//! the associativities, the units, the interchange and Yang–Baxter are all
//! *representation*, true of the wiring because the wiring cannot say them.
//!
//! Two are new, and they are why a table is worth having:
//!
//! - [`Law::Dedup`] — δ-naturality, which `super` used to list among the
//!   things it had not bought. Two boxes of one kind reading one set of
//!   sources are one box read twice. It refuses [`NodeKind::Fork`] and
//!   [`NodeKind::Select`]: a fork *is* a copy, and merging two of them would
//!   destroy the one fact it exists to record.
//! - [`Law::NotNot`] — `not ; not = as_bool`, a layer-3 law carried as the
//!   template for the rest. It is in the table and **not** in
//!   [`structural`], because the opaque-operation oracle the tests judge by
//!   reads `not(not(x))` and `as_bool(x)` as different symbols — this law is
//!   about what the machine computes, and `vm` is what measures it.
//!
//! ## The branch layer, and the one place it stops
//!
//! [`branching`] is layer 2 of the sheet: [`Law::ForkDedup`],
//! [`Law::SelectView`], [`Law::SelectSame`], [`Law::SelectLiteral`],
//! [`Law::SpecializeEqual`] and [`Law::SpecializeBool`]. Between them they
//! fold a literal condition into its arm, delete a branch whose arms answer
//! alike, lift work both arms do out in front, and write what a test decided
//! into the block that tested it. `branch { A } { A } = drop-top ; A` is not
//! among them and does not need to be: it is `fork-dedup`, then
//! `select-same`, then `dead-node`.
//!
//! ### One end, or the whole branch
//!
//! A rule is a local window, and a branch's arms lie *between* its two ends.
//! So a window holds one end — or it holds **everything**, arms included.
//! Both shapes are here, and the difference is what each can say.
//!
//! Four of the laws hold one end. That is enough to talk about the
//! condition, which is why it sits at port 0 of both ends, and it is what
//! [`Law::SelectView`] keeps from being inert: everything an arm passes
//! through arrives at a select from behind the fork, so a block is a *view*
//! and not a value until that rule pulls it out.
//!
//! But one end cannot see the **discard** — the fact that the select throws
//! the untaken block away. So a one-ended rule may not reason from "the
//! condition holds": a fork's views are plain copies, and a then-view *is*
//! `x` whatever the condition says. That is why [`Law::SpecializeEqual`] and
//! [`Law::SpecializeBool`] are stated at the select, and why they reach a
//! block and not the inside of an arm.
//!
//! [`Law::SelectLiteral`] holds the whole branch, and it does so by carrying
//! the arms as **payload** — the way the term version carried subterms. That
//! costs the table nothing, since [`sides`] implants them, and it buys two
//! things. The two ends always go together, so no rule leaves a fork holding
//! views that no select pairs with. And the discard is *inside the window*,
//! which is exactly what a rule reasoning from the condition needs.
//!
//! So the boundary is not where a first reading suggests. Arm-local
//! specialization is not beyond this representation; it is beyond a
//! **one-ended** rule. Stated whole — the fork, the arms, the select, with
//! the arms carried — `x` tested `equal` to `7` could become `7` inside the
//! then arm, and the pair would be an honest equality: the two sides differ
//! only where the select discards the difference. The specializing rules
//! have not been rewritten that way yet, and that is the next thing to do,
//! not a thing that cannot be done.
//!
//! ## Where the trust sits
//!
//! [`sides`] and [`apply`] are the whole of it: one builds the table, the
//! other holds a claimed embedding to agreeing at every port and then
//! re-points. [`find`] and [`propose`] are search, they are wrong the way a
//! bad guess is wrong, and every answer they give goes through `apply`
//! anyway.
//!
//! [`find`] is partial, in the two places a pattern does not pin its own
//! match: a pattern with **no boxes** has nothing to anchor on (which is
//! every rule's right-hand side but `not-not`'s), and a pattern that exports
//! **one port twice** leaves the split of that port's readers a choice
//! rather than a reading. Those are decisions, and they belong to whatever
//! writes a derivation — which is exactly why [`Match`] carries the split
//! rather than deriving it.

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::{BranchId, Graph, NodeId, NodeKind, Sink, Source};
use bytecode::Value;

use crate::term::{Arity, Prim};

// ---- the laws --------------------------------------------------------------------

/// Which equation, with its blanks still open.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Law {
    IdElim,
    SwapElim,
    CopyElim,
    DeadNode,
    Dedup,
    NotNot,
    // The branch layer. Every one of these is stated at an end of a branch
    // that has the condition in its own window — see the module docs for why
    // that is the only place some of them can be stated soundly at all.
    ForkDedup,
    SelectView,
    SelectSame,
    SelectLiteral,
    SpecializeEqual,
    SpecializeBool,
}

/// Which operand of a two-input box a payload means.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    /// Input 0, the deeper one.
    Deep,
    /// Input 1.
    Top,
}

/// One equation, stated outright: a pair of graphs, built from the payload
/// and nothing else.
///
/// Widths a payload determines are not carried — `DeadNode { kind }` reads
/// its boundary width off the kind's own arity, because carrying it as well
/// would let a rule state a pair whose two halves disagree.
#[derive(Debug, Clone, PartialEq)]
pub enum Rule {
    /// `id(n)` is a wire: its readers read what it read.
    IdElim { n: usize },
    /// A crossing is not recorded — the two lines cross by being re-pointed.
    SwapElim,
    /// `copy(n)` is a port read twice. The one rule that grows the readers
    /// of a port rather than shrinking the graph, and where the cartesian
    /// structure enters.
    CopyElim { n: usize },
    /// ε-naturality: a box nothing reads, and its input links, gone. The
    /// language is total and pure, which is what licenses it.
    DeadNode { kind: NodeKind },
    /// δ-naturality: two boxes of one kind on one set of sources are one box
    /// read twice.
    Dedup { kind: NodeKind },
    /// `not ; not = as_bool` — the coercion spelled the long way round.
    NotNot,

    // ---- the branch layer ----
    /// The same operation done in both arms is one operation, done before
    /// the fork. δ-naturality again, this time seeing through a `fork`: the
    /// views are copies, so the two boxes were always computing the one
    /// thing.
    ///
    /// `ports[i]` is the fork input whose view the box's input `i` reads.
    ForkDedup {
        arity: usize,
        kind: NodeKind,
        ports: Vec<usize>,
    },
    /// A `select` block that is one of the views a `fork` handed out is the
    /// value the fork was handed. The views are copies, so this is the
    /// plainest wiring fact there is.
    ///
    /// It is also what makes the rest of this layer reach anything.
    /// Everything an arm passes through arrives at the select **from behind
    /// the fork**, so a rule that wants to say something about a block —
    /// [`Rule::SelectSame`], and both of the specializing rules — finds a
    /// view sitting there rather than the value. This pulls the value out.
    ///
    /// Every block that comes from the fork moves at once, and it has to:
    /// a window holding the fork cannot leave a *second* block reading it
    /// from outside, or what the match points at is the pattern plus a
    /// link. The symmetric case — one wire through both arms — is the
    /// common one, so this takes a list.
    ///
    /// `views[i]` is `(block, port)`: the select's block, counted over the
    /// whole `2n` with the then side first, and the fork's output port,
    /// counted over the whole `2f` the same way.
    SelectView {
        fork: usize,
        arity: usize,
        views: Vec<(usize, usize)>,
    },
    /// A block a `select` answers with either way is what it answers: `if c
    /// then x else x = x`. The select keeps its other blocks and narrows by
    /// one.
    SelectSame { arity: usize, at: usize },
    /// β: a literal condition keeps its arm, and the whole branch goes with
    /// it — fork, both arms, select. Sound on **every** value and not only
    /// on booleans, because `truthy` is total: `false` is the one falsy
    /// value and everything else takes the then block.
    ///
    /// The arms are **payload**, the way the term version carried subterms,
    /// and that is what makes the window whole. A rule holding only the
    /// select could fold the condition but not take the fork with it, and
    /// would leave one end of a branch standing without the other. Carrying
    /// the arms costs the table nothing — [`sides`] implants them — and buys
    /// the two ends always going together.
    ///
    /// It also puts the **discard inside the window**, which is what a rule
    /// reasoning from "the condition holds" needs and cannot get at either
    /// end alone.
    ///
    /// Each arm takes its side's views first, then whatever it reads from
    /// outside the branch, and leaves the blocks the select chooses between.
    /// `fork` is `None` when the arms take nothing and there is no fork.
    SelectLiteral {
        value: Value,
        fork: Option<usize>,
        then_arm: Graph,
        else_arm: Graph,
    },
    /// A value that tested `equal` to a literal **is** that literal, in the
    /// block the test chose. `equal` answers `Bool(a == b)`, so a truthy
    /// answer is `a == b` and nothing weaker.
    SpecializeEqual {
        arity: usize,
        at: usize,
        value: Value,
        literal: Side,
    },
    /// `as_bool` of the very value a branch tested is what the branch
    /// decided: `true` in the then block, `false` in the else block.
    /// `as_bool` *is* `truthy` made into an instruction, and the else block
    /// is reached only by the one falsy value, so both halves are exact.
    ///
    /// The **fork is in the window**, and it has to be. An arm never sees
    /// the condition directly — it sees whatever the fork handed it — so
    /// the rule can only say "this is the condition" by holding the fork
    /// and pointing at a stack slot the condition was copied into. That is
    /// what `port` names, and requiring it to be the condition's own source
    /// is the whole of the side condition.
    ///
    /// `view` is the fork output the `as_bool` reads and `at` the select's
    /// block, each counted over the whole of `2f` and `2n`; `at < arity` is
    /// the then side, and so decides which literal this folds to.
    SpecializeBool {
        fork: usize,
        arity: usize,
        view: usize,
        at: usize,
    },
}

impl Rule {
    /// Which row of the table this is an instance of.
    pub fn law(&self) -> Law {
        match self {
            Rule::IdElim { .. } => Law::IdElim,
            Rule::SwapElim => Law::SwapElim,
            Rule::CopyElim { .. } => Law::CopyElim,
            Rule::DeadNode { .. } => Law::DeadNode,
            Rule::Dedup { .. } => Law::Dedup,
            Rule::NotNot => Law::NotNot,
            Rule::ForkDedup { .. } => Law::ForkDedup,
            Rule::SelectView { .. } => Law::SelectView,
            Rule::SelectSame { .. } => Law::SelectSame,
            Rule::SelectLiteral { .. } => Law::SelectLiteral,
            Rule::SpecializeEqual { .. } => Law::SpecializeEqual,
            Rule::SpecializeBool { .. } => Law::SpecializeBool,
        }
    }
}

/// The laws a rewrite to fixpoint spends: everything true of the wiring
/// alone, which is layer 1 of the algebra sheet and nothing else.
///
/// `DeadNode` leads because it is the cheapest test and because a dead box
/// should go before anything bothers looking inside it.
pub fn structural() -> Vec<Law> {
    vec![
        Law::DeadNode,
        Law::IdElim,
        Law::SwapElim,
        Law::CopyElim,
        Law::Dedup,
    ]
}

/// The branch layer: the laws stated at one end of a branch or the other.
///
/// **Not** what [`super::rewrite`] spends, for the reason [`Law::NotNot`] is
/// not either. Three of these turn on what an operation *computes* — which
/// values are truthy, that `equal` is identity, that `as_bool` is `truthy` —
/// and the oracle the corpus tests judge by reads every operation as opaque,
/// so it cannot tell a graph that spent one of them from a graph that means
/// something else. `vm` is the judge for those, and the tests call it.
///
/// The other three are pure wiring and the oracle can judge them; they are
/// here rather than in [`structural`] because they take a branch apart, and
/// a rewriter that dissolves every branch it can is a strategy, which this
/// module does not decide.
///
/// The order matters for what a run finds: [`Law::SelectView`] is what pulls
/// a block out from behind a fork, and until it has, none of the others has
/// anything to match.
pub fn branching() -> Vec<Law> {
    vec![
        Law::SelectLiteral,
        Law::SelectView,
        Law::SelectSame,
        Law::ForkDedup,
        Law::SpecializeEqual,
        Law::SpecializeBool,
    ]
}

/// Whether a law can be judged by reading every operation as opaque.
///
/// The wiring laws can: they move boxes around without asking what any box
/// does. The rest are claims about the machine, and only the machine settles
/// them — which is why they are tested against `vm` and not against the
/// corpus oracle.
pub fn is_wiring(law: Law) -> bool {
    !matches!(
        law,
        Law::NotNot | Law::SelectLiteral | Law::SpecializeEqual | Law::SpecializeBool
    )
}

/// Which side of a rule's equation to match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Match the left-hand side, leave the right.
    Forward,
    /// Match the right-hand side, leave the left.
    Backward,
}

impl Direction {
    fn flipped(self) -> Direction {
        match self {
            Direction::Forward => Direction::Backward,
            Direction::Backward => Direction::Forward,
        }
    }
}

// ---- where a step lands ----------------------------------------------------------

/// A subgraph, pointed at: the claim that this part of a host graph *is* one
/// side of a rule.
///
/// Not a path. A term's subterm has a name in the term; a graph's subgraph
/// has none, so the embedding itself is the name — which box is which, what
/// the pattern's boundary stands for outside, and who reads what it leaves.
///
/// [`outputs`](Match::outputs) is the one field that is a **choice** rather
/// than a reading. When two of a pattern's boundary outputs name one port,
/// nothing in the host says which of that port's outside readers belong to
/// which; the split is the matcher's business, and [`apply`] only holds it
/// to being consistent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    /// Image of the pattern's boxes, indexed by the pattern's own node
    /// index. A rule's side deletes nothing, so those indices are dense.
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

/// One rewrite: an equation, which way round, and where.
#[derive(Debug, Clone, PartialEq)]
pub struct Step {
    pub rule: Rule,
    pub dir: Direction,
    pub at: Match,
}

// ---- what can go wrong -----------------------------------------------------------

/// Why a payload states no equation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ill {
    /// The law refuses this payload outright.
    Refused,
    /// The two sides do not take and leave the same thing, so no rewrite by
    /// them could keep a graph's arity.
    Interface(Arity, Arity),
    /// A side of the rule is not a graph. A rule that cannot be built cannot
    /// be applied.
    Broken(super::Error),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The payload does not state an equation.
    Ill { law: Law, why: Ill },
    /// The subgraph the match points at is not the side of the equation the
    /// step says it is. This is the only way a step can be wrong.
    NotThere {
        law: Law,
        dir: Direction,
        at: Mismatch,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Ill { law, why } => match why {
                Ill::Refused => write!(f, "{:?} refuses that payload", law),
                Ill::Interface(l, r) => write!(
                    f,
                    "{:?} relates a {} graph and a {} one, which is no equation",
                    law, l, r
                ),
                Ill::Broken(e) => write!(f, "{:?} builds a side that is not a graph: {}", law, e),
            },
            Error::NotThere { law, dir, at } => {
                let side = match dir {
                    Direction::Forward => "left",
                    Direction::Backward => "right",
                };
                match at {
                    Mismatch::Shape => {
                        write!(f, "the match is not the shape of {:?}'s {} side", law, side)
                    }
                    Mismatch::Gone(node) => {
                        write!(f, "the match names {}, which is not there", node)
                    }
                    Mismatch::Kind(node) => write!(
                        f,
                        "{} is not the box {:?}'s {} side has in its place",
                        node, law, side
                    ),
                    Mismatch::Edge(sink) => {
                        write!(
                            f,
                            "{} reads something {:?} does not say it reads",
                            sink, law
                        )
                    }
                    Mismatch::Readers(src) => {
                        write!(
                            f,
                            "the readers of {} are not the ones the match claims",
                            src
                        )
                    }
                    Mismatch::Induced(src) => write!(
                        f,
                        "{} is inside the match, so what it points at is {:?} plus a link",
                        src, law
                    ),
                }
            }
        }
    }
}

impl std::error::Error for Error {}

// ---- the table, as construction --------------------------------------------------

/// The two graphs a rule says are the same program, built from its payload
/// alone.
///
/// This is the table. It reads no graph it was not handed, tests nothing,
/// and decides nothing: a payload that states no equation comes back as
/// [`Error::Ill`] rather than as a silently wrong pair.
///
/// The two sides share a branch-id namespace — a [`BranchId`] means the same
/// branch on both — which is what lets a rule keep a branch across a
/// rewrite rather than only make or delete one.
pub fn sides(rule: &Rule) -> Result<(Graph, Graph), Error> {
    let law = rule.law();
    let ill = |why| Error::Ill { law, why };
    let (a, b) = match rule {
        Rule::IdElim { n } => {
            let n = *n;
            (
                one_box(NodeKind::Id(n)),
                wires(n, (0..n).map(Source::Input).collect()),
            )
        }
        Rule::SwapElim => (
            one_box(NodeKind::Op(Prim::Swap)),
            // Output 0 is what came in on top, which is what a crossing is.
            wires(2, vec![Source::Input(1), Source::Input(0)]),
        ),
        Rule::CopyElim { n } => {
            let n = *n;
            // Block-wise, as the box is: output `i` and output `n + i` both
            // stand for input `i`, so the right side names one source twice.
            let both = (0..n).chain(0..n).map(Source::Input).collect();
            (one_box(NodeKind::Copy(n)), wires(n, both))
        }
        Rule::DeadNode { kind } => {
            let inputs = kind.arity().inputs;
            (dead_box(kind.clone()), wires(inputs, Vec::new()))
        }
        Rule::Dedup { kind } => {
            // A fork is a copy in everything but name, and the name is the
            // point: merging two of them loses which port is an arm's own
            // view of a value. A select carries the other end of the same
            // fact.
            if matches!(kind, NodeKind::Fork { .. } | NodeKind::Select { .. }) {
                return Err(ill(Ill::Refused));
            }
            let arity = kind.arity();
            let ins: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();

            let mut twice = Graph::empty(arity.inputs);
            let mut ports = twice.add(kind.clone(), ins.clone());
            ports.extend(twice.add(kind.clone(), ins.clone()));
            twice.close(ports);

            let mut once = Graph::empty(arity.inputs);
            let ports = once.add(kind.clone(), ins);
            let mut both = ports.clone();
            both.extend(ports);
            once.close(both);

            (twice, once)
        }
        Rule::NotNot => {
            let mut long = Graph::empty(1);
            let first = long.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
            // The middle port is not exported, which is the side condition:
            // a `not` something else reads is not this window.
            let second = long.add(NodeKind::Op(Prim::Not), first);
            long.close(second);

            let mut short = Graph::empty(1);
            let coerced = short.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)]);
            short.close(coerced);

            (long, short)
        }

        // ---- the branch layer ----
        Rule::ForkDedup { arity, kind, ports } => {
            let n = *arity;
            // A fork is a copy of the two kinds this refuses, and merging two
            // of *those* is what `dedup` refuses, for the same reason. A box
            // that reads none of the views is not about this fork at all, and
            // merging it is plain `dedup`.
            if matches!(kind, NodeKind::Fork { .. } | NodeKind::Select { .. })
                || ports.is_empty()
                || ports.len() != kind.arity().inputs
                || ports.iter().any(|&p| p >= n)
            {
                return Err(ill(Ill::Refused));
            }
            let handed: Vec<Source> = (0..=n).map(Source::Input).collect();

            let mut apart = Graph::empty(n + 1);
            let branch = apart.next_branch();
            let views = apart.add(NodeKind::Fork { arity: n, branch }, handed.clone());
            let this: Vec<Source> = ports.iter().map(|&p| views[p]).collect();
            let that: Vec<Source> = ports.iter().map(|&p| views[n + p]).collect();
            let mut out = views.clone();
            out.extend(apart.add(kind.clone(), this));
            out.extend(apart.add(kind.clone(), that));
            apart.close(out);

            let mut once = Graph::empty(n + 1);
            let branch = once.next_branch();
            let views = once.add(NodeKind::Fork { arity: n, branch }, handed);
            let ahead: Vec<Source> = ports.iter().map(|&p| Source::Input(1 + p)).collect();
            let shared = once.add(kind.clone(), ahead);
            let mut out = views;
            out.extend(shared.iter().copied());
            out.extend(shared);
            once.close(out);

            (apart, once)
        }
        Rule::SelectView { fork, arity, views } => {
            let (f, n) = (*fork, *arity);
            let mut named: Vec<usize> = views.iter().map(|&(at, _)| at).collect();
            named.sort_unstable();
            named.dedup();
            if f == 0
                || views.is_empty()
                || named.len() != views.len()
                || views.iter().any(|&(at, v)| at >= 2 * n || v >= 2 * f)
            {
                return Err(ill(Ill::Refused));
            }
            // The condition, the fork's stack, and every block the fork does
            // *not* supply.
            let width = 1 + f + 2 * n - views.len();
            let from_boundary: Vec<usize> = (0..2 * n).filter(|b| !named.contains(b)).collect();
            let supplied = |b: usize| {
                views
                    .iter()
                    .find(|&&(at, _)| at == b)
                    .map(|&(_, v)| v)
                    // The fork input the view stands for: output `i` and
                    // output `f + i` are both the value handed in at `1 + i`.
                    .ok_or_else(|| {
                        let slot = from_boundary
                            .iter()
                            .position(|&o| o == b)
                            .expect("one or other");
                        Source::Input(1 + f + slot)
                    })
            };

            let build = |through: bool| {
                let mut g = Graph::empty(width);
                let branch = g.next_branch();
                let handed: Vec<Source> = (0..=f).map(Source::Input).collect();
                let ports = g.add(NodeKind::Fork { arity: f, branch }, handed);
                let mut takes = vec![Source::Input(0)];
                takes.extend((0..2 * n).map(|b| match supplied(b) {
                    Err(outside) => outside,
                    Ok(v) if through => Source::Input(1 + v % f),
                    Ok(v) => ports[v],
                }));
                let answers = g.add(NodeKind::Select { arity: n, branch }, takes);
                let mut out = ports;
                out.extend(answers);
                g.close(out);
                g
            };
            (build(false), build(true))
        }
        Rule::SelectSame { arity, at } => {
            let (n, j) = (*arity, *at);
            if j >= n {
                return Err(ill(Ill::Refused));
            }
            // `2n` boundary inputs, not `2n + 1`: the block both sides answer
            // with is **one** input, read twice, and it has to be one in the
            // pattern itself. A match that merely pointed two of the pattern's
            // inputs at one host source would be matching a graph that does
            // not state the equation.
            let shared = Source::Input(1 + j);
            let then = |i: usize| Source::Input(1 + i);
            let els = |i: usize| {
                if i == j {
                    shared
                } else {
                    Source::Input(n + 1 + if i < j { i } else { i - 1 })
                }
            };

            let mut both = Graph::empty(2 * n);
            let branch = both.next_branch();
            let mut takes = vec![Source::Input(0)];
            takes.extend((0..n).map(then));
            takes.extend((0..n).map(els));
            let answers = both.add(NodeKind::Select { arity: n, branch }, takes);
            both.close(answers);

            let mut fewer = Graph::empty(2 * n);
            let branch = fewer.next_branch();
            let mut takes = vec![Source::Input(0)];
            takes.extend((0..n).filter(|&i| i != j).map(then));
            takes.extend((0..n).filter(|&i| i != j).map(els));
            let kept = fewer.add(
                NodeKind::Select {
                    arity: n - 1,
                    branch,
                },
                takes,
            );
            let mut answers = Vec::with_capacity(n);
            let mut next = 0;
            for i in 0..n {
                if i == j {
                    answers.push(shared);
                } else {
                    answers.push(kept[next]);
                    next += 1;
                }
            }
            fewer.close(answers);

            (both, fewer)
        }
        Rule::SelectLiteral {
            value,
            fork,
            then_arm,
            else_arm,
        } => {
            let f = fork.unwrap_or(0);
            let n = then_arm.arity().outputs;
            if else_arm.arity().outputs != n
                || then_arm.arity().inputs < f
                || else_arm.arity().inputs < f
            {
                return Err(ill(Ill::Refused));
            }
            for side in [then_arm, else_arm] {
                side.check().map_err(|e| ill(Ill::Broken(e)))?;
            }
            // What each arm reads from outside the branch, beyond its views.
            let (t_extra, e_extra) = (then_arm.arity().inputs - f, else_arm.arity().inputs - f);
            let width = f + t_extra + e_extra;
            let outside = |at: usize, count: usize| (0..count).map(move |i| Source::Input(at + i));

            let mut whole = Graph::empty(width);
            let lit = whole.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
            let branch = whole.next_branch();
            let views = match fork {
                Some(wide) => {
                    let mut handed = vec![lit[0]];
                    handed.extend(outside(0, *wide));
                    whole.add(
                        NodeKind::Fork {
                            arity: *wide,
                            branch,
                        },
                        handed,
                    )
                }
                None => Vec::new(),
            };
            let mut takes = views[..f].to_vec();
            takes.extend(outside(f, t_extra));
            let this = implant(&mut whole, then_arm, &takes);
            let mut takes = views[f..].to_vec();
            takes.extend(outside(f + t_extra, e_extra));
            let that = implant(&mut whole, else_arm, &takes);
            let mut chooses = vec![lit[0]];
            chooses.extend(this);
            chooses.extend(that);
            let mut answers = whole.add(NodeKind::Select { arity: n, branch }, chooses);
            // The literal is exported, so the rule does not also demand that
            // nothing else reads it.
            answers.push(lit[0]);
            whole.close(answers);

            // The arm the literal keeps, on the values the fork was handed —
            // the views were copies of those, so it reads them straight.
            let taken = value.truthy();
            let (arm, at) = if taken {
                (then_arm, f)
            } else {
                (else_arm, f + t_extra)
            };
            let mut kept = Graph::empty(width);
            let lit = kept.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
            // A branch id means the same branch on both sides, so the ids
            // this side does not use are skipped over rather than reused.
            let skip = if taken { 1 } else { 1 + then_arm.branches };
            for _ in 0..skip {
                kept.next_branch();
            }
            let mut takes: Vec<Source> = outside(0, f).collect();
            takes.extend(outside(at, arm.arity().inputs - f));
            let mut answers = implant(&mut kept, arm, &takes);
            answers.push(lit[0]);
            kept.close(answers);

            (whole, kept)
        }
        Rule::SpecializeEqual {
            arity,
            at,
            value,
            literal,
        } => {
            let (n, j) = (*arity, *at);
            if j >= n {
                return Err(ill(Ill::Refused));
            }
            // Input 0 is the value under test, and it is *also* the then block
            // at `j` — said once in the pattern, for the reason `select-same`
            // says its shared block once.
            let x = Source::Input(0);
            let then = |i: usize| {
                if i == j {
                    x
                } else {
                    Source::Input(1 + if i < j { i } else { i - 1 })
                }
            };
            let els = |i: usize| Source::Input(n + i);
            let operands = |lit: Source| match literal {
                Side::Deep => vec![lit, x],
                Side::Top => vec![x, lit],
            };

            let build = |folded: bool| {
                let mut g = Graph::empty(2 * n);
                let lit = g.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
                let test = g.add(NodeKind::Op(Prim::Equal), operands(lit[0]));
                let branch = g.next_branch();
                let mut takes = vec![test[0]];
                takes.extend((0..n).map(|i| if folded && i == j { lit[0] } else { then(i) }));
                takes.extend((0..n).map(els));
                let mut answers = g.add(NodeKind::Select { arity: n, branch }, takes);
                // Both the test and the literal stay readable from outside.
                answers.push(test[0]);
                answers.push(lit[0]);
                g.close(answers);
                g
            };
            (build(false), build(true))
        }
        Rule::SpecializeBool {
            fork,
            arity,
            view,
            at,
        } => {
            let (f, n, v, b) = (*fork, *arity, *view, *at);
            if f == 0 || v >= 2 * f || b >= 2 * n {
                return Err(ill(Ill::Refused));
            }
            // The block is on the then side exactly when it is in the first
            // half, and that is what the branch decided about the condition.
            let decided = Value::Bool(b < n);
            // Boundary input 0 is the condition, and it is *also* the fork's
            // stack slot `v % f` — which is the side condition, said in the
            // pattern rather than tested.
            let slot = v % f;
            let stack = |i: usize| {
                if i == slot {
                    Source::Input(0)
                } else {
                    Source::Input(1 + if i < slot { i } else { i - 1 })
                }
            };
            let block = |other: usize| Source::Input(f + if other < b { other } else { other - 1 });
            let width = f + 2 * n - 1;

            let build = |folded: bool| {
                let mut g = Graph::empty(width);
                let branch = g.next_branch();
                let mut handed = vec![Source::Input(0)];
                handed.extend((0..f).map(stack));
                let ports = g.add(NodeKind::Fork { arity: f, branch }, handed);
                let coerced = g.add(NodeKind::Op(Prim::AsBool), vec![ports[v]]);
                let known = if folded {
                    g.add(NodeKind::Op(Prim::Push(decided.clone())), Vec::new())[0]
                } else {
                    coerced[0]
                };
                let mut takes = vec![Source::Input(0)];
                takes.extend((0..2 * n).map(|other| if other == b { known } else { block(other) }));
                let answers = g.add(NodeKind::Select { arity: n, branch }, takes);
                let mut out = ports;
                // The coercion stays readable from outside.
                out.push(coerced[0]);
                out.extend(answers);
                g.close(out);
                g
            };
            (build(false), build(true))
        }
    };
    if a.arity() != b.arity() {
        return Err(ill(Ill::Interface(a.arity(), b.arity())));
    }
    a.check().map_err(|e| ill(Ill::Broken(e)))?;
    b.check().map_err(|e| ill(Ill::Broken(e)))?;
    Ok((a, b))
}

/// One box, its inputs the boundary's and every output port exported in
/// order: the window one node fills.
fn one_box(kind: NodeKind) -> Graph {
    let arity = kind.arity();
    let mut g = Graph::empty(arity.inputs);
    let kind = refresh(&mut g, kind);
    let ports = g.add(kind, (0..arity.inputs).map(Source::Input).collect());
    g.close(ports);
    g
}

/// The same box with **nothing exported**, which is how "nothing reads this"
/// is said as an interface rather than as a test.
fn dead_box(kind: NodeKind) -> Graph {
    let arity = kind.arity();
    let mut g = Graph::empty(arity.inputs);
    let kind = refresh(&mut g, kind);
    g.add(kind, (0..arity.inputs).map(Source::Input).collect());
    g.close(Vec::new());
    g
}

/// No boxes at all: `n` inputs, and outputs that name them.
fn wires(inputs: usize, outputs: Vec<Source>) -> Graph {
    let mut g = Graph::empty(inputs);
    g.close(outputs);
    g
}

/// One graph's boxes added to another, its boundary inputs standing for the
/// sources given, answering with the sources its boundary outputs name.
///
/// This is what lets an **arm** be a payload rather than part of a fixed
/// pattern. A rule about a whole branch cannot spell its arms out — they are
/// whatever the program put there — so it carries them, exactly as the term
/// version carried subterms, and [`sides`] implants them between the two
/// ends.
fn implant(into: &mut Graph, arm: &Graph, inputs: &[Source]) -> Vec<Source> {
    debug_assert_eq!(inputs.len(), arm.inputs.len(), "one source per input");
    let base = into.branches;
    let mut fresh: Vec<NodeId> = Vec::with_capacity(arm.nodes.len());
    let carry = |src: Source, fresh: &[NodeId]| match src {
        Source::Input(i) => inputs[i],
        Source::Port { node, port } => Source::Port {
            node: fresh[node.index()],
            port,
        },
    };
    for slot in &arm.nodes {
        let node = slot.as_ref().expect("an arm keeps every box it builds");
        let takes = node.inputs.iter().map(|&s| carry(s, &fresh)).collect();
        fresh.push(into.add_node(lift(&node.kind, base), takes));
    }
    into.branches += arm.branches;
    arm.outputs.iter().map(|&s| carry(s, &fresh)).collect()
}

/// An arm's own branch ids, moved clear of the ones its host has already
/// handed out.
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

/// A branch id off a host graph means nothing in a rule, so a rule's side
/// mints its own; [`Match::branches`] is what carries the correspondence
/// back.
fn refresh(g: &mut Graph, kind: NodeKind) -> NodeKind {
    match kind {
        NodeKind::Fork { arity, .. } => NodeKind::Fork {
            arity,
            branch: g.next_branch(),
        },
        NodeKind::Select { arity, .. } => NodeKind::Select {
            arity,
            branch: g.next_branch(),
        },
        other => other,
    }
}

// ---- applying a step -------------------------------------------------------------

/// One rewrite, and the step that undoes it.
///
/// The whole of the checking is here, and none of it searches: build both
/// sides, hold the match to being an isomorphism onto an induced subgraph,
/// then delete that subgraph and put the other side in its place.
///
/// The answer is the **inverse step**. This is the one place a graph cannot
/// copy the term version: a path survived a rewrite unchanged, but a
/// [`Match`] names host [`NodeId`]s and the replacement's boxes are freshly
/// allocated, so the way back has to be handed over rather than derived by
/// flipping a bit.
pub fn apply(graph: &mut Graph, step: &Step) -> Result<Step, Error> {
    let (lhs, rhs) = sides(&step.rule)?;
    let (pattern, replacement) = match step.dir {
        Direction::Forward => (&lhs, &rhs),
        Direction::Backward => (&rhs, &lhs),
    };
    check_match(graph, pattern, &step.at).map_err(|at| Error::NotThere {
        law: step.rule.law(),
        dir: step.dir,
        at,
    })?;
    let back = splice(graph, replacement, &step.at);
    Ok(Step {
        rule: step.rule.clone(),
        dir: step.dir.flipped(),
        at: back,
    })
}

/// A run of the table: every step, paired with the step that undoes it.
///
/// The pairing is what a graph needs and a term did not. A term's step was
/// undone by flipping a bit, because a `Path` named the same place before
/// the rewrite and after. Undoing a graph's step puts boxes **back**, and a
/// box put back is a new box with a new [`NodeId`] — so the undo before it
/// has to say which ids it handed out, and everything still to be undone
/// has to be said again in those terms. A derivation is where both halves
/// are written down so [`Derivation::undo`] can rebase as it walks.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Derivation {
    /// Each step and the one that reverses it, in the order they landed.
    steps: Vec<(Step, Step)>,
}

impl Derivation {
    /// How many rewrites.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The steps as they were taken.
    pub fn steps(&self) -> impl Iterator<Item = &Step> {
        self.steps.iter().map(|(forward, _)| forward)
    }

    /// One more rewrite, applied and recorded.
    pub fn push(&mut self, graph: &mut Graph, step: Step) -> Result<(), Error> {
        let back = apply(graph, &step)?;
        self.steps.push((step, back));
        Ok(())
    }

    /// The graph back where it started: every step undone, latest first,
    /// each match said again in terms of the boxes the undo before it put
    /// back. This is what closes the valley — a derivation from `A` and the
    /// undo of one from `B`.
    pub fn undo(&self, graph: &mut Graph) -> Result<(), Error> {
        let mut moved: HashMap<NodeId, NodeId> = HashMap::new();
        for (forward, back) in self.steps.iter().rev() {
            let here = Step {
                rule: back.rule.clone(),
                dir: back.dir,
                at: rebase(&back.at, &moved),
            };
            let restored = apply(graph, &here)?;
            // What this undo put back is what the step had matched, under
            // ids the graph had not handed out at the time. A step deletes
            // the boxes it matches, so nothing later ever matched them
            // again — which is why one lookup is enough and there is no
            // chain to chase.
            for (&was, &now) in forward.at.nodes.iter().zip(&restored.at.nodes) {
                moved.insert(was, now);
            }
        }
        Ok(())
    }
}

/// A match said again in terms of the boxes that stand where its own used
/// to.
fn rebase(at: &Match, moved: &HashMap<NodeId, NodeId>) -> Match {
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
        nodes: at.nodes.iter().map(|&id| now(id)).collect(),
        inputs: at.inputs.iter().map(|&src| port(src)).collect(),
        outputs: at
            .outputs
            .iter()
            .map(|sinks| sinks.iter().map(|&sink| reader(sink)).collect())
            .collect(),
        branches: at.branches.clone(),
    }
}

/// Every step applied in order, answering with the run that did it.
///
/// A derivation replays against the graph it was written for and no other:
/// a [`Match`] names host [`NodeId`]s, and ids are handed out in order, so
/// the same steps on the same starting graph land in the same places — and
/// on a different graph they name boxes that are not there.
pub fn replay(graph: &mut Graph, steps: &[Step]) -> Result<Derivation, Error> {
    let mut run = Derivation::default();
    for step in steps {
        run.push(graph, step.clone())?;
    }
    Ok(run)
}

/// Whether the match points at a subgraph isomorphic to the pattern.
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
/// The indexing here is unchecked on purpose: a pattern comes from
/// [`sides`], which holds it to [`Graph::check`](super::Graph::check), so
/// every source it names is a source it has. What is *not* trusted is the
/// match, and every field of it is measured against the pattern before it
/// is used to index anything.
fn check_match(graph: &Graph, pattern: &Graph, at: &Match) -> Result<(), Mismatch> {
    debug_assert!(
        pattern.nodes.iter().all(Option::is_some),
        "a rule's side deletes nothing, so its boxes are dense"
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
/// which is where the inverse step lands.
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

    // In. A rule's side builds its boxes producers-first, so its own order
    // is one the host can add them in.
    let mut fresh: Vec<NodeId> = Vec::with_capacity(replacement.nodes.len());
    let carry = |src: Source, at: &Match, fresh: &[NodeId]| match src {
        Source::Input(i) => at.inputs[i],
        Source::Port { node, port } => Source::Port {
            node: fresh[node.index()],
            port,
        },
    };
    for slot in &replacement.nodes {
        let node = slot.as_ref().expect("a rule's side deletes nothing");
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
/// it binds the renaming as it goes and [`same_kind`] is what holds the
/// binding it settled on.
fn kinds_fit(pattern: &NodeKind, host: &NodeKind) -> bool {
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

// ---- finding one, which is not the checker's business ----------------------------

/// Every embedding of `pattern` in `graph`.
///
/// Search, and wrong the way a guess is wrong: everything it does is checked
/// by [`apply`] anyway, so a matcher with a bug makes a rewrite that is
/// refused rather than one that changes what a program means.
///
/// It **declines** — answers with nothing, for every graph — where a pattern
/// does not pin its own match:
///
/// - a pattern with no boxes has nothing to anchor on, which is every
///   right-hand side in the table but `not-not`'s;
/// - a pattern that exports one port twice, or that exports a boundary
///   input, leaves the split of that source's outside readers a choice.
///
/// Those are the payloads a derivation has to *state* rather than read, and
/// [`Match`] is where it states them.
pub fn find(graph: &Graph, pattern: &Graph) -> Vec<Match> {
    graph
        .live()
        .map(|(id, _)| id)
        .flat_map(|seed| find_at(graph, pattern, seed))
        .collect()
}

/// [`find`], with the pattern's first box pinned to one node. What
/// [`propose`] uses, since a rule read off a node is a rule anchored there.
pub fn find_at(graph: &Graph, pattern: &Graph, seed: NodeId) -> Vec<Match> {
    if !pins_itself(pattern) || !graph.is_live(seed) {
        return Vec::new();
    }
    let mut search = Search {
        graph,
        pattern,
        nodes: vec![None; pattern.nodes.len()],
        inputs: vec![None; pattern.inputs.len()],
        branches: vec![None; pattern.branches as usize],
        used: HashSet::new(),
        seed,
        found: Vec::new(),
    };
    search.walk(0);
    search.found
}

/// Whether a pattern says enough about itself to be looked for: at least one
/// box to anchor on, and no source exported twice or exported straight from
/// the boundary.
fn pins_itself(pattern: &Graph) -> bool {
    if pattern.nodes.is_empty() {
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
    nodes: Vec<Option<NodeId>>,
    inputs: Vec<Option<Source>>,
    branches: Vec<Option<BranchId>>,
    used: HashSet<NodeId>,
    seed: NodeId,
    found: Vec<Match>,
}

impl Search<'_> {
    fn walk(&mut self, i: usize) {
        if i == self.nodes.len() {
            self.finish();
            return;
        }
        for host in self.candidates(i) {
            let undo = self.assign(i, host);
            if let Some(undo) = undo {
                self.walk(i + 1);
                self.undo(i, host, undo);
            }
        }
    }

    /// The host boxes worth trying for the pattern's box `i`.
    ///
    /// Once one box is fixed, its neighbours are: a port whose source is
    /// already known has only that source's readers to offer. Only a box
    /// nothing so far touches falls back on the whole graph, which is why
    /// two unconnected boxes — `dedup`'s pattern — still cost one sweep
    /// rather than a product.
    fn candidates(&self, i: usize) -> Vec<NodeId> {
        if i == 0 {
            return vec![self.seed];
        }
        let here = NodeId::at(i);
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
                    let want = self.nodes[node.index()].map(|n| Source::Port { node: n, port });
                    if want != Some(hsrc) {
                        self.rollback(&fixed, branch);
                        return None;
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

/// The steps that could fire at one box.
///
/// The other half of what is not the checker: [`sides`] needs a payload, and
/// a payload is read off the box a rule would be anchored at — its kind and
/// its widths, and nothing deeper. Every proposal goes through [`apply`],
/// so one that is wrong costs a refusal.
pub fn propose(graph: &Graph, laws: &[Law], id: NodeId) -> Vec<Step> {
    if !graph.is_live(id) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for &law in laws {
        for (rule, seed) in read_off(graph, law, id) {
            let Ok((lhs, _)) = sides(&rule) else { continue };
            out.extend(find_at(graph, &lhs, seed).into_iter().map(|at| Step {
                rule: rule.clone(),
                dir: Direction::Forward,
                at,
            }));
        }
    }
    out
}

/// The boxes between a fork and one side of its select, lifted out as a
/// graph of their own — the payload a whole-branch rule carries.
///
/// The region is what lies **downstream of that side's views and upstream
/// of that side's blocks**. A box the arm merely reads and does not own — a
/// literal shared with the world outside, say — is downstream of no view,
/// so it stays outside and becomes one of the arm's own inputs.
///
/// `None` when the region is not self-contained: one of its boxes is read
/// from outside the branch, so lifting it out would strand a reader. The
/// rule then declines, which is the honest answer — a whole-branch window
/// cannot hold a branch whose insides are not wholly its own.
fn arm(
    graph: &Graph,
    select: NodeId,
    blocks: &[Source],
    side: std::ops::Range<usize>,
    views: &[Source],
) -> Option<Graph> {
    // Downstream of the views, stopping at the select.
    let mut ahead: HashSet<NodeId> = HashSet::new();
    let mut todo: Vec<Source> = views.to_vec();
    while let Some(src) = todo.pop() {
        for &sink in graph.sinks(src) {
            let Sink::Port { node, .. } = sink else {
                continue;
            };
            if node == select || !ahead.insert(node) {
                continue;
            }
            for port in 0..graph.kind(node).arity().outputs {
                todo.push(Source::Port { node, port });
            }
        }
    }
    // ...and upstream of the blocks, which is where it stops being an arm.
    let mut region: Vec<NodeId> = Vec::new();
    let mut todo: Vec<Source> = blocks.to_vec();
    while let Some(Source::Port { node, .. }) = todo.pop() {
        if !ahead.contains(&node) || region.contains(&node) {
            continue;
        }
        region.push(node);
        todo.extend(graph.sources(node).iter().copied());
    }
    region.sort_unstable();
    let mine: HashSet<NodeId> = region.iter().copied().collect();

    // An order the arm can be rebuilt in. Ids will not do: a rewrite that
    // re-points an old reader at a new box — `fork-dedup` does — leaves a
    // low id reading a high one, so the region is sorted by its own edges.
    let mut order: Vec<NodeId> = Vec::with_capacity(region.len());
    while order.len() < region.len() {
        let stuck = order.len();
        for &node in &region {
            if order.contains(&node) {
                continue;
            }
            let ready = graph.sources(node).iter().all(|src| match src {
                Source::Port { node: made, .. } => !mine.contains(made) || order.contains(made),
                Source::Input(_) => true,
            });
            if ready {
                order.push(node);
            }
        }
        if order.len() == stuck {
            return None;
        }
    }
    let region = order;

    // Self-contained, or nothing doing.
    for &node in &region {
        for port in 0..graph.kind(node).arity().outputs {
            for &sink in graph.sinks(Source::Port { node, port }) {
                let held = match sink {
                    Sink::Output(_) => false,
                    Sink::Port { node: reader, port } => {
                        mine.contains(&reader) || (reader == select && side.contains(&port))
                    }
                };
                if !held {
                    return None;
                }
            }
        }
    }

    // What it reads that it does not own: the views first, then the rest.
    let held = |src: Source| matches!(src, Source::Port { node, .. } if mine.contains(&node));
    let mut extra: Vec<Source> = Vec::new();
    let sources = region
        .iter()
        .flat_map(|&node| graph.sources(node).iter().copied())
        .chain(blocks.iter().copied());
    for src in sources {
        if !held(src) && !views.contains(&src) && !extra.contains(&src) {
            extra.push(src);
        }
    }

    let place: HashMap<NodeId, usize> = region.iter().enumerate().map(|(i, &n)| (n, i)).collect();
    let mut branches: Vec<BranchId> = Vec::new();
    for &node in &region {
        if let NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } = graph.kind(node)
            && !branches.contains(branch)
        {
            branches.push(*branch);
        }
    }
    let renumber = |kind: &NodeKind| {
        let of =
            |b: &BranchId| BranchId(branches.iter().position(|h| h == b).expect("noted") as u32);
        match kind {
            NodeKind::Fork { arity, branch } => NodeKind::Fork {
                arity: *arity,
                branch: of(branch),
            },
            NodeKind::Select { arity, branch } => NodeKind::Select {
                arity: *arity,
                branch: of(branch),
            },
            other => other.clone(),
        }
    };
    let inside = |src: Source| match src {
        Source::Port { node, port } if mine.contains(&node) => Source::Port {
            node: NodeId::at(place[&node]),
            port,
        },
        other => match views.iter().position(|&v| v == other) {
            Some(i) => Source::Input(i),
            None => {
                Source::Input(views.len() + extra.iter().position(|&e| e == other).expect("noted"))
            }
        },
    };

    let mut lifted = Graph::empty(views.len() + extra.len());
    for &node in &region {
        let takes = graph.sources(node).iter().map(|&s| inside(s)).collect();
        lifted.add(renumber(graph.kind(node)), takes);
    }
    lifted.branches = branches.len() as u32;
    lifted.close(blocks.iter().map(|&s| inside(s)).collect());
    lifted.check().ok()?;
    Some(lifted)
}

/// The payloads one law could be anchored at one box with, each paired with
/// the box the pattern's **first** node would land on.
///
/// Those are usually the same box, and for the branch laws they are not: a
/// pattern is built producers-first, so a rule whose window holds a literal
/// begins at that literal, while the box a payload is *read* off is the
/// `select` the literal decides. Reading and seeding come apart, and this is
/// where.
fn read_off(graph: &Graph, law: Law, id: NodeId) -> Vec<(Rule, NodeId)> {
    let kind = graph.kind(id).clone();
    let takes = graph.sources(id);
    // What produces one source, when that is a box's port 0.
    let made_by = |src: Source| match src {
        Source::Port { node, port: 0 } => Some((node, graph.kind(node))),
        _ => None,
    };
    let one = |rule: Rule| vec![(rule, id)];
    match (law, &kind) {
        (Law::IdElim, NodeKind::Id(n)) => one(Rule::IdElim { n: *n }),
        (Law::SwapElim, NodeKind::Op(Prim::Swap)) => one(Rule::SwapElim),
        (Law::CopyElim, NodeKind::Copy(n)) => one(Rule::CopyElim { n: *n }),
        (Law::DeadNode, _) => one(Rule::DeadNode { kind }),
        (Law::Dedup, NodeKind::Fork { .. } | NodeKind::Select { .. }) => Vec::new(),
        (Law::Dedup, _) => one(Rule::Dedup { kind }),
        (Law::NotNot, NodeKind::Op(Prim::Not)) => one(Rule::NotNot),

        // A block that is really a value from before the fork.
        (
            Law::SelectView,
            NodeKind::Select {
                arity: n,
                branch: mine,
            },
        ) => {
            let n = *n;
            // Every block this branch's fork supplies, together: a window
            // holding the fork has to account for all of them at once.
            let mut from: Option<(NodeId, usize)> = None;
            let mut views: Vec<(usize, usize)> = Vec::new();
            for b in 0..2 * n {
                let Source::Port { node: fork, port } = takes[1 + b] else {
                    continue;
                };
                let NodeKind::Fork { arity: f, branch } = graph.kind(fork) else {
                    continue;
                };
                // The two ends of *one* branch: the same id, and the one
                // condition, which is what port 0 on both ends is for.
                if branch != mine || graph.sources(fork)[0] != takes[0] {
                    continue;
                }
                if from.is_none() {
                    from = Some((fork, *f));
                }
                if from == Some((fork, *f)) {
                    views.push((b, port));
                }
            }
            match from {
                Some((fork, f)) => vec![(
                    Rule::SelectView {
                        fork: f,
                        arity: n,
                        views,
                    },
                    fork,
                )],
                None => Vec::new(),
            }
        }

        // A block the select answers with either way.
        (Law::SelectSame, NodeKind::Select { arity: n, .. }) => (0..*n)
            .filter(|j| takes[1 + j] == takes[1 + n + j])
            .map(|j| (Rule::SelectSame { arity: *n, at: j }, id))
            .collect(),

        // A condition that is already a value — and, with it, the whole
        // branch it decides.
        (
            Law::SelectLiteral,
            NodeKind::Select {
                arity: n,
                branch: mine,
            },
        ) => {
            let n = *n;
            let Some((lit, NodeKind::Op(Prim::Push(value)))) = made_by(takes[0]) else {
                return Vec::new();
            };
            let value = value.clone();
            // The fork this select is paired with, if the arms take
            // anything at all.
            let paired = graph.live().find_map(|(node, kind)| match kind {
                NodeKind::Fork { arity, branch } if branch == mine => Some((node, *arity)),
                _ => None,
            });
            let f = paired.map_or(0, |(_, f)| f);
            let views: Vec<Source> = paired
                .into_iter()
                .flat_map(|(node, f)| (0..2 * f).map(move |port| Source::Port { node, port }))
                .collect();
            let blocks = &takes[1..1 + 2 * n];
            let Some(then_arm) = arm(graph, id, &blocks[..n], 1..1 + n, &views[..f]) else {
                return Vec::new();
            };
            let Some(else_arm) = arm(graph, id, &blocks[n..], 1 + n..1 + 2 * n, &views[f..]) else {
                return Vec::new();
            };
            vec![(
                Rule::SelectLiteral {
                    value,
                    fork: paired.map(|(_, f)| f),
                    then_arm,
                    else_arm,
                },
                lit,
            )]
        }

        // A condition that is a test against a literal, and a block that
        // answers with the very value tested.
        (Law::SpecializeEqual, NodeKind::Select { arity: n, .. }) => {
            let Some((test, NodeKind::Op(Prim::Equal))) = made_by(takes[0]) else {
                return Vec::new();
            };
            let operands = graph.sources(test);
            let (lit, side, x) = match (made_by(operands[0]), made_by(operands[1])) {
                (Some((lit, NodeKind::Op(Prim::Push(_)))), _) => (lit, Side::Deep, operands[1]),
                (_, Some((lit, NodeKind::Op(Prim::Push(_))))) => (lit, Side::Top, operands[0]),
                _ => return Vec::new(),
            };
            let NodeKind::Op(Prim::Push(value)) = graph.kind(lit) else {
                return Vec::new();
            };
            (0..*n)
                .filter(|j| takes[1 + j] == x)
                .map(|j| {
                    (
                        Rule::SpecializeEqual {
                            arity: *n,
                            at: j,
                            value: value.clone(),
                            literal: side,
                        },
                        lit,
                    )
                })
                .collect()
        }

        // A block that answers with `as_bool` of a view of the very
        // condition — which is the only way an arm gets to see it.
        (
            Law::SpecializeBool,
            NodeKind::Select {
                arity: n,
                branch: mine,
            },
        ) => {
            let (n, cond) = (*n, takes[0]);
            (0..2 * n)
                .filter_map(|b| {
                    let (ab, NodeKind::Op(Prim::AsBool)) = made_by(takes[1 + b])? else {
                        return None;
                    };
                    let Source::Port { node: fork, port } = graph.sources(ab)[0] else {
                        return None;
                    };
                    let NodeKind::Fork { arity: f, branch } = graph.kind(fork) else {
                        return None;
                    };
                    let handed = graph.sources(fork);
                    // One branch, and a stack slot the condition was copied
                    // into — without which the coercion says nothing.
                    (branch == mine && handed[0] == cond && handed[1 + port % f] == cond).then_some(
                        (
                            Rule::SpecializeBool {
                                fork: *f,
                                arity: n,
                                view: port,
                                at: b,
                            },
                            fork,
                        ),
                    )
                })
                .collect()
        }

        // One operation done in both arms. Read off a box in the *then* arm;
        // the matcher is what finds its opposite number.
        (Law::ForkDedup, NodeKind::Fork { arity: n, .. }) => {
            let n = *n;
            let mut readers: Vec<NodeId> = Vec::new();
            for port in 0..n {
                for &sink in graph.sinks(Source::Port { node: id, port }) {
                    if let Sink::Port { node, .. } = sink
                        && !readers.contains(&node)
                    {
                        readers.push(node);
                    }
                }
            }
            readers
                .into_iter()
                .filter_map(|reader| {
                    let ports: Option<Vec<usize>> = graph
                        .sources(reader)
                        .iter()
                        .map(|src| match src {
                            Source::Port { node, port } if *node == id && *port < n => Some(*port),
                            _ => None,
                        })
                        .collect();
                    Some((
                        Rule::ForkDedup {
                            arity: n,
                            kind: graph.kind(reader).clone(),
                            ports: ports?,
                        },
                        id,
                    ))
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

// ---- rewriting to fixpoint -------------------------------------------------------

/// Every law spent everywhere it fires, and the derivation that did it.
///
/// A worklist rather than repeated passes, which the back-links are what
/// make possible: a rewrite leaves the graph already correct, so the only
/// thing to reconsider is the handful of boxes the step could have reached.
/// Every law in [`structural`] strictly shrinks the live box count — one
/// deleted, or two made one — so it drains.
pub fn saturate(graph: &mut Graph, laws: &[Law]) -> Derivation {
    saturate_watching(graph, laws, &mut |_| {})
}

/// [`saturate`], with a witness run against the graph after every single
/// firing. The tests use it to hold [`Graph::check`](super::Graph::check) at
/// each step rather than only at the fixpoint.
pub fn saturate_watching(
    graph: &mut Graph,
    laws: &[Law],
    after: &mut dyn FnMut(&Graph),
) -> Derivation {
    let mut work: Vec<NodeId> = graph.live().map(|(id, _)| id).collect();
    let mut spent = Derivation::default();
    while let Some(id) = work.pop() {
        if !graph.is_live(id) {
            continue;
        }
        let Some(step) = propose(graph, laws, id).into_iter().next() else {
            continue;
        };
        // What the step could reach, read before it lands: the producers of
        // what is going away, which may now be unread, and the readers of
        // what it leaves, which may now be duplicates of each other. The
        // second half is what `dedup` needs and the four eliminations do
        // not.
        let mut again = neighbours(graph, &step.at);
        let Ok(back) = apply(graph, &step) else {
            continue;
        };
        again.extend(back.at.nodes.iter().copied());
        for &src in &step.at.inputs {
            again.extend(readers(graph, src));
        }
        after(graph);
        work.extend(again);
        spent.steps.push((step, back));
    }
    spent
}

/// The boxes a step at this match could unsettle, read while it still
/// stands.
fn neighbours(graph: &Graph, at: &Match) -> Vec<NodeId> {
    let mut out = Vec::new();
    for &id in &at.nodes {
        for &src in graph.sources(id) {
            if let Source::Port { node, .. } = src {
                out.push(node);
            }
        }
    }
    for sinks in &at.outputs {
        for &sink in sinks {
            if let Sink::Port { node, .. } = sink {
                out.push(node);
            }
        }
    }
    out
}

fn readers(graph: &Graph, src: Source) -> Vec<NodeId> {
    graph
        .sinks(src)
        .iter()
        .filter_map(|&sink| match sink {
            Sink::Port { node, .. } => Some(node),
            Sink::Output(_) => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::meaning::{Meaning, boundary, eval_graph};
    use crate::diagram2::{build, read_back};
    use crate::term::Context;
    use crate::term::TermIndex;
    use bytecode::{Value, assemble};

    /// The two graphs a rule relates, run on the same symbols. A law whose
    /// two sides are different programs is not a law, and this is what says
    /// so — the same oracle `super` holds its own rewriting to, with every
    /// operation left opaque.
    fn means_the_same(law: Law, a: &Graph, b: &Graph) {
        let mut m = Meaning::default();
        let inputs = boundary(&mut m, a.arity().inputs);
        assert_eq!(
            eval_graph(&mut m, a, &inputs),
            eval_graph(&mut m, b, &inputs),
            "{:?} relates two different programs:\n{}\n{}",
            law,
            a,
            b
        );
    }

    /// A law holds. Five claims, and the payload is the only input: the two
    /// sides are *built* from it rather than written out here, so this
    /// tests the table itself and not a second copy of it.
    ///
    /// 1. Both sides are graphs, and of one interface — so no step can
    ///    change what a graph takes or leaves.
    /// 2. They are the same program.
    /// 3. Each side, taken as a graph in its own right, matches itself.
    /// 4. Applying the rule to one side lands on the other.
    /// 5. The step that comes back undoes it.
    fn holds(law: Law, rule: Rule) {
        assert_eq!(rule.law(), law, "the payload names the wrong law");
        let (lhs, rhs) =
            sides(&rule).unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        assert_eq!(lhs.arity(), rhs.arity());
        means_the_same(law, &lhs, &rhs);

        for (dir, here, there) in [
            (Direction::Forward, &lhs, &rhs),
            (Direction::Backward, &rhs, &lhs),
        ] {
            // A rule's own side is the one graph its pattern is certain to
            // be found in, and the identity embedding is the match — so
            // the matcher and the table agree, wherever the matcher is
            // total.
            let found = find(here, here);
            if pins_itself(here) {
                assert!(
                    found.contains(&identity(here)),
                    "{:?} {:?}: the matcher does not find its own side:\n{}",
                    law,
                    dir,
                    here
                );
            } else {
                assert!(
                    found.is_empty(),
                    "{:?} {:?}: a side that pins nothing was matched anyway",
                    law,
                    dir
                );
            }
            let mut whole = here.clone();
            let step = Step {
                rule: rule.clone(),
                dir,
                at: identity(here),
            };
            let back =
                apply(&mut whole, &step).unwrap_or_else(|e| panic!("{:?} {:?}: {}", law, dir, e));
            whole
                .check()
                .unwrap_or_else(|e| panic!("{:?} {:?} left a torn graph: {}", law, dir, e));
            means_the_same(law, &whole, there);

            // And the way back really is the way back.
            apply(&mut whole, &back)
                .unwrap_or_else(|e| panic!("{:?} {:?} does not undo: {}", law, dir, e));
            whole.check().unwrap();
            means_the_same(law, &whole, here);
        }
    }

    /// A graph matched against itself: every box its own image, every
    /// boundary its own, and the boundary outputs served by nothing.
    fn identity(g: &Graph) -> Match {
        Match {
            nodes: (0..g.nodes.len()).map(NodeId::at).collect(),
            inputs: (0..g.inputs.len()).map(Source::Input).collect(),
            outputs: (0..g.outputs.len())
                .map(|j| vec![Sink::Output(j)])
                .collect(),
            branches: (0..g.branches).map(BranchId).collect(),
        }
    }

    /// The graph a body builds, with the arena its term lives in.
    fn built(body: &str) -> (Context, Graph) {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        let mut terms = Context::new();
        let term = crate::term::lower(&mut terms, &library, idx).unwrap();
        let graph = build(&terms, term);
        graph.check().unwrap();
        (terms, graph)
    }

    fn only(kind: &NodeKind, graph: &Graph) -> NodeId {
        let mut found = graph.live().filter(|(_, k)| kinds_fit(kind, k));
        let (id, _) = found
            .next()
            .unwrap_or_else(|| panic!("no {} in\n{}", kind, graph));
        assert!(
            found.next().is_none(),
            "more than one {} in\n{}",
            kind,
            graph
        );
        id
    }

    // ---- the table ----

    #[test]
    fn an_identity_box_is_a_wire() {
        holds(Law::IdElim, Rule::IdElim { n: 3 });
        holds(Law::IdElim, Rule::IdElim { n: 0 });
    }

    #[test]
    fn a_crossing_is_the_links_it_leaves() {
        holds(Law::SwapElim, Rule::SwapElim);
    }

    #[test]
    fn a_copy_is_a_port_read_twice() {
        holds(Law::CopyElim, Rule::CopyElim { n: 1 });
        holds(Law::CopyElim, Rule::CopyElim { n: 3 });
    }

    /// The side condition that is an interface rather than a test: the left
    /// side exports nothing, so a box with a reader is simply not that
    /// graph. `drop(n)` is the base case, having no outputs to export.
    #[test]
    fn work_nothing_reads_is_no_work() {
        for kind in [
            NodeKind::Drop(2),
            NodeKind::Op(Prim::Add),
            NodeKind::Op(Prim::Push(Value::Int(9))),
            NodeKind::Copy(2),
            NodeKind::Select {
                arity: 2,
                branch: BranchId(7),
            },
        ] {
            holds(Law::DeadNode, Rule::DeadNode { kind });
        }
        let (_, lhs) = (
            0,
            sides(&Rule::DeadNode {
                kind: NodeKind::Op(Prim::Add),
            })
            .unwrap()
            .0,
        );
        assert_eq!(lhs.arity(), Arity::new(2, 0), "the window exports nothing");
    }

    #[test]
    fn one_computation_run_twice_is_one_box() {
        holds(
            Law::Dedup,
            Rule::Dedup {
                kind: NodeKind::Op(Prim::Add),
            },
        );
        holds(
            Law::Dedup,
            Rule::Dedup {
                kind: NodeKind::Op(Prim::Push(Value::Int(9))),
            },
        );
        holds(
            Law::Dedup,
            Rule::Dedup {
                kind: NodeKind::Op(Prim::Untuple(3)),
            },
        );
    }

    /// A fork is a copy in everything but the one fact it records, and the
    /// rule that would delete that fact is refused before it is built.
    #[test]
    fn dedup_refuses_the_two_ends_of_a_branch() {
        for kind in [
            NodeKind::Fork {
                arity: 2,
                branch: BranchId(0),
            },
            NodeKind::Select {
                arity: 2,
                branch: BranchId(0),
            },
        ] {
            assert_eq!(
                sides(&Rule::Dedup { kind }).unwrap_err(),
                Error::Ill {
                    law: Law::Dedup,
                    why: Ill::Refused
                }
            );
        }
    }

    /// `not ; not = as_bool`. The opaque oracle cannot judge this one — it
    /// reads `not(not(x))` and `as_bool(x)` as different symbols, which is
    /// exactly right of *wiring* and wrong of *this law* — so the judge is
    /// the machine, reached the way `diagram` reaches it: fold each side on
    /// a literal and see that the answers agree. `vm` states the law itself,
    /// over every shape of value.
    #[test]
    fn not_twice_is_the_coercion() {
        for v in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(42),
            Value::unit(),
        ] {
            let mut terms = Context::new();
            let long = {
                let push = terms.op(Prim::Push(v.clone()));
                let not = terms.op(Prim::Not);
                let once = terms.compose(push, not).unwrap();
                let not = terms.op(Prim::Not);
                terms.compose(once, not).unwrap()
            };
            let mut graph = build(&terms, long);
            let spent = saturate(&mut graph, &[Law::NotNot]);
            assert_eq!(spent.len(), 1, "the window is right there");
            graph.check().unwrap();
            let folded = read_back(&graph, &mut terms);
            assert_eq!(
                format!("{}", terms.display(folded)),
                format!("push {} ; as_bool", v)
            );

            let short = {
                let push = terms.op(Prim::Push(v.clone()));
                let coerce = terms.op(Prim::AsBool);
                terms.compose(push, coerce).unwrap()
            };
            let mut engine = crate::diagram::Ctx::default();
            assert_eq!(
                crate::diagram::normalize(&mut engine, &terms, folded),
                crate::diagram::normalize(&mut engine, &terms, short),
                "not ; not disagrees with as_bool on {:?}",
                v
            );
        }
    }

    /// The one place `not-not` must *not* fire: something else reads the
    /// first `not`, so the window the rule states — whose middle port is
    /// not exported — is not there.
    #[test]
    fn a_not_someone_else_reads_is_not_the_window() {
        // `not` once, copied, and the copy negated again: the first `not`'s
        // port ends up with two readers, so nothing here is `not ; not`.
        let (_terms, mut graph) = built("not pick 0 not");
        saturate(&mut graph, &structural());
        let spent = saturate(&mut graph, &[Law::NotNot]);
        assert!(spent.is_empty(), "fired anyway:\n{}", graph);
    }

    // ---- the branch layer ----

    /// Every assignment of a handful of values to `width` inputs.
    ///
    /// Five values, chosen to cover the truthiness table on both poles:
    /// `false` is the one falsy value, and `unit` is junk, which is truthy
    /// like everything else.
    fn samples(width: usize) -> Vec<Vec<Value>> {
        let each = [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(7),
            Value::unit(),
        ];
        let mut out: Vec<Vec<Value>> = vec![Vec::new()];
        for _ in 0..width {
            out = out
                .into_iter()
                .flat_map(|so_far| {
                    each.iter().map(move |v| {
                        let mut next = so_far.clone();
                        next.push(v.clone());
                        next
                    })
                })
                .collect();
        }
        out
    }

    /// A graph with a literal on every one of its inputs, as a term.
    fn closed(terms: &mut Context, g: &Graph, values: &[Value]) -> TermIndex {
        assert_eq!(values.len(), g.arity().inputs, "one literal per input");
        let back = read_back(g, terms);
        let mut stack: Option<TermIndex> = None;
        for v in values {
            let push = terms.op(Prim::Push(v.clone()));
            stack = Some(match stack {
                None => push,
                Some(acc) => terms.pad_compose(acc, push),
            });
        }
        match stack {
            None => back,
            Some(stack) => terms.pad_compose(stack, back),
        }
    }

    /// A law held to the **machine**, over every assignment of a handful of
    /// values to its boundary.
    ///
    /// The opaque oracle cannot judge these: `equal(x, 7)` is a symbol to
    /// it, and the whole content of the law is what that symbol computes. So
    /// the judge is the one `diagram` is — close both sides with literals
    /// and fold. Sampling is not a proof, and the proof is in the docs; this
    /// is what would catch the proof being wrong.
    fn the_machine_agrees(law: Law, rule: Rule) {
        assert_eq!(rule.law(), law, "the payload names the wrong law");
        assert!(!is_wiring(law), "a wiring law has a cheaper judge");
        let (lhs, rhs) =
            sides(&rule).unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        assert_eq!(lhs.arity(), rhs.arity());
        for values in samples(lhs.arity().inputs) {
            let mut terms = Context::new();
            let long = closed(&mut terms, &lhs, &values);
            let short = closed(&mut terms, &rhs, &values);
            let mut engine = crate::diagram::Ctx::default();
            assert_eq!(
                crate::diagram::normalize(&mut engine, &terms, long),
                crate::diagram::normalize(&mut engine, &terms, short),
                "{:?} relates two different programs on {:?}",
                law,
                values
            );
        }
    }

    /// One operation done in both arms is one operation. The fork's views
    /// are copies, so the two boxes were always computing the one thing —
    /// which makes this pure wiring, and the opaque oracle can judge it.
    #[test]
    fn one_operation_in_both_arms_is_one_operation() {
        holds(
            Law::ForkDedup,
            Rule::ForkDedup {
                arity: 1,
                kind: NodeKind::Op(Prim::Not),
                ports: vec![0],
            },
        );
        holds(
            Law::ForkDedup,
            Rule::ForkDedup {
                arity: 3,
                kind: NodeKind::Op(Prim::Add),
                ports: vec![2, 0],
            },
        );
        // The two ends of a branch are what a fork is for, so merging two of
        // *them* is refused for the reason `dedup` refuses it.
        for kind in [
            NodeKind::Fork {
                arity: 1,
                branch: BranchId(0),
            },
            NodeKind::Select {
                arity: 1,
                branch: BranchId(0),
            },
        ] {
            assert!(matches!(
                sides(&Rule::ForkDedup {
                    arity: 3,
                    kind,
                    ports: vec![0],
                }),
                Err(Error::Ill {
                    why: Ill::Refused,
                    ..
                })
            ));
        }
        // A box that reads none of the views is not about this fork, and
        // merging it is plain `dedup`.
        assert!(matches!(
            sides(&Rule::ForkDedup {
                arity: 1,
                kind: NodeKind::Op(Prim::Push(Value::Int(1))),
                ports: Vec::new(),
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// A choice between one value is that value — and the rule that pulls a
    /// block out from behind a fork, which is what gives it anything to fire
    /// on.
    #[test]
    fn a_block_answered_either_way_is_the_answer() {
        holds(Law::SelectSame, Rule::SelectSame { arity: 1, at: 0 });
        holds(Law::SelectSame, Rule::SelectSame { arity: 3, at: 1 });
        for (fork, arity, views) in [
            (1, 1, vec![(0, 0)]),
            // The symmetric case: one wire through both arms, which is what
            // a window holding the fork has to take in one bite.
            (1, 1, vec![(0, 0), (1, 1)]),
            (2, 3, vec![(5, 3)]),
            (2, 2, vec![(1, 0), (3, 2), (2, 1)]),
        ] {
            holds(Law::SelectView, Rule::SelectView { fork, arity, views });
        }
    }

    /// An arm of one box on the view it was handed.
    fn one_step(kind: NodeKind) -> Graph {
        let mut g = Graph::empty(1);
        let out = g.add(kind, vec![Source::Input(0)]);
        g.close(out);
        g
    }

    /// An arm that hands its view straight on.
    fn passes() -> Graph {
        let mut g = Graph::empty(1);
        g.close(vec![Source::Input(0)]);
        g
    }

    /// An arm that reads nothing and answers with a literal. It still takes
    /// `f` inputs — an arm is handed every view whether it looks at them or
    /// not.
    fn yields(f: usize, v: Value) -> Graph {
        let mut g = Graph::empty(f);
        let out = g.add(NodeKind::Op(Prim::Push(v)), Vec::new());
        g.close(out);
        g
    }

    /// β. Sound on **every** value and not only on booleans, because
    /// `truthy` is total: `false` is the one falsy value, so zero and junk
    /// and the empty tuple all take the then block.
    ///
    /// The arms come along as payload, so the pair the law states is the
    /// **whole branch** against one arm — which is why the fork goes with
    /// the select rather than being left behind.
    #[test]
    fn a_literal_condition_keeps_its_arm() {
        for value in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::unit(),
        ] {
            // Arms that take nothing, so there is no fork to pair with.
            the_machine_agrees(
                Law::SelectLiteral,
                Rule::SelectLiteral {
                    value: value.clone(),
                    fork: None,
                    then_arm: yields(0, Value::Int(1)),
                    else_arm: yields(0, Value::Int(2)),
                },
            );
            // Arms that each do a box's worth of work on their own view.
            the_machine_agrees(
                Law::SelectLiteral,
                Rule::SelectLiteral {
                    value: value.clone(),
                    fork: Some(1),
                    then_arm: one_step(NodeKind::Op(Prim::Not)),
                    else_arm: one_step(NodeKind::Op(Prim::Negate)),
                },
            );
            // One arm passing its view through, the other ignoring it.
            the_machine_agrees(
                Law::SelectLiteral,
                Rule::SelectLiteral {
                    value: value.clone(),
                    fork: Some(1),
                    then_arm: passes(),
                    else_arm: yields(1, Value::Int(5)),
                },
            );
        }
    }

    /// An arm that reads something from outside the branch is still an arm;
    /// what it reads becomes one of its own inputs, and the pattern's
    /// boundary carries it.
    #[test]
    fn an_arm_may_read_from_outside_the_branch() {
        let mut adds = Graph::empty(2);
        let out = adds.add(
            NodeKind::Op(Prim::Add),
            vec![Source::Input(0), Source::Input(1)],
        );
        adds.close(out);
        let rule = Rule::SelectLiteral {
            value: Value::Bool(true),
            fork: Some(1),
            then_arm: adds,
            else_arm: yields(1, Value::Int(5)),
        };
        let (lhs, _) = sides(&rule).unwrap();
        // One view, plus the outside value the then arm reads.
        assert_eq!(lhs.arity().inputs, 2);
        the_machine_agrees(Law::SelectLiteral, rule);
    }

    /// A payload whose arms disagree about how much they answer with states
    /// no equation, and is refused before anything is compared.
    #[test]
    fn arms_that_answer_differently_are_refused() {
        let mut two = Graph::empty(1);
        two.close(vec![Source::Input(0), Source::Input(0)]);
        assert!(matches!(
            sides(&Rule::SelectLiteral {
                value: Value::Bool(true),
                fork: Some(1),
                then_arm: passes(),
                else_arm: two,
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// A value that tested `equal` to a literal **is** that literal, in the
    /// block the test chose. `equal` answers `Bool(a == b)`, so a truthy
    /// answer is `a == b` and nothing weaker — which is what makes the
    /// substitution exact rather than merely plausible.
    #[test]
    fn a_value_that_tested_equal_is_the_literal() {
        for literal in [Side::Deep, Side::Top] {
            for value in [Value::Int(7), Value::Bool(false), Value::unit()] {
                the_machine_agrees(
                    Law::SpecializeEqual,
                    Rule::SpecializeEqual {
                        arity: 1,
                        at: 0,
                        value,
                        literal,
                    },
                );
            }
        }
    }

    /// `as_bool` of the very value a branch tested is what the branch
    /// decided. Exact on both arms: `as_bool` *is* `truthy` made into an
    /// instruction, and the else block is reached only by `false`.
    #[test]
    fn as_bool_of_a_condition_is_what_the_branch_decided() {
        // `at < arity` is the then side; both halves, and both views.
        for (fork, arity, view, at) in [(1, 1, 0, 0), (1, 1, 1, 1)] {
            the_machine_agrees(
                Law::SpecializeBool,
                Rule::SpecializeBool {
                    fork,
                    arity,
                    view,
                    at,
                },
            );
        }
    }

    /// A body built, then settled against the whole table.
    fn settled(body: &str) -> (Context, Graph, Vec<Law>) {
        let (terms, mut graph) = built(body);
        let run = saturate(&mut graph, &[structural(), branching()].concat());
        graph
            .check()
            .unwrap_or_else(|e| panic!("{}: {}\n{}", body, e, graph));
        let spent = run.steps().map(|step| step.rule.law()).collect();
        (terms, graph, spent)
    }

    fn reads_as(terms: &mut Context, graph: &Graph) -> String {
        let back = read_back(graph, terms);
        format!("{}", terms.display(back))
    }

    /// `branch { A } { A } = drop-top ; A`, which
    /// [docs/algebra.md](../../../docs/algebra.md) books as a layer-2 law
    /// and which is written down nowhere: it falls out of `fork-dedup`,
    /// then `select-same`, then `dead-node`.
    #[test]
    fn a_branch_with_one_answer_is_no_branch() {
        let (mut terms, graph, spent) = settled("branch { not } { not }");
        assert!(spent.contains(&Law::ForkDedup), "{:?}", spent);
        assert!(spent.contains(&Law::SelectSame), "{:?}", spent);
        assert_eq!(graph.live_count(), 1, "{}", graph);
        assert_eq!(reads_as(&mut terms, &graph), "id(1) * drop(1) ; not");
    }

    /// A wire both arms pass through untouched. Nothing can see it until
    /// `select-view` pulls it out from behind the fork, which is that rule's
    /// whole reason for being.
    #[test]
    fn a_wire_through_both_arms_is_the_wire() {
        let (mut terms, graph, spent) = settled("branch { pick 0 drop 0 } { pick 0 drop 0 }");
        assert!(spent.contains(&Law::SelectView), "{:?}", spent);
        assert!(spent.contains(&Law::SelectSame), "{:?}", spent);
        assert_eq!(graph.live_count(), 0, "{}", graph);
        assert_eq!(reads_as(&mut terms, &graph), "id(1) * drop(1)");
    }

    /// β, on the truthiness table the machine actually has: `false` is the
    /// one falsy value, so a zero and an empty tuple both take the *then*
    /// arm. A rule stated for booleans alone would get this wrong.
    ///
    /// And it folds the branch **whole** — arms included, so the fork goes
    /// with the select rather than being left behind holding views nobody
    /// pairs with.
    #[test]
    fn a_literal_condition_folds_the_whole_branch() {
        let (mut terms, graph, spent) = settled("push true branch { push 1 } { push 2 }");
        assert!(spent.contains(&Law::SelectLiteral), "{:?}", spent);
        assert_eq!(reads_as(&mut terms, &graph), "push 1");

        for (cond, answer) in [("push 0", "push 1"), ("push false", "push 2")] {
            let body = format!("{} branch {{ push 1 }} {{ push 2 }}", cond);
            let (mut terms, graph, _) = settled(&body);
            assert_eq!(reads_as(&mut terms, &graph), answer, "{}", body);
        }

        // Arms with work in them, and a fork to hand them their views: all
        // of it goes, and what the surviving arm did is left standing on
        // the values the fork was handed.
        let (mut terms, graph, _) = settled("push true branch { not } { negate }");
        assert_eq!(reads_as(&mut terms, &graph), "not");
        let (mut terms, graph, _) = settled("push true branch { push 1 add } { drop 0 push 0 }");
        assert_eq!(reads_as(&mut terms, &graph), "id(1) * push 1 ; add");
    }

    /// The point of carrying the arms: a branch is folded at both ends or
    /// not at all, so nothing is left holding views no `select` pairs with.
    ///
    /// Only the **fork** is held to this, and the asymmetry is deliberate.
    /// Over the corpus, lone selects go from 39 before rewriting to 107
    /// after — `select-view` re-points every block out from behind a fork,
    /// its views all go unread, and `dead-node` takes it. Lone forks are 0
    /// either way.
    ///
    /// That is the right shape rather than a gap. A lone fork is the
    /// hazardous end: live views and no discard, which is where "observed
    /// only when the condition holds" stops being true. A lone select has no
    /// fork, so no views, so nothing to be wrong about — it is a chooser
    /// over values from outside. And a fork only dies once *every* view is
    /// unread, which means no arm box reads one either, so by the time a
    /// select is orphaned there is no arm left to reason about.
    ///
    /// Pairing them both would mean keeping every emptied fork alive — a
    /// box per branch, reading its inputs and producing nothing, exempt from
    /// the rule that would otherwise take it. That buys symmetry the
    /// semantics does not have.
    #[test]
    fn beta_takes_both_ends_of_a_branch() {
        let all = [structural(), branching()].concat();
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        let mut folded = 0;
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            let run = saturate(&mut graph, &all);
            folded += run
                .steps()
                .filter(|step| step.rule.law() == Law::SelectLiteral)
                .count();
            let ends: Vec<(BranchId, bool)> = graph
                .live()
                .filter_map(|(_, kind)| match kind {
                    NodeKind::Fork { branch, .. } => Some((*branch, true)),
                    NodeKind::Select { branch, .. } => Some((*branch, false)),
                    _ => None,
                })
                .collect();
            for (branch, fork) in ends.iter().filter(|(_, fork)| *fork) {
                assert!(
                    ends.iter().any(|(b, f)| b == branch && f != fork),
                    "sentence {}: branch {} kept a fork with no select",
                    library.names[idx],
                    branch
                );
            }
        }
        assert!(
            folded > 0,
            "no branch in the corpus had a literal condition"
        );
    }

    /// The whole table, over the corpus, judged by **`diagram`** — the one
    /// engine that decides this fragment outright.
    ///
    /// The opaque oracle cannot judge the value laws, so nothing else here
    /// holds β or the specializing rules to a real program. This does.
    ///
    /// Both sides are read back from a graph, and that matters: a branch
    /// comes back as both arms run flat and then a choice, which is a
    /// different case tree from the one the sentence was written as, and
    /// `diagram` is complete only off the branch fragment. Comparing the
    /// rewritten read-back against the **unrewritten** one puts that
    /// reshaping on both sides of the equation, so what is left to differ is
    /// the rules.
    #[test]
    fn the_whole_table_agrees_with_the_engine() {
        let all = [structural(), branching()].concat();
        let (library, mut arena, terms) = crate::diagram2::tests::corpus();
        let (mut judged, mut branchy) = (0, 0);
        for (idx, term) in terms {
            let start = build(&arena, term);
            // The read-back runs both arms flat, so a sentence with several
            // branches in it costs the engine a case tree the size of their
            // product. The big ones are left to the other corpus tests,
            // which judge the wiring rather than the values.
            if start.live_count() > 40 {
                continue;
            }
            let has_branch = start
                .live()
                .any(|(_, kind)| matches!(kind, NodeKind::Select { .. }));
            let plain = read_back(&start, &mut arena);
            let mut graph = start;
            saturate(&mut graph, &all);
            let spent = read_back(&graph, &mut arena);
            let mut engine = crate::diagram::Ctx::default();
            assert_eq!(
                crate::diagram::normalize(&mut engine, &arena, plain),
                crate::diagram::normalize(&mut engine, &arena, spent),
                "sentence {} means something else once the table has drained",
                library.names[idx]
            );
            judged += 1;
            branchy += usize::from(has_branch);
        }
        assert!(
            branchy > 5,
            "only {} of {} sentences judged had a branch in them",
            branchy,
            judged
        );
    }

    /// A value that tested `equal` to a literal is that literal where the
    /// test chose it — reached, as everything at a select is, only after
    /// `select-view` has pulled the block out from behind the fork.
    #[test]
    fn a_tested_value_becomes_its_literal() {
        let (_terms, graph, spent) =
            settled("pick 0 pick 0 push 7 equal branch { } { drop 0 push 0 }");
        assert!(spent.contains(&Law::SelectView), "{:?}", spent);
        assert!(spent.contains(&Law::SpecializeEqual), "{:?}", spent);

        let (select, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
            .expect("the branch is still a branch");
        let Source::Port { node: chose, .. } = graph.sources(select)[1] else {
            panic!("the then block is not a box:\n{}", graph);
        };
        assert!(
            matches!(graph.kind(chose), NodeKind::Op(Prim::Push(v)) if *v == Value::Int(7)),
            "the then block is {} rather than the literal:\n{}",
            graph.kind(chose),
            graph
        );
    }

    /// `as_bool` of a value the branch tested is what the branch decided,
    /// on either arm. The fork has to be in the window: an arm never sees
    /// the condition, only what the fork handed it, so the rule reaches
    /// this one by holding both the fork and the slot the condition was
    /// copied into.
    #[test]
    fn as_bool_in_an_arm_is_what_the_branch_decided() {
        for (body, answer) in [
            ("pick 0 branch { as_bool } { drop 0 push 5 }", "push true"),
            ("pick 0 branch { drop 0 push 5 } { as_bool }", "push false"),
        ] {
            let (_terms, graph, spent) = settled(body);
            assert!(
                spent.contains(&Law::SpecializeBool),
                "{}: {:?}",
                body,
                spent
            );
            assert!(
                graph
                    .live()
                    .all(|(_, kind)| !matches!(kind, NodeKind::Op(Prim::AsBool))),
                "{}: the coercion is still here:\n{}",
                body,
                graph
            );
            assert!(
                graph.live().any(|(_, kind)| format!("{}", kind) == answer),
                "{}: no {}:\n{}",
                body,
                answer,
                graph
            );
        }
    }

    /// What the branch layer cannot do, said out loud rather than left to
    /// be discovered.
    ///
    /// A rule is a local window and a branch's arms lie *between* its two
    /// ends, so no window holds both. Every law here is therefore stated at
    /// one end, which means a value is specialized where it reaches that
    /// end and **not inside an arm**: the `add` below keeps its operand
    /// however much the condition says about it. Reaching into an arm would
    /// need the fork's views to be conditional — they are plain copies, so
    /// a rule that rewrote one would be claiming something false of the
    /// graph as it stands.
    #[test]
    fn specializing_reaches_a_block_and_not_an_arm() {
        let (_terms, graph, spent) =
            settled("pick 0 pick 0 push 7 equal branch { push 1 add } { drop 0 push 0 }");
        assert!(!spent.contains(&Law::SpecializeEqual), "{:?}", spent);
        assert!(
            graph
                .live()
                .any(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Add))),
            "{}",
            graph
        );
    }

    // ---- the checker does not match ----

    /// The point of the split. A match is a claim about ports, and every
    /// way it can be false is decided by comparing ports — there is no
    /// searching in the checker to go wrong.
    #[test]
    fn a_match_that_does_not_fit_is_refused() {
        let (_terms, mut graph) = built("push 1 not");
        let push = only(&NodeKind::Op(Prim::Push(Value::Int(1))), &graph);
        let not = only(&NodeKind::Op(Prim::Not), &graph);

        let refuse = |graph: &mut Graph, step: &Step| match apply(graph, step) {
            Err(Error::NotThere { at, .. }) => at,
            other => panic!("accepted: {:?}", other.map(|_| ())),
        };

        // The right law and the wrong box.
        let step = Step {
            rule: Rule::IdElim { n: 1 },
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not],
                inputs: vec![Source::Port {
                    node: push,
                    port: 0,
                }],
                outputs: vec![vec![Sink::Output(0)]],
                branches: Vec::new(),
            },
        };
        assert_eq!(refuse(&mut graph, &step), Mismatch::Kind(not));

        // The right box, and an input port that reads something else.
        let step = Step {
            rule: Rule::DeadNode {
                kind: NodeKind::Op(Prim::Not),
            },
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not],
                inputs: vec![Source::Input(0)],
                outputs: Vec::new(),
                branches: Vec::new(),
            },
        };
        assert_eq!(
            refuse(&mut graph, &step),
            Mismatch::Edge(Sink::Port { node: not, port: 0 })
        );

        // The right box, and a reader the window does not export. This is
        // `dead-node`'s side condition doing its work: the `not` is read by
        // the boundary, so the window with nothing exported is not there.
        let step = Step {
            rule: Rule::DeadNode {
                kind: NodeKind::Op(Prim::Not),
            },
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not],
                inputs: vec![Source::Port {
                    node: push,
                    port: 0,
                }],
                outputs: Vec::new(),
                branches: Vec::new(),
            },
        };
        assert_eq!(
            refuse(&mut graph, &step),
            Mismatch::Readers(Source::Port { node: not, port: 0 })
        );

        // A boundary that points back inside the match: what it names is
        // the pattern plus a link, not the pattern.
        let step = Step {
            rule: Rule::Dedup {
                kind: NodeKind::Op(Prim::Not),
            },
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not, not],
                inputs: vec![Source::Port { node: not, port: 0 }],
                outputs: vec![vec![], vec![]],
                branches: Vec::new(),
            },
        };
        assert_eq!(refuse(&mut graph, &step), Mismatch::Shape);

        // And nothing above changed the graph.
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 2);
    }

    /// The matcher is partial exactly where a side does not pin its own
    /// match, and every one of those is a right-hand side that has to be
    /// *stated* rather than read: a graph with no boxes has nothing to
    /// anchor on, and a graph that exports one port twice leaves the split
    /// of that port's readers a choice.
    #[test]
    fn the_matcher_declines_where_a_side_pins_nothing() {
        let (_terms, graph) = built("push 1 push 2 add");
        for rule in [
            Rule::IdElim { n: 1 },
            Rule::SwapElim,
            Rule::CopyElim { n: 1 },
            Rule::DeadNode {
                kind: NodeKind::Op(Prim::Add),
            },
            Rule::Dedup {
                kind: NodeKind::Op(Prim::Add),
            },
        ] {
            let (_, rhs) = sides(&rule).unwrap();
            assert!(
                find(&graph, &rhs).is_empty(),
                "{:?} backward was matched anyway",
                rule.law()
            );
        }
        // `not-not` is the one right-hand side that is a box, and it reads
        // fine.
        let (_terms, graph) = built("as_bool");
        let (_, rhs) = sides(&Rule::NotNot).unwrap();
        assert_eq!(find(&graph, &rhs).len(), 1);
    }

    /// A backward step still *spends* the laws the matcher declines — it
    /// just has to say what it is spending, which is the whole point of the
    /// match carrying the split rather than deriving it.
    #[test]
    fn a_derivation_states_what_the_matcher_cannot_read() {
        let (_terms, mut graph) = built("not");
        let not = only(&NodeKind::Op(Prim::Not), &graph);
        // Put a `copy(1)` back in front of the boundary output: the right
        // side of `copy-elim` is one source exported twice, and here the
        // one source is the `not` and the two readers are invented.
        let step = Step {
            rule: Rule::CopyElim { n: 1 },
            dir: Direction::Backward,
            at: Match {
                nodes: Vec::new(),
                inputs: vec![Source::Port { node: not, port: 0 }],
                outputs: vec![vec![Sink::Output(0)], vec![]],
                branches: Vec::new(),
            },
        };
        let back = apply(&mut graph, &step).unwrap();
        graph.check().unwrap();
        let copy = only(&NodeKind::Copy(1), &graph);
        assert_eq!(graph.sources(copy), [Source::Port { node: not, port: 0 }]);
        assert_eq!(
            graph.outputs(),
            [Source::Port {
                node: copy,
                port: 0
            }]
        );

        // And forward again takes it straight back out.
        apply(&mut graph, &back).unwrap();
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 1);
        assert_eq!(graph.outputs(), [Source::Port { node: not, port: 0 }]);
    }

    // ---- derivations ----

    /// Rewriting a real program writes a derivation, the derivation replays
    /// against the graph it was written for, and it undoes.
    #[test]
    fn a_derivation_replays_and_undoes() {
        let (_terms, start) = built("pick 1 swap swap add dip { pick 0 }");
        let mut m = Meaning::default();
        let inputs = boundary(&mut m, start.arity().inputs);
        let was = eval_graph(&mut m, &start, &inputs);

        let mut here = start.clone();
        let run = saturate(&mut here, &structural());
        assert!(run.len() > 4, "there was structure to spend");
        here.check().unwrap();

        // Replaying the steps on the graph they were written for lands in
        // the same place. Ids are handed out in order, so it does.
        let mut again = start.clone();
        let steps: Vec<Step> = run.steps().cloned().collect();
        let twice = replay(&mut again, &steps).unwrap();
        again.check().unwrap();
        assert_eq!(again.live_count(), here.live_count());
        assert_eq!(
            eval_graph(&mut m, &again, &inputs),
            eval_graph(&mut m, &here, &inputs)
        );

        // And the run walks home. Not by flipping a bit on each step: every
        // box it puts back is a box the graph has not seen, so each undo
        // says the next one's match again in the ids it just handed out.
        twice.undo(&mut again).unwrap();
        again.check().unwrap();
        assert_eq!(again.live_count(), start.live_count());
        assert_eq!(eval_graph(&mut m, &again, &inputs), was);
    }

    /// The rebasing is not decoration: an undo that took each step's match
    /// at face value would name boxes that are not there.
    #[test]
    fn an_undo_names_the_boxes_the_undo_before_it_made() {
        let (_terms, start) = built("pick 1 swap swap add dip { pick 0 }");
        let mut graph = start.clone();
        let run = saturate(&mut graph, &structural());
        let stale: Vec<Step> = run
            .steps()
            .map(|s| Step {
                rule: s.rule.clone(),
                dir: s.dir,
                at: s.at.clone(),
            })
            .collect();
        // The forward steps replay, because the graph is the one they were
        // written against.
        let mut again = start.clone();
        replay(&mut again, &stale).unwrap();
        // A run built by hand out of the same steps still undoes, because
        // `push` records the inverse the graph actually handed back rather
        // than one worked out afterwards.
        let mut byhand = start.clone();
        let mut built_run = Derivation::default();
        for step in &stale {
            built_run.push(&mut byhand, step.clone()).unwrap();
        }
        built_run.undo(&mut byhand).unwrap();
        byhand.check().unwrap();
        assert_eq!(byhand.live_count(), start.live_count());
    }

    // ---- what the table settles ----

    /// The claim that the table is not merely a re-encoding of the four
    /// eliminations: after it drains, no two boxes compute the same thing.
    #[test]
    fn nothing_is_computed_twice() {
        let (_terms, mut graph) = built("pick 1 pick 1 add dip { pick 1 pick 1 add } add");
        saturate(&mut graph, &structural());
        graph.check().unwrap();
        let boxes: Vec<(NodeId, &NodeKind)> = graph.live().collect();
        for (i, (a, ka)) in boxes.iter().enumerate() {
            for (b, kb) in &boxes[i + 1..] {
                assert!(
                    !(ka == kb && graph.sources(*a) == graph.sources(*b)),
                    "{} and {} are one computation:\n{}",
                    a,
                    b,
                    graph
                );
            }
        }
        // The two halves of that sentence are the same sum of the same two
        // wires, so one `add` survives them both, and the outer one reads
        // it twice.
        let adds = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Add)))
            .count();
        assert_eq!(adds, 2, "{}", graph);
    }

    /// A branch's two views are not duplicates of each other, which is the
    /// fork earning its keep against the one rule that could delete it.
    #[test]
    fn dedup_leaves_a_branch_its_two_views() {
        let (_terms, mut graph) = built("branch { not } { not }");
        saturate(&mut graph, &structural());
        graph.check().unwrap();
        let nots = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Not)))
            .count();
        assert_eq!(nots, 2, "the arms were merged:\n{}", graph);
    }

    /// The corpus rewritten and walked home again. The load-bearing check
    /// on the rebasing: over a hundred real programs, each undone step
    /// naming boxes the step after it put back.
    #[test]
    fn the_corpus_walks_home() {
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        for (idx, term) in terms {
            let start = build(&arena, term);
            let mut graph = start.clone();
            let run = saturate(&mut graph, &structural());
            run.undo(&mut graph)
                .unwrap_or_else(|e| panic!("sentence {} does not undo: {}", library.names[idx], e));
            graph.check().unwrap_or_else(|e| {
                panic!(
                    "sentence {} undid into a torn graph: {}",
                    library.names[idx], e
                )
            });
            assert_eq!(
                graph.live_count(),
                start.live_count(),
                "sentence {} came back a different size",
                library.names[idx]
            );
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, start.arity().inputs);
            assert_eq!(
                eval_graph(&mut m, &graph, &inputs),
                eval_graph(&mut m, &start, &inputs),
                "sentence {} came back meaning something else",
                library.names[idx]
            );
        }
    }

    /// What `dedup` is worth, over the corpus: when the table drains, no
    /// two boxes left in it compute the same thing. This is the claim
    /// `super` used to list among the things it had not bought.
    #[test]
    fn nothing_in_the_corpus_is_computed_twice() {
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            saturate(&mut graph, &structural());
            let boxes: Vec<(NodeId, &NodeKind)> = graph.live().collect();
            for (i, (a, ka)) in boxes.iter().enumerate() {
                for (b, kb) in &boxes[i + 1..] {
                    assert!(
                        !(ka == kb && graph.sources(*a) == graph.sources(*b)),
                        "sentence {}: {} and {} are one computation",
                        library.names[idx],
                        a,
                        b
                    );
                }
            }
        }
    }

    /// The wiring half of the branch layer, over the corpus, judged by the
    /// opaque oracle — which can judge exactly these and none of the rest.
    ///
    /// This is the load-bearing soundness check on `fork-dedup`,
    /// `select-view` and `select-same`: over a hundred real programs, take
    /// every branch apart as far as the wiring allows and mean the same
    /// thing at the end.
    #[test]
    fn taking_branches_apart_preserves_meaning() {
        let laws: Vec<Law> = structural()
            .into_iter()
            .chain(branching())
            .filter(|&law| is_wiring(law))
            .collect();
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let before = eval_graph(&mut m, &graph, &inputs);
            saturate(&mut graph, &laws);
            graph
                .check()
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            assert_eq!(
                before,
                eval_graph(&mut m, &graph, &inputs),
                "the branch layer changed what sentence {} means",
                library.names[idx]
            );
        }
    }

    /// The whole table drains, and drains to a fixpoint.
    ///
    /// Not every law here shrinks the live box count the way [`structural`]'s
    /// all do — `select-view` and the two specializing rules re-point a link
    /// and leave the boxes where they are — so termination rests on a
    /// lexicographic measure rather than one number: blocks a fork supplies,
    /// then blocks that answer with a tested value, then boxes. This is what
    /// would catch that being wrong, by hanging or by firing again here.
    #[test]
    fn the_whole_table_drains() {
        let all = [structural(), branching()].concat();
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        for (idx, term) in terms {
            let mut graph = build(&arena, term);
            saturate(&mut graph, &all);
            let settled = graph.live_count();
            graph
                .check()
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            let again = saturate(&mut graph, &all);
            assert!(
                again.is_empty(),
                "sentence {} had {} more to spend",
                library.names[idx],
                again.len()
            );
            assert_eq!(graph.live_count(), settled);
        }
    }

    /// Every proposal the driver makes is one the checker takes, over every
    /// box of every sentence in the corpus. A matcher that drifts from the
    /// table says so here.
    #[test]
    fn every_proposal_is_accepted() {
        let (library, arena, terms) = crate::diagram2::tests::corpus();
        let laws = [structural(), branching()].concat();
        for (idx, term) in terms {
            let graph = build(&arena, term);
            for (id, _) in graph.live() {
                for step in propose(&graph, &laws, id) {
                    let mut copy = graph.clone();
                    let law = step.rule.law();
                    apply(&mut copy, &step).unwrap_or_else(|e| {
                        panic!(
                            "sentence {}: {:?} proposed and refused: {}",
                            library.names[idx], law, e
                        )
                    });
                    copy.check().unwrap_or_else(|e| {
                        panic!(
                            "sentence {}: a step left a torn graph: {}",
                            library.names[idx], e
                        )
                    });
                }
            }
        }
    }
}
