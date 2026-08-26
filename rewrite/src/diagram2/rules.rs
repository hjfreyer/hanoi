//! The table: each law a pair of graphs the module says are the same
//! program, and a rewrite the business of pointing at one and swapping in
//! the other.
//!
//! [`super`] builds a graph and stops there. It used to shrink one as well:
//! first by hand — a `match` on [`NodeKind`] that re-pointed ports directly
//! — and then by running this table to fixpoint. Both are gone. The
//! hand-written version said nothing: there was no page to read, and no way
//! to add a law without editing the engine. The fixpoint said too much:
//! *which* laws, *where*, and *in what order* is a strategy, and a strategy
//! belongs to whoever is proving something rather than to the module the
//! graph lives in. What is left here is the page — this module is the thing
//! `rewrite/src/rules.rs` was for terms, over graphs instead — and the
//! handful of operations a driver is built out of: [`sides`], [`find`],
//! [`propose`], [`apply`], [`replay`].
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
//!   sources are one box read twice. It refuses [`NodeKind::Select`]: a
//!   branch id is a name, and merging two selects would give one box two
//!   of them.
//! - [`Law::NotNot`] — `not ; not = as_bool`, a layer-3 law carried as the
//!   template for the rest. It is in the table and **not** in
//!   [`structural`], because the opaque-operation oracle the tests judge by
//!   reads `not(not(x))` and `as_bool(x)` as different symbols — this law is
//!   about what the machine computes, and `vm` is what measures it.
//!
//! ## The value layer, and the two rows no list drives
//!
//! [`folding`] is layer 3 of the sheet: what an operation *computes*, with
//! the machine itself as the judge — [`Law::Fold`] runs a literal window on
//! `vm`, and the rest are facts about particular instructions.
//!
//! Two of them are about a value the window watched being **built**, which
//! is a shape the window knows without asking the machine anything:
//! [`Law::AsTupleBuilt`] says coercing it changes nothing, and
//! [`Law::IsTupleBuilt`] says testing its width answers. The second is what
//! lets the compiler's `type` and `enum` guard be `pick 0 ; is_tuple n`
//! rather than a coercion compared against a copy — see
//! [docs/totality.md](../../../docs/totality.md), where that guard has now
//! shortened twice.
//!
//! Every row on that list **shrinks** a graph, which is what makes it a
//! list a driver can run to fixpoint. Two rows in the table are about the
//! same instructions and are deliberately on no list at all, because they
//! grow one:
//!
//! - [`Law::AsBoolBranch`] — `as_bool` is the branch it makes,
//!   `if x { true } else { false }`. The coercion *is*
//!   [`truthy`](bytecode::Value::truthy) and a `select` keeps the block
//!   `truthy` picks, so the two are one program by construction.
//! - [`Law::CoercionGuard`] — a coercion is a guarded identity, which is
//!   the instruction set's own sentence about all three of them: the value
//!   where its test holds, a default where it does not. For `as_tuple n`
//!   the test is `is_tuple n`, the width and all: a tuple of the wrong
//!   length is exactly what `untuple n` could not take apart, so the
//!   width-blind `is_tuple` would guard the wrong domain.
//!
//! These are **unpackings**, and what they buy is the direction of reading
//! the rest of the table cannot go: a coercion is opaque to every rule
//! that wants to know what a value *is*, and these put the test that
//! decides it into the graph where the branch layer and a `cases` split
//! can spend it. Which is also why no list carries them — whether to
//! unpack a coercion is a decision of the same kind `inline` is, so a
//! strategy names the one it wants.
//!
//! ## Which way a branch can grow
//!
//! [`Law::SelectHoist`] is another row no list drives, and it grows a
//! graph for a different reason: it duplicates a **region**, the way
//! [`Law::Shannon`] does, and carries it as payload for the same reason.
//! What it says is `select(C, T, E) ; A = select(C, T ; A, E ; A)` — the
//! commuting conversion, what runs *after* a branch runs inside whichever
//! arm the branch takes. Said as a composition on purpose: `select(…) ; A`
//! is the side condition as well as the shape, since a composition is
//! exactly the claim that the answers go into `A` and nowhere else. The
//! The gap it fills was always at the select. A branch's views are a
//! `copy`, so a branch grows *backwards* over what fed it for free —
//! `copy-elim` and `dedup` are all it takes. Nothing said anything at the
//! **select**, so a branch could never grow forwards: everything
//! downstream of one was out of the whole layer's reach, and a select
//! could be deleted but never moved.
//!
//! It is worth holding it against [`Law::Shannon`], since both put two
//! copies of a region under one branch and they are not the same row.
//! `shannon` *makes* a branch, out of a wire, by pinning that wire to
//! `true` in one copy and `false` in the other — which is why it is
//! refused on anything the instruction set does not promise is a bool,
//! since a third case would make the pin a lie. `select-hoist` makes no
//! branch and pins nothing: the branch is already there, its condition
//! wire is passed to the moved select untouched, and the only thing
//! assumed about that wire is the truthiness a select was reading anyway.
//! So it holds of **any** branch, whatever computed the condition, and
//! it holds of conditions no case split can reach.
//!
//! ## The branch layer, and the one place it stops
//!
//! [`branching`] is layer 2 of the sheet: [`Law::SelectConst`],
//! [`Law::SelectSame`], [`Law::SpecializeEqual`], [`Law::SpecializeBool`]
//! and [`Law::SpecializeChoice`]. Between them they fold a literal
//! condition into the blocks it chooses, delete a branch whose arms answer
//! alike, and write what a test decided into the block that tested it.
//!
//! `branch { A } { A } = drop-top ; A` is not among them and does not need
//! to be: it is `copy-elim`, then `dedup`, then `select-same`, then
//! `dead-node`.
//!
//! ### The discard is what a rule reasons from
//!
//! A rule is a local window, and a branch has one box in it — the select.
//! That is where every law of this layer is anchored, and it is the right
//! place for a reason that has nothing to do with convenience: the select
//! holds the **discard**, the fact that the untaken block is thrown away.
//! Reasoning from "the condition held" is sound exactly where the answer
//! that disagrees is discarded, so a rule that wants to say what a branch
//! decided has to hold the select and reach a **block**.
//!
//! It cannot reach *inside* an arm, and that is the honest boundary. An
//! arm's boxes are shared with the other arm wherever both read one value,
//! so there is no port to write an arm-local answer into. What reaches
//! inside an arm is making the arm's copy of the work its own first, which
//! is what [`Law::Shannon`] and [`Law::SelectHoist`] do — and then the
//! specializing rows fire on the copy.
//!
//! [`Law::SpecializeBool`] holds one box more than the branch: the
//! `as_bool` that made the condition. A bool is the one kind of condition
//! whose truthiness *is* its value, and having the coercion in the window
//! is how the rule says the condition is one. [`Law::PromisedBool`] is what
//! puts it there, which is the whole use of writing an instruction set's
//! promise down as a box. The rule then fires where one wire is both the
//! condition and a block — a pattern reading one boundary input twice,
//! which is how [`Law::SelectSame`] states its shared block too.
//!
//! [`Law::SpecializeChoice`] is the same shape one branch deeper: two
//! selects reading one condition, the outer one's blocks reading the
//! inner one's answers. The same value tested twice answers the same, and
//! the outer select's discard is what makes saying so sound.
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
use bytecode::{Instruction, Library, Value};

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
    AndLiteral,
    TupleCancel,
    AsTupleBuilt,
    EqualRefl,
    // The branch layer. Every one of these is stated at an end of a branch
    // that has the condition in its own window — see the module docs for why
    // that is the only place some of them can be stated soundly at all.
    SelectSame,
    SelectConst,
    SpecializeEqual,
    SpecializeBool,
    SpecializeChoice,
    Shannon,
    SelectHoist,
    // The value layer: what an operation computes, measured on the machine.
    PromisedBool,
    Fold,
    TestedBool,
    Retuple,
    AsTupleRoundTrip,
    IsTupleBuilt,
    // The two unpackings: a coercion said as the program it is. Both grow
    // a graph, so no list drives them — see [`folding`].
    AsBoolBranch,
    CoercionGuard,
}

impl Law {
    /// How the docs spell this law, which is also how a proof names it.
    ///
    /// One table, read both ways: [`crate::hant`] parses a law name by
    /// scanning [`every`](Law::every) law for the spelling that matches,
    /// so a law added to the enum is spellable in a `.hant` the moment it
    /// is named here, and a message that names a law and a proof that
    /// names one cannot drift apart.
    pub fn name(self) -> &'static str {
        match self {
            Law::IdElim => "id-elim",
            Law::SwapElim => "swap-elim",
            Law::CopyElim => "copy-elim",
            Law::DeadNode => "dead-node",
            Law::Dedup => "dedup",
            Law::NotNot => "not-not",
            Law::AndLiteral => "and-literal",
            Law::TupleCancel => "tuple-cancel",
            Law::AsTupleBuilt => "as-tuple-built",
            Law::EqualRefl => "equal-refl",
            Law::SelectSame => "select-same",
            Law::SelectConst => "select-const",
            Law::SpecializeEqual => "specialize-equal",
            Law::SpecializeBool => "specialize-bool",
            Law::SpecializeChoice => "specialize-choice",
            Law::Shannon => "shannon",
            Law::SelectHoist => "select-hoist",
            Law::PromisedBool => "promised-bool",
            Law::Fold => "fold",
            Law::TestedBool => "tested-bool",
            Law::Retuple => "retuple",
            Law::AsTupleRoundTrip => "as-tuple-round-trip",
            Law::IsTupleBuilt => "is-tuple-built",
            Law::AsBoolBranch => "as-bool-branch",
            Law::CoercionGuard => "coercion-guard",
        }
    }

    /// Every law there is, in the order the enum declares them.
    ///
    /// Not a list to *drive* — [`structural`], [`branching`] and
    /// [`folding`] are the lists a strategy spends, and `view-value` is
    /// held out of all three on purpose. This is the vocabulary: what a
    /// name can resolve to, and what a table of names is checked against.
    pub fn every() -> Vec<Law> {
        vec![
            Law::IdElim,
            Law::SwapElim,
            Law::CopyElim,
            Law::DeadNode,
            Law::Dedup,
            Law::NotNot,
            Law::AndLiteral,
            Law::TupleCancel,
            Law::AsTupleBuilt,
            Law::EqualRefl,
            Law::SelectSame,
            Law::SelectConst,
            Law::SpecializeEqual,
            Law::SpecializeBool,
            Law::SpecializeChoice,
            Law::Shannon,
            Law::SelectHoist,
            Law::PromisedBool,
            Law::Fold,
            Law::TestedBool,
            Law::Retuple,
            Law::AsTupleRoundTrip,
            Law::IsTupleBuilt,
            Law::AsBoolBranch,
            Law::CoercionGuard,
        ]
    }
}

impl fmt::Display for Law {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
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
    /// `and` with a literal operand is decided by `truthy` alone —
    /// short-circuiting, as an equation. A truthy literal contributes
    /// nothing but the coercion: the answer is `Bool(truthy(other))`,
    /// which is `as_bool` of the other operand. The one falsy value
    /// decides the whole answer: `false`, the other operand discarded —
    /// the discard licensed the way every discard here is, by totality
    /// and purity.
    ///
    /// The literal stays **exported** on both sides, the way
    /// [`Rule::Fold`] keeps its operands: a deduped literal is one box
    /// with many readers, and a window that claimed all of them would
    /// never match. A literal the `and` alone read is left reader-less,
    /// and `dead-node` collects it.
    ///
    /// This is the row that lets a case split spend a **conjunction**: a
    /// guard `and(a, b)` branch-tested as one opaque bool decomposes only
    /// when a split on `a` can fold the `and` its literal leaves behind.
    ///
    /// `literal` names the operand the pushed value feeds — the payload
    /// carries which, so the two sides of the equation agree on where the
    /// boundary input sits.
    AndLiteral { literal: Side, value: Value },
    /// Taking apart what `tuple n` built answers the built elements:
    /// `tuple n ; untuple n = id(n)` — the algebra sheet's tuple
    /// cancellation, stated with the tuple **kept**, since its port may
    /// have other readers: the equation re-points the untuple's readers
    /// at the element wires and leaves the tuple standing for whoever
    /// else holds it; a tuple nobody else reads falls to `dead-node`.
    /// The machine's promise that `untuple` inverts `tuple` exactly is
    /// what makes this a row rather than wiring.
    TupleCancel { n: usize },
    /// The coercion is a no-op on a value `tuple n` built: `tuple n ;
    /// as_tuple n` answers the tuple itself. This is the witness a shape
    /// guard spends when it reads a built value — the guard's `as_tuple`
    /// collapses onto the built wire, and the comparison against it
    /// becomes a comparison of one wire with itself.
    AsTupleBuilt { n: usize },
    /// `equal` on one wire read twice is `true`: `equal` is structural
    /// identity and the language is deterministic and pure, so a value
    /// compared with itself answers yes. The wire itself is a boundary
    /// input — its other readers never entered the window — and the
    /// answer side leaves it unread, the discard totality licenses. The
    /// candidate law the algebra sheet names `equal_refl`.
    EqualRefl,

    // ---- the branch layer ----
    /// A block a `select` answers with either way is what it answers: `if c
    /// then x else x = x`. The select keeps its other blocks and narrows by
    /// one.
    SelectSame { arity: usize, at: usize },
    /// β: a literal condition and the select is the blocks it chooses.
    ///
    /// It carries no arms. A branch has one box, so folding it strands
    /// nothing — the arm the literal did not choose becomes work nobody
    /// reads, which is [`Law::DeadNode`]'s to collect, not this rule's to
    /// hold in its window.
    ///
    /// Sound on **every** value and not only on booleans, because `truthy`
    /// is total: `false` is the one falsy value and everything else takes
    /// the then blocks.
    ///
    /// `lit_blocks` names the block positions (over `2n`) that read the
    /// **literal itself** — the shape a `dedup` makes when the condition
    /// and an answer are one pushed value — because a boundary input may
    /// not stand for a port inside the window.
    SelectConst {
        value: Value,
        arity: usize,
        lit_blocks: Vec<usize>,
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
    /// The very value a branch tested, when it is a **bool**, is what the
    /// branch decided: `true` in the then block, `false` in the else block.
    /// A truthy bool is `true` and a falsy one is `false` — there is
    /// nothing else for it to be — so both halves are exact.
    ///
    /// The window says its side condition rather than testing it: **one
    /// box is read twice**, as the select's condition and as block `at`.
    /// That is the same trick [`Rule::SelectSame`] uses for its shared
    /// block, and it is what makes "this block *is* the condition" a fact
    /// about the pattern instead of a comparison some search has to get
    /// right.
    ///
    /// The **`as_bool` is in the window too**, and it is the other half of
    /// the claim: it is where the condition is made, and its being there is
    /// what says the condition is a bool. Without it the rule would be
    /// false — a condition of `5` is truthy, and the then block would read
    /// `5` rather than `true`. [`Law::PromisedBool`] is what puts it there,
    /// writing the promise on the op that made the answer, so this rule
    /// fires on exactly what that law leaves.
    ///
    /// `at` is the select's block over the whole `2n`; `at < arity` is the
    /// then side, and so decides which literal this folds to.
    SpecializeBool { arity: usize, at: usize },
    /// A branch **inside an arm** whose condition is a view of the very
    /// value the outer branch tested is already decided: its then blocks in
    /// the outer then arm, its else blocks in the outer else arm — the same
    /// value tested twice answers the same, and `false` is the one falsy
    /// value.
    ///
    /// [`Rule::SpecializeBool`] with the inner `select` where the `as_bool`
    /// was, and the same window for the same reason: one wire is read
    /// twice — as both selects' condition — and the outer select holds the
    /// discard that makes reasoning from "the condition held" sound. The
    /// inner select stays; only the outer blocks that read its answers come
    /// to read the blocks it would choose.
    ///
    /// `inner` is the inner select's arity and `moves` pairs an inner
    /// output with the outer block that reads it (over `m` and `2n`). Which
    /// side is not a field: the blocks the moves name say it, and they must
    /// all name the one side.
    SpecializeChoice {
        arity: usize,
        inner: usize,
        moves: Vec<(usize, usize)>,
    },
    /// Case analysis, as an equation: a wire the instruction set promises
    /// is a bool is `true` or it is `false` — there is no third case — so
    /// everything downstream of it equals a branch holding one copy per
    /// case, the assumed answer pasted in as a literal:
    /// `body(w) = if w then body(true) else body(false)`. Shannon
    /// expansion (η, in the literature), and the one law that *grows* a
    /// graph on purpose: the case split the old engine kept as its pinned
    /// boundary, stated as a pair of graphs like every other row.
    ///
    /// `kind` is the operation whose answer is split on — refused unless
    /// [`yields_bool`](bytecode::Instruction::yields_bool) promises it —
    /// and `body` is the region downstream of that answer, carried as
    /// payload the way [`Rule::SelectHoist`] carries its own: its input 0
    /// is the answer, the rest is whatever else the region reads. The
    /// right side runs both pinned copies and keeps one with a `select`,
    /// which is sound for the reason every branch is — total, pure, the
    /// untaken copy an answer nobody reads.
    ///
    /// No law list collects this row. Expanding is a *strategy's* act —
    /// it spends η where a proof says to — and the `cases` proof step is
    /// what fires it; a driver that expanded on its own would never
    /// terminate, since the expansion re-creates the shape it fires on.
    Shannon { kind: NodeKind, body: Graph },
    /// The commuting conversion, as an equation: what runs **after** a
    /// branch runs inside whichever arm the branch takes.
    ///
    /// ```text
    /// select(C, T, E) ; A  =  select(C, T ; A, E ; A)
    /// ```
    ///
    /// Written as a composition, which is the half of the statement that
    /// is usually left to prose: `select(…) ; A` says the answers go into
    /// `A` and nowhere else, and that is exactly the side condition, said
    /// where it cannot be forgotten. `A` may read wires that are not
    /// answers, so in full it is `(select(C, T, E) * id(k)) ; A`, and `k`
    /// is what `body` carries past the answers.
    ///
    /// A branch grows *backwards* over what fed it for free: its views are
    /// a `copy`, so `copy-elim` and `dedup` do it. Nothing said anything at
    /// the select's end, so a branch could never grow **forwards**:
    /// everything downstream of a select was beyond the reach of the whole
    /// branch layer, and a select could only ever be got rid of, never
    /// moved. This is that row.
    ///
    /// `arity` is the select's width `n` and `body` is `A` — the region
    /// downstream of the answers, carried as payload the way
    /// [`Rule::Shannon`] carries its own. Its inputs `0..n` are the
    /// answers, its inputs `n..n+k` are the `id(k)` alongside them, and
    /// its outputs are what the region leaves.
    ///
    /// **Nothing is pinned**, and that is the whole difference from
    /// [`Rule::Shannon`]. Shannon pastes `true` and `false` into its
    /// copies, which is only sound because
    /// [`yields_bool`](bytecode::Instruction::yields_bool) promises the
    /// wire is a bool and so has no third case. Here the condition wire is
    /// untouched — the same value governs the select on either side of the
    /// equation — so nothing is assumed about it beyond the truthiness a
    /// select reads, and **any** branch splits, whatever made its
    /// condition. Running both copies and keeping one is the licence every
    /// branch spends: total, pure, the untaken copy an answer nobody
    /// reads.
    ///
    /// The side condition is carried by the interface rather than tested:
    /// the left side exports `body`'s outputs and never the select's
    /// answers, so the fullness clause of `check_match` forces every
    /// answer to be read *inside* the window. It has to — the select is
    /// gone on the right, and there would be nothing left to export them
    /// from. An answer the host boundary reads is not stranded by that:
    /// `downstream_of` hands it back as one of `body`'s own outputs,
    /// passed straight through, and the new select chooses between the
    /// blocks it chose between before.
    ///
    /// Like [`Rule::Shannon`] and the two unpackings, it **grows** a
    /// graph, so no list drives it and a proof names where to spend it.
    SelectHoist { arity: usize, body: Graph },

    // ---- the value layer ----
    /// An operation on literal operands is the answer the machine gives:
    /// the fold, run on the machine itself so there is no second semantics
    /// to drift. [`sides`] executes the window and **builds** the answer
    /// side from what came back — a payload does not carry an answer it
    /// could lie about.
    ///
    /// `operands` are the distinct literals in the window and `reads[i]`
    /// names the one the operation's input `i` reads — said the way
    /// [`Rule::Fold`] says its reads, so one literal read twice (`equal`
    /// after a `dedup`) is one box in the pattern.
    Fold {
        prim: Prim,
        operands: Vec<Value>,
        reads: Vec<usize>,
    },
    /// An answer the instruction set promises is a bool is that answer with
    /// the promise **written down**: `op` is `op ; as_bool`, whenever
    /// [`yields_bool`](bytecode::Instruction::yields_bool) holds of `op`.
    ///
    /// `as_bool` *is* `truthy` made into an instruction, so on a value that
    /// is already a bool it is the identity and the equation is exact. What
    /// it buys is that the promise stops being a fact about the instruction
    /// set and becomes a **box**: a type assertion manifested in the graph,
    /// standing where any rule can see it.
    ///
    /// [`Rule::SpecializeBool`] is the rule that needs it. It says what a
    /// branch decided about the value it tested, and it says it of an
    /// `as_bool` on the condition — the coercion being how an arbitrary
    /// truthy value becomes the bool the branch settled. A
    /// condition that is *already* a bool carries no coercion, so the rule
    /// cannot see it. Spending this law first puts one there.
    ///
    /// Nothing about the equation needs a side condition: it is true of a
    /// promised bool however many `as_bool`s already stand on it. Not
    /// re-proposing it forever is [`propose`]'s business, and search is
    /// where a termination argument belongs.
    PromisedBool { kind: NodeKind },
    /// `is_bool` of an answer the instruction set promises is a bool is
    /// `true`, and the answer itself is untouched: `op ; is_bool` on one
    /// wire is `op` and `push true` side by side. The promise is
    /// [`yields_bool`](bytecode::Instruction::yields_bool), measured by
    /// `vm`; the answer stays exported, so the window does not care who
    /// else reads it.
    TestedBool { kind: NodeKind },
    /// Rebuilding what `untuple n` took apart is the coercion, not the
    /// identity — the slots may have been junk-filled: `untuple n ; tuple
    /// n = as_tuple n`, whole or not at all.
    Retuple { n: usize },
    /// A value already coerced survives the round trip: `as_tuple n ;
    /// untuple n ; tuple n = as_tuple n`.
    ///
    /// [`Rule::Retuple`] says the round trip *is* the coercion; this says
    /// the coercion is **stable** under it, which is the fact a guard
    /// spends. `as_tuple n` leaves a tuple of exactly `n` elements on every
    /// input — that is its codomain, and the whole of why it exists — so
    /// taking that apart and putting it back answers the very value it
    /// started from.
    ///
    /// Not derivable from the two rows next to it, though it looks it:
    /// `retuple` turns the tail into a second `as_tuple n`, and the table
    /// has no idempotence row to collapse the pair. Stating it whole is
    /// also what keeps the window honest — the parts are **not** exported,
    /// so the rule declines a round trip something else reads into.
    ///
    /// The coercion's own port *is* exported, on both sides, the way
    /// [`Rule::AsTupleBuilt`] exports its tuple: it may have other readers,
    /// and a window that claimed all of them would rarely match.
    AsTupleRoundTrip { n: usize },
    /// Asking a value `tuple m` built whether it is a tuple of width `n`
    /// is asking whether `m` is `n`: `tuple m ; is_tuple n` = `tuple m ;
    /// push (m == n)`.
    ///
    /// The sibling of [`Rule::AsTupleBuilt`], and it exists for the same
    /// reason: a value the window watched being built has a shape the
    /// window knows, so a test of that shape is decided rather than
    /// computed. `as-tuple-built` says the coercion changes nothing; this
    /// says the test answers, and both keep the tuple **exported**, since
    /// its port may have readers the window never held.
    ///
    /// Both widths ride in the payload rather than one, because both cases
    /// are useful and neither is harder than the other: the equal widths
    /// answer `true`, and a mismatch answers `false` — which is the whole
    /// of what `is_tuple n` computes on a value whose width is known.
    ///
    /// This is the row the `type` and `enum` sugar's guard needs. That
    /// guard used to coerce a copy and compare it, which handed the
    /// rewriter an `equal` the folding rows could take apart; asked as
    /// `pick 0 ; is_tuple n` it hands over a test instead, and without
    /// this row a built tuple meeting one is a question nothing decides.
    IsTupleBuilt { built: usize, asked: usize },
    /// `as_bool` is the branch it is: `as_bool x = if x { true } else
    /// { false }`.
    ///
    /// [`Instruction::AsBool`](bytecode::Instruction::AsBool) is
    /// [`truthy`](bytecode::Value::truthy) made into an instruction, and a
    /// `select` keeps the block `truthy` says — so the two are the same
    /// program by construction, with the arms answering the two values
    /// `truthy` can report. Nothing is read inside either arm, so the
    /// branch needs no views at all.
    ///
    /// This is the unpacking that puts a *decision* where a coercion
    /// stood, which is what a proof about the two cases of a truthiness
    /// test needs: after it, the ordinary branch layer can specialize each
    /// arm, and `select-const` can fold the branch away wherever
    /// the condition turns out to be a literal.
    ///
    /// [`Rule::CoercionGuard`] unpacks the same box a different way — as
    /// the guarded identity every coercion is. Both are true, they answer
    /// different questions, and which one a proof wants is the proof's to
    /// say.
    AsBoolBranch,
    /// A coercion is a guarded identity: `as_T x = if x is a T { x } else
    /// { junk }`.
    ///
    /// The instruction set says it in prose —
    /// [each coercion](bytecode::Instruction::AsTuple) "is the identity
    /// where the value is already of that type, and hands back a default
    /// where it is not" — and this is that sentence as an equation. The
    /// payload is which coercion, and everything else is read off it: the
    /// test that guards it, and the default it hands back.
    ///
    /// | `prim` | guard | junk |
    /// |---|---|---|
    /// | `as_bool` | `is_bool` | `true` — every non-bool is truthy, `false` being the one falsy value and a bool |
    /// | `as_int` | `is_int` | `0` |
    /// | `as_tuple n` | `is_tuple n` | a tuple of `n` empty tuples |
    ///
    /// The width in that guard is not decoration, and it is why
    /// [`IsTuple`](bytecode::Instruction::IsTuple) carries one. The width
    /// is part of the type coerced to: a tuple of the wrong length is
    /// exactly what `untuple n` could not take apart, so a guard of the
    /// width-blind `is_tuple` would claim `as_tuple 2` is the identity on
    /// `(1, 2, 3)`, which it is not. Asked with the width, the equation is
    /// one box against one box on either side of the branch.
    ///
    /// Like [`Rule::AsBoolBranch`], this **grows** a graph, and it is on no
    /// driven list for that reason. What it is for is the other direction
    /// of reading: a coercion is opaque to every rule that wants to know
    /// what a value *is*, and this puts the test that decides it into the
    /// graph where a case split can spend it.
    CoercionGuard { prim: Prim },
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
            Rule::AndLiteral { .. } => Law::AndLiteral,
            Rule::TupleCancel { .. } => Law::TupleCancel,
            Rule::AsTupleBuilt { .. } => Law::AsTupleBuilt,
            Rule::EqualRefl => Law::EqualRefl,
            Rule::SelectSame { .. } => Law::SelectSame,
            Rule::SelectConst { .. } => Law::SelectConst,
            Rule::SpecializeEqual { .. } => Law::SpecializeEqual,
            Rule::SpecializeBool { .. } => Law::SpecializeBool,
            Rule::SpecializeChoice { .. } => Law::SpecializeChoice,
            Rule::Shannon { .. } => Law::Shannon,
            Rule::SelectHoist { .. } => Law::SelectHoist,
            Rule::Fold { .. } => Law::Fold,
            Rule::PromisedBool { .. } => Law::PromisedBool,
            Rule::TestedBool { .. } => Law::TestedBool,
            Rule::Retuple { .. } => Law::Retuple,
            Rule::AsTupleRoundTrip { .. } => Law::AsTupleRoundTrip,
            Rule::IsTupleBuilt { .. } => Law::IsTupleBuilt,
            Rule::AsBoolBranch => Law::AsBoolBranch,
            Rule::CoercionGuard { .. } => Law::CoercionGuard,
        }
    }
}

/// The wiring laws: everything true of the wiring alone, which is layer 1 of
/// the algebra sheet and nothing else.
///
/// `DeadNode` leads because it is the cheapest test and because a dead box
/// should go before anything bothers looking inside it — advice to a driver
/// that takes the first proposal it is offered, not a promise this module
/// keeps.
pub fn structural() -> Vec<Law> {
    vec![
        Law::DeadNode,
        Law::IdElim,
        Law::SwapElim,
        Law::CopyElim,
        Law::Dedup,
    ]
}

/// The branch layer: the laws stated at a branch's one end.
///
/// Kept out of [`structural`], for the reason [`Law::NotNot`] is kept out of
/// it. Every one of these turns on what an operation *computes* — which
/// values are truthy, that `equal` is identity, that `as_bool` is `truthy` —
/// except [`Law::SelectSame`], which is here rather than in [`structural`]
/// because it takes a branch apart, and a rewriter that dissolves every
/// branch it can is a strategy, which this module does not decide.
///
/// This list used to be nine and is five, and what went was the price of
/// the `fork`: `select-view` pulled a block out from behind one,
/// `fork-hoist` and `fork-dedup` moved work across one, and `select-literal`
/// held a whole branch so as never to strand one. A branch's views are a
/// plain [`NodeKind::Copy`] now, so `copy-elim` and `dedup` do that work
/// and the ordering hazard those four had between them is gone with them.
///
/// [`Law::SelectHoist`] is a branch law and is **not** here, for the reason
/// the unpackings are not in [`folding`]: it grows a graph. A driver run to
/// fixpoint over it would push every branch past everything downstream of
/// it, duplicating the lot — which is sometimes exactly what a proof wants
/// and never what a cleanup pass does. A strategy names it.
pub fn branching() -> Vec<Law> {
    vec![
        Law::SelectConst,
        Law::SelectSame,
        Law::SpecializeEqual,
        Law::SpecializeBool,
        Law::SpecializeChoice,
    ]
}

/// The value layer: what an operation computes, measured on the machine.
/// [`Law::NotNot`] is its elder — stated before the layer had a name — and
/// is listed with it.
///
/// Every row here **shrinks** a graph, which is what makes the list one a
/// driver can run to fixpoint. That is why [`Law::AsBoolBranch`] and
/// [`Law::CoercionGuard`] are not on it: they unpack a coercion into the
/// program it is, so they grow one, and *whether to spend an unpacking* is
/// a strategy in a way that folding a computation is not. They are named
/// by name — `fire(coercion-guard)`, `at(#7, as-bool-branch)` — and a
/// driver that wanted them could list them itself.
pub fn folding() -> Vec<Law> {
    vec![
        Law::Fold,
        Law::TestedBool,
        // The longer window first: both are read off the same `tuple` box,
        // and `retuple` alone would turn a round trip that began at a
        // coercion into two coercions the table has no row to collapse.
        Law::AsTupleRoundTrip,
        Law::Retuple,
        Law::IsTupleBuilt,
        Law::NotNot,
        Law::AndLiteral,
        Law::TupleCancel,
        Law::AsTupleBuilt,
        Law::EqualRefl,
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
        Law::NotNot
            | Law::AndLiteral
            | Law::TupleCancel
            | Law::AsTupleBuilt
            | Law::EqualRefl
            | Law::PromisedBool
            | Law::SelectConst
            | Law::SpecializeEqual
            | Law::SpecializeBool
            | Law::SpecializeChoice
            | Law::Shannon
            | Law::SelectHoist
            | Law::Fold
            | Law::TestedBool
            | Law::Retuple
            | Law::AsTupleRoundTrip
            | Law::IsTupleBuilt
            | Law::AsBoolBranch
            | Law::CoercionGuard
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
            // A branch id is a name, and merging two selects would give
            // one box two of them — which `Graph::check` refuses, so the
            // rule refuses to state it.
            if matches!(kind, NodeKind::Select { .. }) {
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
        Rule::AndLiteral { literal, value } => {
            let mut long = Graph::empty(1);
            let lit = long.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
            let operands = match literal {
                Side::Deep => vec![lit[0], Source::Input(0)],
                Side::Top => vec![Source::Input(0), lit[0]],
            };
            let and = long.add(NodeKind::Op(Prim::And), operands);
            long.close(vec![lit[0], and[0]]);

            // The answer is `truthy`'s verdict on the literal, measured on
            // the value itself: truthy leaves the other operand's
            // coercion, the one falsy value leaves `false` and the other
            // operand unread.
            let mut short = Graph::empty(1);
            let lit = short.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
            let answer = if value.truthy() {
                short.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)])
            } else {
                short.add(NodeKind::Op(Prim::Push(Value::Bool(false))), Vec::new())
            };
            short.close(vec![lit[0], answer[0]]);

            (long, short)
        }
        Rule::TupleCancel { n } => {
            let n = *n;
            let elements: Vec<Source> = (0..n).map(Source::Input).collect();

            let mut long = Graph::empty(n);
            let tuple = long.add(NodeKind::Op(Prim::Tuple(n)), elements.clone());
            let apart = long.add(NodeKind::Op(Prim::Untuple(n)), tuple.clone());
            let mut out = tuple.clone();
            out.extend(apart);
            long.close(out);

            let mut short = Graph::empty(n);
            let tuple = short.add(NodeKind::Op(Prim::Tuple(n)), elements.clone());
            let mut out = tuple;
            out.extend(elements);
            short.close(out);

            (long, short)
        }
        Rule::AsTupleBuilt { n } => {
            let n = *n;
            let elements: Vec<Source> = (0..n).map(Source::Input).collect();

            let mut long = Graph::empty(n);
            let tuple = long.add(NodeKind::Op(Prim::Tuple(n)), elements.clone());
            let coerced = long.add(NodeKind::Op(Prim::AsTuple(n)), tuple.clone());
            long.close(vec![tuple[0], coerced[0]]);

            let mut short = Graph::empty(n);
            let tuple = short.add(NodeKind::Op(Prim::Tuple(n)), elements);
            short.close(vec![tuple[0], tuple[0]]);

            (long, short)
        }
        Rule::EqualRefl => {
            let mut long = Graph::empty(1);
            let same = long.add(
                NodeKind::Op(Prim::Equal),
                vec![Source::Input(0), Source::Input(0)],
            );
            long.close(same);

            let mut short = Graph::empty(1);
            let yes = short.add(NodeKind::Op(Prim::Push(Value::Bool(true))), Vec::new());
            short.close(yes);

            (long, short)
        }

        // ---- the branch layer ----
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
        Rule::SelectConst {
            value,
            arity,
            lit_blocks,
        } => {
            let n = *arity;
            let mut named = lit_blocks.clone();
            named.sort_unstable();
            named.dedup();
            if n == 0 || named.len() != lit_blocks.len() || named.iter().any(|&b| b >= 2 * n) {
                return Err(ill(Ill::Refused));
            }
            let width = 2 * n - lit_blocks.len();
            let outside: Vec<usize> = (0..2 * n).filter(|b| !named.contains(b)).collect();
            let source = |lit: Source, b: usize| {
                if named.contains(&b) {
                    lit
                } else {
                    let idx = outside.iter().position(|&o| o == b).expect("one or other");
                    Source::Input(idx)
                }
            };

            let mut both = Graph::empty(width);
            let lit = both.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new())[0];
            let branch = both.next_branch();
            let mut takes = vec![lit];
            takes.extend((0..2 * n).map(|b| source(lit, b)));
            let mut out = both.add(NodeKind::Select { arity: n, branch }, takes);
            out.push(lit);
            both.close(out);

            let taken = value.truthy();
            let mut chosen = Graph::empty(width);
            let lit = chosen.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new())[0];
            // The branch id is skipped, not reused: the equation's two
            // sides share a namespace, and this side has no select.
            chosen.next_branch();
            let mut out: Vec<Source> = (0..n)
                .map(|j| source(lit, if taken { j } else { n + j }))
                .collect();
            out.push(lit);
            chosen.close(out);

            (both, chosen)
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
        Rule::SpecializeBool { arity, at } => {
            let (n, b) = (*arity, *at);
            if n == 0 || b >= 2 * n {
                return Err(ill(Ill::Refused));
            }
            // The block is on the then side exactly when it is in the first
            // half, and that is what the branch decided about the condition.
            let decided = Value::Bool(b < n);
            // The coercion's answer is the condition **and** the block, said
            // by the pattern reading one box twice rather than by a test —
            // the trick `select-same` uses for its shared block. The
            // coercion being in the window is what says the condition is a
            // bool, which is the whole of why a truthy condition may be read
            // as `true`.
            let block = |other: usize| Source::Input(1 + if other < b { other } else { other - 1 });
            let width = 2 * n;

            let build = |folded: bool| {
                let mut g = Graph::empty(width);
                let coerced = g.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)])[0];
                let branch = g.next_branch();
                let known = if folded {
                    g.add(NodeKind::Op(Prim::Push(decided.clone())), Vec::new())[0]
                } else {
                    coerced
                };
                let mut takes = vec![coerced];
                takes.extend((0..2 * n).map(|other| if other == b { known } else { block(other) }));
                let answers = g.add(NodeKind::Select { arity: n, branch }, takes);
                // The coercion stays readable from outside.
                let mut out = vec![coerced];
                out.extend(answers);
                g.close(out);
                g
            };
            (build(false), build(true))
        }
        Rule::SpecializeChoice {
            arity,
            inner,
            moves,
        } => {
            let (n, m) = (*arity, *inner);
            let mut taken: Vec<usize> = moves.iter().map(|&(_, b)| b).collect();
            taken.sort_unstable();
            taken.dedup();
            // Which side is not a payload field: the blocks the moves name
            // say it, and they must all name the one side — a move on the
            // other side is a different equation and the rule refuses to
            // state two at once.
            let Some(&(_, first)) = moves.first() else {
                return Err(ill(Ill::Refused));
            };
            let then = first < n;
            if n == 0
                || m == 0
                || taken.len() != moves.len()
                || moves
                    .iter()
                    .any(|&(j, b)| j >= m || b >= 2 * n || (b < n) != then)
            {
                return Err(ill(Ill::Refused));
            }
            // Boundary input 0 is the condition of **both** selects — one
            // input read twice, which is the side condition said in the
            // pattern rather than tested. Then the inner select's blocks,
            // then the outer blocks no move covers.
            let iblock = |k: usize| Source::Input(1 + k);
            let outside: Vec<usize> = (0..2 * n).filter(|b| !taken.contains(b)).collect();
            let width = 1 + 2 * m + 2 * n - moves.len();

            let build = |folded: bool| {
                let mut g = Graph::empty(width);
                let branch = g.next_branch();
                let within = g.next_branch();
                let mut takes = vec![Source::Input(0)];
                takes.extend((0..2 * m).map(iblock));
                let chosen = g.add(
                    NodeKind::Select {
                        arity: m,
                        branch: within,
                    },
                    takes,
                );
                let mut takes = vec![Source::Input(0)];
                takes.extend((0..2 * n).map(|b| {
                    match moves.iter().find(|&&(_, at)| at == b) {
                        // The block the move covers: the inner select's
                        // answer, or — folded — the block that answer is,
                        // read straight.
                        Some(&(j, _)) if folded => iblock(if then { j } else { m + j }),
                        Some(&(j, _)) => chosen[j],
                        None => {
                            let idx = outside.iter().position(|&o| o == b).expect("one or other");
                            Source::Input(1 + 2 * m + idx)
                        }
                    }
                }));
                let answers = g.add(NodeKind::Select { arity: n, branch }, takes);
                // The inner select stays, and stays readable from outside.
                let mut out = chosen;
                out.extend(answers);
                g.close(out);
                g
            };
            (build(false), build(true))
        }
        Rule::Shannon { kind, body } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            if prim.arity().outputs != 1
                || !prim.to_instruction().yields_bool()
                || body.arity().inputs == 0
            {
                return Err(ill(Ill::Refused));
            }
            body.check().map_err(|e| ill(Ill::Broken(e)))?;
            let n = prim.arity().inputs;
            let k = body.arity().inputs - 1;
            let m = body.arity().outputs;
            let outside: Vec<Source> = (0..k).map(|i| Source::Input(n + i)).collect();
            let handed: Vec<Source> = (0..n).map(Source::Input).collect();

            let mut asked = Graph::empty(n + k);
            let answer = asked.add(kind.clone(), handed.clone());
            let mut takes = vec![answer[0]];
            takes.extend(outside.iter().copied());
            let mut out = implant(&mut asked, body, &takes);
            out.push(answer[0]);
            asked.close(out);

            let mut split = Graph::empty(n + k);
            let answer = split.add(kind.clone(), handed);
            // Both copies run — the totality license every branch spends —
            // and the copy whose pin disagrees with the answer is the one
            // the select throws away.
            let copy = |split: &mut Graph, value: bool| {
                let lit = split.add(NodeKind::Op(Prim::Push(Value::Bool(value))), Vec::new());
                let mut takes = vec![lit[0]];
                takes.extend(outside.iter().copied());
                implant(split, body, &takes)
            };
            let sure = copy(&mut split, true);
            let doubted = copy(&mut split, false);
            let branch = split.next_branch();
            let mut chooses = vec![answer[0]];
            chooses.extend(sure);
            chooses.extend(doubted);
            let mut out = split.add(NodeKind::Select { arity: m, branch }, chooses);
            out.push(answer[0]);
            split.close(out);

            (asked, split)
        }
        Rule::SelectHoist { arity, body } => {
            let n = *arity;
            if n == 0 || body.arity().inputs < n || body.arity().outputs == 0 {
                return Err(ill(Ill::Refused));
            }
            body.check().map_err(|e| ill(Ill::Broken(e)))?;
            let k = body.arity().inputs - n;
            let m = body.arity().outputs;
            // The condition, the two blocks of every answer, and whatever
            // the region reads that is not an answer.
            let width = 1 + 2 * n + k;
            let outside: Vec<Source> = (0..k).map(|i| Source::Input(1 + 2 * n + i)).collect();
            let block =
                |side: bool| move |i: usize| Source::Input(1 + if side { i } else { n + i });
            let feeds = |blocks: Vec<Source>| {
                let mut takes = blocks;
                takes.extend(outside.iter().copied());
                takes
            };

            let mut chosen = Graph::empty(width);
            // The branch is minted first on both sides, so index 0 names
            // *this* branch on either — which is what carries the host's
            // own branch across the rewrite rather than minting a new one.
            // A select is where a branch ends, and this row moves that end
            // without ending a different branch.
            let branch = chosen.next_branch();
            let mut takes = vec![Source::Input(0)];
            takes.extend((0..n).map(block(true)));
            takes.extend((0..n).map(block(false)));
            let answers = chosen.add(NodeKind::Select { arity: n, branch }, takes);
            let out = implant(&mut chosen, body, &feeds(answers));
            chosen.close(out);

            let mut hoisted = Graph::empty(width);
            let branch = hoisted.next_branch();
            let sure = implant(
                &mut hoisted,
                body,
                &feeds((0..n).map(block(true)).collect()),
            );
            let doubted = implant(
                &mut hoisted,
                body,
                &feeds((0..n).map(block(false)).collect()),
            );
            let mut chooses = vec![Source::Input(0)];
            chooses.extend(sure);
            chooses.extend(doubted);
            let out = hoisted.add(NodeKind::Select { arity: m, branch }, chooses);
            hoisted.close(out);

            (chosen, hoisted)
        }

        // ---- the value layer ----
        Rule::Fold {
            prim,
            operands,
            reads,
        } => {
            let arity = prim.arity();
            if matches!(prim, Prim::Push(_) | Prim::Swap)
                || arity.inputs == 0
                || reads.len() != arity.inputs
                || operands.is_empty()
                || reads.iter().any(|&r| r >= operands.len())
                || !(0..operands.len()).all(|i| reads.contains(&i))
            {
                return Err(ill(Ill::Refused));
            }
            // The machine is the fold: the window runs on `vm` itself, so
            // the answer side is *built from the answer* rather than
            // carried by a payload that could lie about it.
            let window: Vec<Value> = reads.iter().map(|&r| operands[r].clone()).collect();
            let Some(answers) = run_window(&window, &prim.to_instruction()) else {
                return Err(ill(Ill::Refused));
            };
            if answers.len() != arity.outputs {
                return Err(ill(Ill::Refused));
            }

            let mut long = Graph::empty(0);
            let held: Vec<Source> = operands
                .iter()
                .map(|v| long.add(NodeKind::Op(Prim::Push(v.clone())), Vec::new())[0])
                .collect();
            let took = reads.iter().map(|&r| held[r]).collect();
            let out = long.add(NodeKind::Op(prim.clone()), took);
            let mut exports = held;
            exports.extend(out);
            long.close(exports);

            let mut short = Graph::empty(0);
            let mut exports: Vec<Source> = operands
                .iter()
                .map(|v| short.add(NodeKind::Op(Prim::Push(v.clone())), Vec::new())[0])
                .collect();
            exports.extend(
                answers
                    .into_iter()
                    .map(|v| short.add(NodeKind::Op(Prim::Push(v)), Vec::new())[0]),
            );
            short.close(exports);

            (long, short)
        }
        Rule::PromisedBool { kind } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            let arity = prim.arity();
            // `as_bool` of an `as_bool` is an equation too, and a true one,
            // but stating it invites a driver to stack them forever. The
            // law refuses to be the reason that happens.
            if arity.outputs != 1
                || matches!(prim, Prim::AsBool)
                || !prim.to_instruction().yields_bool()
            {
                return Err(ill(Ill::Refused));
            }
            let ins: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();

            let mut bare = Graph::empty(arity.inputs);
            let answer = bare.add(kind.clone(), ins.clone());
            bare.close(answer);

            let mut asserted = Graph::empty(arity.inputs);
            let answer = asserted.add(kind.clone(), ins);
            let promise = asserted.add(NodeKind::Op(Prim::AsBool), answer);
            asserted.close(promise);

            (bare, asserted)
        }
        Rule::TestedBool { kind } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            let arity = prim.arity();
            if arity.outputs != 1 || !prim.to_instruction().yields_bool() {
                return Err(ill(Ill::Refused));
            }
            let ins: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();

            let mut tested = Graph::empty(arity.inputs);
            let answer = tested.add(kind.clone(), ins.clone());
            let truth = tested.add(NodeKind::Op(Prim::IsBool), answer.clone());
            // The answer stays exported, so the window does not care who
            // else reads it — `dead-node` collects it where nobody does.
            let mut out = answer;
            out.extend(truth);
            tested.close(out);

            let mut known = Graph::empty(arity.inputs);
            let answer = known.add(kind.clone(), ins);
            let truth = known.add(NodeKind::Op(Prim::Push(Value::Bool(true))), Vec::new());
            let mut out = answer;
            out.extend(truth);
            known.close(out);

            (tested, known)
        }
        Rule::Retuple { n } => {
            let n = *n;
            if n == 0 {
                return Err(ill(Ill::Refused));
            }
            let mut roundabout = Graph::empty(1);
            let parts = roundabout.add(NodeKind::Op(Prim::Untuple(n)), vec![Source::Input(0)]);
            // The parts are not exported: rebuilding is the coercion only
            // when the window holds the whole round trip.
            let rebuilt = roundabout.add(NodeKind::Op(Prim::Tuple(n)), parts);
            roundabout.close(rebuilt);

            let mut coerced = Graph::empty(1);
            let out = coerced.add(NodeKind::Op(Prim::AsTuple(n)), vec![Source::Input(0)]);
            coerced.close(out);

            (roundabout, coerced)
        }
        Rule::AsTupleRoundTrip { n } => {
            let n = *n;
            if n == 0 {
                return Err(ill(Ill::Refused));
            }
            let mut roundabout = Graph::empty(1);
            let coerced = roundabout.add(NodeKind::Op(Prim::AsTuple(n)), vec![Source::Input(0)]);
            // The parts are not exported and the coercion is: the round
            // trip has to be whole, and the value it starts from is free
            // to have readers of its own.
            let parts = roundabout.add(NodeKind::Op(Prim::Untuple(n)), coerced.clone());
            let rebuilt = roundabout.add(NodeKind::Op(Prim::Tuple(n)), parts);
            roundabout.close(vec![coerced[0], rebuilt[0]]);

            let mut once = Graph::empty(1);
            let coerced = once.add(NodeKind::Op(Prim::AsTuple(n)), vec![Source::Input(0)]);
            once.close(vec![coerced[0], coerced[0]]);

            (roundabout, once)
        }
        Rule::IsTupleBuilt { built, asked } => {
            let (built, asked) = (*built, *asked);
            let elements: Vec<Source> = (0..built).map(Source::Input).collect();

            let mut question = Graph::empty(built);
            let tuple = question.add(NodeKind::Op(Prim::Tuple(built)), elements.clone());
            let answer = question.add(NodeKind::Op(Prim::IsTuple(Some(asked))), tuple.clone());
            // The tuple stays exported, the way `as-tuple-built` keeps its
            // own: a deduped tuple is one box with many readers, and a
            // window claiming all of them would rarely match.
            question.close(vec![tuple[0], answer[0]]);

            let mut settled = Graph::empty(built);
            let tuple = settled.add(NodeKind::Op(Prim::Tuple(built)), elements);
            let answer = settled.add(
                NodeKind::Op(Prim::Push(Value::Bool(built == asked))),
                Vec::new(),
            );
            settled.close(vec![tuple[0], answer[0]]);

            (question, settled)
        }
        Rule::AsBoolBranch => {
            let mut forced = Graph::empty(1);
            let out = forced.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)]);
            forced.close(out);

            // Neither arm reads anything, so the branch has no views: the
            // two blocks are the two answers `truthy` can give, and the
            // value itself is spent as the condition.
            let mut asked = Graph::empty(1);
            let yes = asked.add(NodeKind::Op(Prim::Push(Value::Bool(true))), Vec::new());
            let no = asked.add(NodeKind::Op(Prim::Push(Value::Bool(false))), Vec::new());
            let branch = asked.next_branch();
            let kept = asked.add(
                NodeKind::Select { arity: 1, branch },
                vec![Source::Input(0), yes[0], no[0]],
            );
            asked.close(kept);

            (forced, asked)
        }
        Rule::CoercionGuard { prim } => {
            // One test per coercion, and the width rides along: `is_tuple
            // n` asks the whole question a guard needs, so the equation is
            // one box against one box either way.
            let (test, junk) = match prim {
                Prim::AsBool => (Prim::IsBool, Value::Bool(true)),
                Prim::AsInt => (Prim::IsInt, Value::Int(0)),
                Prim::AsTuple(n) => (
                    Prim::IsTuple(Some(*n)),
                    Value::Tuple(vec![Value::unit(); *n]),
                ),
                _ => return Err(ill(Ill::Refused)),
            };

            let mut forced = Graph::empty(1);
            let out = forced.add(NodeKind::Op(prim.clone()), vec![Source::Input(0)]);
            forced.close(out);

            let mut guarded = Graph::empty(1);
            let holds = guarded.add(NodeKind::Op(test), vec![Source::Input(0)])[0];
            // The then block is the value itself — the identity half — and
            // the else block the default. Neither arm computes anything,
            // so again there are no views to hand out.
            let junk = guarded.add(NodeKind::Op(Prim::Push(junk)), Vec::new());
            let branch = guarded.next_branch();
            let kept = guarded.add(
                NodeKind::Select { arity: 1, branch },
                vec![holds, Source::Input(0), junk[0]],
            );
            guarded.close(kept);

            (forced, guarded)
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
        NodeKind::Select { arity, branch } => NodeKind::Select {
            arity: *arity,
            branch: BranchId(base + branch.0),
        },
        other => other.clone(),
    }
}

/// Runs one instruction on the operands it wants, on the machine itself.
///
/// The fold owes the interpreter exact agreement, junk included, so there
/// is no second implementation to drift: a scratch library holding
/// `push v̄ ; inst` is executed and the stack it leaves is the answer. The
/// machine joins [`sides`] on the trusted side here — which is no new
/// trust: what an operation computes was always the machine's to say.
fn run_window(operands: &[Value], inst: &Instruction) -> Option<Vec<Value>> {
    let mut library = Library::new();
    let mut sentence: Vec<Instruction> = operands
        .iter()
        .map(|v| Instruction::Push(v.clone()))
        .collect();
    sentence.push(inst.clone());
    library.sentences.push(sentence);
    let start = library.sentences.first_key().expect("one sentence");
    let mut vm = vm::VM::new(library);
    vm.execute(start).ok()?;
    Some(vm.stack().to_vec())
}

/// The `untuple n` a `tuple n` rebuilds, slot for slot: every input of the
/// tuple is port `i` of one untuple, in order, and no slot comes from
/// anywhere else.
///
/// `None` where the round trip is not whole, which is the only shape
/// either of the retupling laws states — [`Rule::Retuple`] and
/// [`Rule::AsTupleRoundTrip`] read the same walk and differ in what they
/// ask of the box behind it.
fn taken_apart(graph: &Graph, takes: &[Source], n: usize) -> Option<NodeId> {
    let apart = match (n > 0).then(|| takes[0])? {
        Source::Port { node, port: 0 } => node,
        _ => return None,
    };
    if !matches!(graph.kind(apart), NodeKind::Op(Prim::Untuple(m)) if *m == n) {
        return None;
    }
    takes
        .iter()
        .enumerate()
        .all(|(i, src)| matches!(*src, Source::Port { node, port } if node == apart && port == i))
        .then_some(apart)
}

/// A branch id off a host graph means nothing in a rule, so a rule's side
/// mints its own; [`Match::branches`] is what carries the correspondence
/// back.
fn refresh(g: &mut Graph, kind: NodeKind) -> NodeKind {
    match kind {
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

    /// The step that would undo the latest rewrite. Its [`Match`] names
    /// the boxes that rewrite left behind — which is how a driver reads a
    /// step's **image** without reaching into the splice.
    pub fn latest_undo(&self) -> Option<&Step> {
        self.steps.last().map(|(_, back)| back)
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
            NodeKind::Select { arity, branch },
            NodeKind::Select {
                arity: n,
                branch: b,
            },
        ) => arity == n && named(branch) == Some(*b),
        (NodeKind::Select { .. }, _) | (_, NodeKind::Select { .. }) => false,
        (a, b) => a == b,
    }
}

/// The same box **ignoring** branch ids — what the search prunes on, since
/// it binds the renaming as it goes and [`same_kind`] is what holds the
/// binding it settled on.
fn kinds_fit(pattern: &NodeKind, host: &NodeKind) -> bool {
    match (pattern, host) {
        (NodeKind::Select { arity, .. }, NodeKind::Select { arity: n, .. }) => arity == n,
        (NodeKind::Select { .. }, _) | (_, NodeKind::Select { .. }) => false,
        (a, b) => a == b,
    }
}

/// A replacement's box, with its branch ids read as the host's.
fn rename(kind: &NodeKind, branches: &[BranchId]) -> NodeKind {
    match kind {
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
    find_pinned(graph, pattern, 0, seed)
}

/// [`find_at`], with pattern box `pat` — not necessarily the first —
/// pinned to `host`.
///
/// This is what lets a driver anchor a rule at the box its *query* bound
/// rather than the box the pattern happens to begin with: a pattern is
/// built producers-first, so the box a rule is naturally *about* need not
/// be its first. The walk starts at `pat` and the answer is unchanged —
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

/// Whether a pattern says enough about itself to be looked for: at least one
/// box to anchor on, no source exported twice or exported straight from
/// the boundary, no boundary input nothing in the pattern reads, and no
/// branch id that no box witnesses.
///
/// The branch decline is for a side that **skips** a branch id — a
/// [`BranchId`] means the same branch on both sides of an equation, and an
/// id no select carries cannot be read off a match — its image in the host is a choice, exactly as a reader-split
/// is, so the pattern has to be stated rather than searched for. The
/// unread-input decline is `equal-refl`'s answer side: a discard's window
/// still stands for the discarded wire, and which wire that is cannot be
/// read off a pattern that never touches it.
fn pins_itself(pattern: &Graph) -> bool {
    if pattern.nodes.is_empty() {
        return false;
    }
    if pattern.inputs.iter().any(|readers| readers.is_empty()) {
        return false;
    }
    let mut witnessed: HashSet<BranchId> = HashSet::new();
    for (_, kind) in pattern.live() {
        if let NodeKind::Select { branch, .. } = kind {
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
    /// the rest in index order. [`Match::nodes`] stays in pattern order;
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
    /// two unconnected boxes — `dedup`'s pattern — still cost one sweep
    /// rather than a product.
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
            (NodeKind::Select { branch, .. }, NodeKind::Select { branch: b, .. }) => {
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
                    // before what feeds it, and [`check_match`] holds every
                    // edge at the end either way. In pattern order this arm
                    // never defers — a rule's side is built producers-first.
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

/// Every instantiation of `law` this graph offers a payload for.
///
/// [`propose`] answers "what can fire *here*", and the anchor it is given
/// is also where the payload is read from. This answers the other half:
/// **which equations** the law comes to in this graph, with the *where*
/// left open — the vocabulary of concrete [`Rule`]s a caller can then look
/// for anywhere, at either side.
///
/// It is [`read_off`] swept over every live box and deduplicated, so the
/// payloads are exactly the ones some box in the graph spells: `dedup` of
/// each kind present, `id-elim` of each width present, and nothing the
/// graph does not itself say. That is a real limit and it is the honest
/// one — a payload no box witnesses would have to be stated rather than
/// found, which is what [`Match`] and a stated step are for — and it is
/// what makes a **backward** search possible at all: the right-hand side
/// of a concrete rule is a graph like any other, so it can be looked for
/// wherever it names enough boxes to pin itself.
pub fn instances(graph: &Graph, law: Law) -> Vec<Rule> {
    let ids: Vec<NodeId> = graph.live().map(|(id, _)| id).collect();
    let mut out: Vec<Rule> = Vec::new();
    for id in ids {
        for (rule, _) in read_off(graph, law, id) {
            if !out.contains(&rule) {
                out.push(rule);
            }
        }
    }
    out
}

/// Everything downstream of one box's single answer, lifted out as a graph
/// of its own — the body a [`Rule::Shannon`] carries.
fn downstream(graph: &Graph, of: NodeId) -> Option<Graph> {
    downstream_of(graph, &[Source::Port { node: of, port: 0 }], false)
}

/// Everything downstream of one box's `answers`, lifted out as a graph of
/// its own — the body a region-carrying rule carries.
///
/// The region is the transitive readers of the answers, which makes it
/// downstream-closed: a region box's readers are region boxes or the
/// boundary, so the lifted graph's outputs are exactly what the host
/// boundary read of it, in the host's order. Inputs `0..answers.len()`
/// stand for the answers; the rest is whatever else the region reads, in
/// encounter order. `None` when nothing but the boundary reads them — an
/// expansion with an empty body decides nothing.
///
/// `spare` says what to do with an answer the host boundary reads
/// **directly**. [`Rule::Shannon`] exports its answer from the window
/// itself and wants it left alone. [`Rule::SelectHoist`] cannot — its
/// select is gone on the other side of the equation — so it asks for the
/// answer to come back as one of the body's own outputs, passed straight
/// through from the input that stands for it. Then the copy on each side
/// leaves that side's block, and the new select chooses between exactly
/// the blocks the old one chose between.
fn downstream_of(graph: &Graph, answers: &[Source], spare: bool) -> Option<Graph> {
    let mut region: Vec<NodeId> = Vec::new();
    let mut todo: Vec<Source> = answers.to_vec();
    while let Some(src) = todo.pop() {
        for &sink in graph.sinks(src) {
            let Sink::Port { node, .. } = sink else {
                continue;
            };
            if region.contains(&node) {
                continue;
            }
            region.push(node);
            for port in 0..graph.kind(node).arity().outputs {
                todo.push(Source::Port { node, port });
            }
        }
    }
    if region.is_empty() {
        return None;
    }
    region.sort_unstable();
    let mine: HashSet<NodeId> = region.iter().copied().collect();

    // An order the body can be rebuilt in — by its own edges, since a
    // rewrite can leave a low id reading a high one.
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

    // What it reads that it does not own, the answers aside.
    let held = |src: Source| matches!(src, Source::Port { node, .. } if mine.contains(&node));
    let mut extra: Vec<Source> = Vec::new();
    for src in region
        .iter()
        .flat_map(|&node| graph.sources(node).iter().copied())
    {
        if !answers.contains(&src) && !held(src) && !extra.contains(&src) {
            extra.push(src);
        }
    }

    let place: HashMap<NodeId, usize> = region.iter().enumerate().map(|(i, &n)| (n, i)).collect();
    let mut branches: Vec<BranchId> = Vec::new();
    for &node in &region {
        if let NodeKind::Select { branch, .. } = graph.kind(node)
            && !branches.contains(branch)
        {
            branches.push(*branch);
        }
    }
    let renumber = |kind: &NodeKind| {
        let of =
            |b: &BranchId| BranchId(branches.iter().position(|h| h == b).expect("noted") as u32);
        match kind {
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
        other => match answers.iter().position(|&a| a == other) {
            Some(i) => Source::Input(i),
            None => Source::Input(
                answers.len() + extra.iter().position(|&e| e == other).expect("noted"),
            ),
        },
    };

    let mut lifted = Graph::empty(answers.len() + extra.len());
    for &node in &region {
        let takes = graph.sources(node).iter().map(|&s| inside(s)).collect();
        lifted.add(renumber(graph.kind(node)), takes);
    }
    lifted.branches = branches.len() as u32;
    lifted.close(
        graph
            .outputs()
            .iter()
            .filter(|src| held(**src) || (spare && answers.contains(src)))
            .map(|&s| inside(s))
            .collect(),
    );
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
        (Law::Dedup, NodeKind::Select { .. }) => Vec::new(),
        (Law::Dedup, _) => one(Rule::Dedup { kind }),
        (Law::NotNot, NodeKind::Op(Prim::Not)) => one(Rule::NotNot),

        // `and` with a literal operand: one rule per operand a pushed
        // value feeds, seeded at the literal the pattern anchors on.
        (Law::AndLiteral, NodeKind::Op(Prim::And)) => {
            let mut out = Vec::new();
            for (side, port) in [(Side::Deep, 0), (Side::Top, 1)] {
                if let Some((lit, NodeKind::Op(Prim::Push(value)))) = made_by(takes[port]) {
                    out.push((
                        Rule::AndLiteral {
                            literal: side,
                            value: value.clone(),
                        },
                        lit,
                    ));
                }
            }
            out
        }

        // Taking apart, or coercing, what `tuple n` built — seeded at the
        // tuple, which is where the pattern anchors.
        (Law::TupleCancel, NodeKind::Op(Prim::Untuple(n))) => match made_by(takes[0]) {
            Some((built, NodeKind::Op(Prim::Tuple(m)))) if m == n => {
                vec![(Rule::TupleCancel { n: *n }, built)]
            }
            _ => Vec::new(),
        },
        (Law::AsTupleBuilt, NodeKind::Op(Prim::AsTuple(n))) => match made_by(takes[0]) {
            Some((built, NodeKind::Op(Prim::Tuple(m)))) if m == n => {
                vec![(Rule::AsTupleBuilt { n: *n }, built)]
            }
            _ => Vec::new(),
        },

        // Asking a value the window watched being built what shape it is.
        // Either width answers, so there is no `m == n` to check here —
        // that comparison is the law's answer, not its side condition.
        (Law::IsTupleBuilt, NodeKind::Op(Prim::IsTuple(Some(asked)))) => match made_by(takes[0]) {
            Some((tuple, NodeKind::Op(Prim::Tuple(m)))) => vec![(
                Rule::IsTupleBuilt {
                    built: *m,
                    asked: *asked,
                },
                tuple,
            )],
            _ => Vec::new(),
        },

        // One wire, compared with itself.
        (Law::EqualRefl, NodeKind::Op(Prim::Equal)) => {
            if takes[0] == takes[1] {
                one(Rule::EqualRefl)
            } else {
                Vec::new()
            }
        }

        // A block the select answers with either way.
        (Law::SelectSame, NodeKind::Select { arity: n, .. }) => (0..*n)
            .filter(|j| takes[1 + j] == takes[1 + n + j])
            .map(|j| (Rule::SelectSame { arity: *n, at: j }, id))
            .collect(),

        // A condition that is already a value: the select is the blocks it
        // chooses, and the arm it did not choose falls to `dead-node`.
        (Law::SelectConst, NodeKind::Select { arity: n, .. }) => {
            let n = *n;
            let Some((lit, NodeKind::Op(Prim::Push(value)))) = made_by(takes[0]) else {
                return Vec::new();
            };
            let lit_blocks: Vec<usize> = (0..2 * n).filter(|&b| takes[1 + b] == takes[0]).collect();
            vec![(
                Rule::SelectConst {
                    value: value.clone(),
                    arity: n,
                    lit_blocks,
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

        // A block that answers with the very condition, that condition
        // being manifestly a bool — which is what the branch decided about
        // it, read where the discard makes reading it sound.
        (Law::SpecializeBool, NodeKind::Select { arity: n, .. }) => {
            let (n, cond) = (*n, takes[0]);
            // The `as_bool` that made the condition is the pattern's first
            // box, so it is what the search is anchored at.
            let Some((coercion, NodeKind::Op(Prim::AsBool))) = made_by(cond) else {
                return Vec::new();
            };
            (0..2 * n)
                .filter(|&b| takes[1 + b] == cond)
                .map(|b| (Rule::SpecializeBool { arity: n, at: b }, coercion))
                .collect()
        }

        // A branch inside an arm, retesting the value the outer branch
        // tested — read off the outer select, one payload per inner select
        // among its blocks and per side of the outer branch it answers.
        (
            Law::SpecializeChoice,
            NodeKind::Select {
                arity: n,
                branch: mine,
            },
        ) => {
            let (n, cond) = (*n, takes[0]);
            let mut rules: Vec<(Rule, NodeId)> = Vec::new();
            let mut inners: Vec<NodeId> = Vec::new();
            for b in 0..2 * n {
                let Source::Port { node: within, .. } = takes[1 + b] else {
                    continue;
                };
                let NodeKind::Select {
                    arity: m,
                    branch: nested,
                } = graph.kind(within)
                else {
                    continue;
                };
                if nested == mine || inners.contains(&within) {
                    continue;
                }
                // The same value tested twice: the inner select turns on
                // the very wire the outer one does, which the pattern says
                // by reading one boundary input at both port 0s.
                if graph.sources(within)[0] != cond {
                    continue;
                }
                inners.push(within);
                // One payload per side. An inner select answering blocks in
                // both halves is two equations, and a payload states one.
                for then in [true, false] {
                    let moves: Vec<(usize, usize)> = (0..2 * n)
                        .filter_map(|at| match takes[1 + at] {
                            Source::Port { node, port } if node == within && (at < n) == then => {
                                Some((port, at))
                            }
                            _ => None,
                        })
                        .collect();
                    if moves.is_empty() {
                        continue;
                    }
                    rules.push((
                        Rule::SpecializeChoice {
                            arity: n,
                            inner: *m,
                            moves,
                        },
                        within,
                    ));
                }
            }
            rules
        }

        // The instruction set's promise, written down as a box. Proposed
        // only where one is not already standing: the equation holds
        // however many `as_bool`s are stacked on the answer, so nothing but
        // this guard stops a driver stacking them forever. Search is where
        // that argument belongs — the law states an equality and no more.
        (Law::PromisedBool, NodeKind::Op(prim)) => {
            if prim.arity().outputs != 1
                || matches!(prim, Prim::AsBool)
                || !prim.to_instruction().yields_bool()
            {
                return Vec::new();
            }
            let asserted = graph
                .sinks(Source::Port { node: id, port: 0 })
                .iter()
                .any(|sink| match sink {
                    Sink::Port { node, .. } => {
                        matches!(graph.kind(*node), NodeKind::Op(Prim::AsBool))
                    }
                    Sink::Output(_) => false,
                });
            match asserted {
                true => Vec::new(),
                false => vec![(Rule::PromisedBool { kind: kind.clone() }, id)],
            }
        }

        // Everything downstream of a promised bool, lifted out as the body
        // of its split.
        (Law::Shannon, NodeKind::Op(prim)) => {
            if prim.arity().outputs != 1 || !prim.to_instruction().yields_bool() {
                return Vec::new();
            }
            match downstream(graph, id) {
                Some(body) => vec![(
                    Rule::Shannon {
                        kind: kind.clone(),
                        body,
                    },
                    id,
                )],
                None => Vec::new(),
            }
        }

        // Everything downstream of a branch's answers, lifted out as the
        // body the branch grows forward over. Read off the `select`, which
        // is also where the pattern begins.
        (Law::SelectHoist, NodeKind::Select { arity, .. }) => {
            let answers: Vec<Source> = (0..*arity)
                .map(|port| Source::Port { node: id, port })
                .collect();
            match downstream_of(graph, &answers, true) {
                Some(body) => vec![(
                    Rule::SelectHoist {
                        arity: *arity,
                        body,
                    },
                    id,
                )],
                None => Vec::new(),
            }
        }

        // An operation whose every operand is a literal — the fold, and
        // the machine is what answers it.
        (Law::Fold, NodeKind::Op(prim)) => {
            if matches!(prim, Prim::Push(_) | Prim::Swap) || takes.is_empty() {
                return Vec::new();
            }
            let mut held: Vec<(NodeId, Value)> = Vec::new();
            let mut reads: Vec<usize> = Vec::new();
            for &src in takes {
                let Some((node, NodeKind::Op(Prim::Push(value)))) = made_by(src) else {
                    return Vec::new();
                };
                let at = match held.iter().position(|(h, _)| *h == node) {
                    Some(at) => at,
                    None => {
                        held.push((node, value.clone()));
                        held.len() - 1
                    }
                };
                reads.push(at);
            }
            let seed = held[0].0;
            vec![(
                Rule::Fold {
                    prim: prim.clone(),
                    operands: held.into_iter().map(|(_, v)| v).collect(),
                    reads,
                },
                seed,
            )]
        }

        // `is_bool` of an answer the instruction set promises is a bool.
        (Law::TestedBool, NodeKind::Op(Prim::IsBool)) => {
            let Some((answered, NodeKind::Op(prim))) = made_by(takes[0]) else {
                return Vec::new();
            };
            if prim.arity().outputs != 1 || !prim.to_instruction().yields_bool() {
                return Vec::new();
            }
            vec![(
                Rule::TestedBool {
                    kind: graph.kind(answered).clone(),
                },
                answered,
            )]
        }

        // Rebuilding exactly what an `untuple` took apart — and, one box
        // further back, doing it to a value already coerced.
        (Law::Retuple, NodeKind::Op(Prim::Tuple(n))) => match taken_apart(graph, takes, *n) {
            Some(apart) => vec![(Rule::Retuple { n: *n }, apart)],
            None => Vec::new(),
        },
        (Law::AsTupleRoundTrip, NodeKind::Op(Prim::Tuple(n))) => {
            let n = *n;
            let Some(apart) = taken_apart(graph, takes, n) else {
                return Vec::new();
            };
            // The pattern is built coercion-first, so that is the seed.
            let Some(Source::Port {
                node: coerced,
                port: 0,
            }) = graph.sources(apart).first().copied()
            else {
                return Vec::new();
            };
            if !matches!(graph.kind(coerced), NodeKind::Op(Prim::AsTuple(m)) if *m == n) {
                return Vec::new();
            }
            vec![(Rule::AsTupleRoundTrip { n }, coerced)]
        }

        // The two unpackings of a coercion, each read off the box it
        // unpacks.
        (Law::AsBoolBranch, NodeKind::Op(Prim::AsBool)) => one(Rule::AsBoolBranch),
        (Law::CoercionGuard, NodeKind::Op(prim))
            if matches!(prim, Prim::AsBool | Prim::AsInt | Prim::AsTuple(_)) =>
        {
            one(Rule::CoercionGuard { prim: prim.clone() })
        }

        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::meaning::{Meaning, boundary, eval_graph};
    use crate::diagram2::{build, isomorphic};
    use crate::term::Context;
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

    /// A branch id is a name, and merging two selects would give one box
    /// two of them — so the rule that would do it is refused before it is
    /// built.
    #[test]
    fn dedup_refuses_the_end_of_a_branch() {
        let kind = NodeKind::Select {
            arity: 2,
            branch: BranchId(0),
        };
        assert_eq!(
            sides(&Rule::Dedup { kind }).unwrap_err(),
            Error::Ill {
                law: Law::Dedup,
                why: Ill::Refused
            }
        );
    }

    // ---- the branch layer ----

    /// Every assignment of a handful of values to `width` inputs.
    ///
    /// Chosen to cover the truthiness table on both poles — `false` is the
    /// one falsy value, and `unit` is junk, which is truthy like everything
    /// else — and the tuple widths on either side of the ones the coercion
    /// laws name: `unit` is a tuple of width 0 and `(1, 2)` one of width 2,
    /// so a law about `as_tuple 2` meets a value it is the identity on, a
    /// tuple it is not, and three things that are no tuple at all.
    fn samples(width: usize) -> Vec<Vec<Value>> {
        let each = [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(7),
            Value::unit(),
            Value::Tuple(vec![Value::Int(1), Value::Int(2)]),
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
    /// A closed graph, run: every operation on the machine itself
    /// ([`run_window`], so there is no second semantics) and a select
    /// keeping the block `truthy` says.
    fn eval_on(graph: &Graph, inputs: &[Value]) -> Vec<Value> {
        assert_eq!(inputs.len(), graph.arity().inputs, "one value per input");
        let mut held: HashMap<Source, Value> = inputs
            .iter()
            .enumerate()
            .map(|(i, v)| (Source::Input(i), v.clone()))
            .collect();
        for id in crate::diagram2::schedule(graph) {
            let took: Vec<Value> = graph
                .sources(id)
                .iter()
                .map(|src| held[src].clone())
                .collect();
            let answers = match graph.kind(id) {
                NodeKind::Op(prim) => run_window(&took, &prim.to_instruction())
                    .expect("every prim is total on the machine"),
                NodeKind::Id(_) => took,
                NodeKind::Copy(_) => [took.clone(), took].concat(),
                NodeKind::Drop(_) => Vec::new(),
                NodeKind::Select { arity, .. } => {
                    let n = *arity;
                    if took[0].truthy() {
                        took[1..=n].to_vec()
                    } else {
                        took[n + 1..].to_vec()
                    }
                }
                NodeKind::Call { .. } => unreachable!("a law's side calls nothing"),
            };
            for (port, v) in answers.into_iter().enumerate() {
                held.insert(Source::Port { node: id, port }, v);
            }
        }
        graph
            .outputs()
            .iter()
            .map(|src| held[src].clone())
            .collect()
    }

    /// A law held to the **machine**, over every assignment of a handful of
    /// values to its boundary.
    ///
    /// The opaque oracle cannot judge these: `equal(x, 7)` is a symbol to
    /// it, and the whole content of the law is what that symbol computes.
    /// So both sides *run*, every operation on the machine itself.
    /// Sampling is not a proof, and the proof is in the docs; this is what
    /// would catch the proof being wrong.
    fn the_machine_agrees(law: Law, rule: Rule) {
        assert_eq!(rule.law(), law, "the payload names the wrong law");
        assert!(!is_wiring(law), "a wiring law has a cheaper judge");
        let (lhs, rhs) =
            sides(&rule).unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        assert_eq!(lhs.arity(), rhs.arity());
        for values in samples(lhs.arity().inputs) {
            assert_eq!(
                eval_on(&lhs, &values),
                eval_on(&rhs, &values),
                "{:?} relates two different programs on {:?}",
                law,
                values
            );
        }
    }

    /// The instruction set's promise, written down. `as_bool` is `truthy`
    /// made into an instruction, so on a value already a bool it is the
    /// identity — which is a fact about what the machine computes, and `vm`
    /// is what judges it.
    #[test]
    fn a_promised_bool_may_say_so() {
        for prim in [Prim::Not, Prim::Equal, Prim::IsSymbol, Prim::IsBool] {
            the_machine_agrees(
                Law::PromisedBool,
                Rule::PromisedBool {
                    kind: NodeKind::Op(prim),
                },
            );
        }
        // `as_bool` of an `as_bool` is a true equation and a bottomless one.
        // The law refuses to be the reason a driver stacks them.
        assert!(matches!(
            sides(&Rule::PromisedBool {
                kind: NodeKind::Op(Prim::AsBool),
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
        // Nothing promises what `add` answers.
        assert!(matches!(
            sides(&Rule::PromisedBool {
                kind: NodeKind::Op(Prim::Add),
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// The equation holds however many `as_bool`s already stand on the
    /// answer, so only the search declines to say it twice.
    #[test]
    fn the_promise_is_proposed_once() {
        let (_terms, graph) = built("pick 0 is_symbol");
        let count = |g: &Graph| {
            g.live()
                .flat_map(|(id, _)| propose(g, &[Law::PromisedBool], id))
                .count()
        };
        assert_eq!(count(&graph), 1, "the one bool-yielding box offers it");
        let mut asserted = graph.clone();
        let step = graph
            .live()
            .flat_map(|(id, _)| propose(&graph, &[Law::PromisedBool], id))
            .next()
            .expect("there is one");
        apply(&mut asserted, &step).expect("and it applies");
        assert_eq!(
            count(&asserted),
            0,
            "an answer already carrying its promise offers nothing"
        );
    }

    /// A choice between one value is that value.
    #[test]
    fn a_block_answered_either_way_is_the_answer() {
        holds(Law::SelectSame, Rule::SelectSame { arity: 1, at: 0 });
        holds(Law::SelectSame, Rule::SelectSame { arity: 3, at: 1 });
    }

    /// An arm of one box on the view it was handed.
    fn one_step(kind: NodeKind) -> Graph {
        let mut g = Graph::empty(1);
        let out = g.add(kind, vec![Source::Input(0)]);
        g.close(out);
        g
    }

    /// A body of one box, one boundary input per port it takes: for a
    /// region-carrying rule the first few stand for the answers it is
    /// downstream of and the rest for what it reads from outside.
    fn takes_all(kind: NodeKind) -> Graph {
        let width = kind.arity().inputs;
        let mut g = Graph::empty(width);
        let out = g.add(kind, (0..width).map(Source::Input).collect());
        g.close(out);
        g
    }

    /// The same value tested twice answers the same: a branch whose
    /// condition is the very wire an outer branch turned on is decided by
    /// the side of the outer branch its answers are read from.
    #[test]
    fn a_value_retested_in_an_arm_is_decided() {
        for moves in [
            // In the then arm the value was truthy; in the else arm it was
            // `false`, the one falsy value.
            vec![(0, 0)],
            vec![(0, 1)],
        ] {
            the_machine_agrees(
                Law::SpecializeChoice,
                Rule::SpecializeChoice {
                    arity: 1,
                    inner: 1,
                    moves,
                },
            );
        }
        // A wider window: two of the inner select's answers, moved at once.
        the_machine_agrees(
            Law::SpecializeChoice,
            Rule::SpecializeChoice {
                arity: 2,
                inner: 2,
                moves: vec![(0, 0), (1, 1)],
            },
        );
        // Moves on both sides at once are refused: which side is what the
        // blocks say, and a payload states one equation.
        assert!(matches!(
            sides(&Rule::SpecializeChoice {
                arity: 1,
                inner: 1,
                moves: vec![(0, 0), (0, 1)],
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// η, as an equation: everything downstream of a promised bool is a
    /// branch on it, both copies run and one kept — which the machine can
    /// judge sample by sample, totality doing the licensing.
    #[test]
    fn a_promised_bool_splits_its_downstream() {
        the_machine_agrees(
            Law::Shannon,
            Rule::Shannon {
                kind: NodeKind::Op(Prim::IsBool),
                body: one_step(NodeKind::Op(Prim::Not)),
            },
        );
        // A body holding a branch of its own, and reading past the answer.
        the_machine_agrees(
            Law::Shannon,
            Rule::Shannon {
                kind: NodeKind::Op(Prim::IsInt),
                body: sides(&Rule::SelectSame { arity: 1, at: 0 }).unwrap().0,
            },
        );
        // The set does not promise `add` answers a bool, so there is no
        // equation to state.
        assert!(matches!(
            sides(&Rule::Shannon {
                kind: NodeKind::Op(Prim::Add),
                body: one_step(NodeKind::Op(Prim::Not)),
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// The commuting conversion: what runs after a branch runs inside
    /// whichever arm it takes. Nothing is pinned, so no promise about the
    /// condition is spent — but the oracle reads a `Choice` per output and
    /// cannot push an opaque application through one, so the machine is
    /// the judge.
    #[test]
    fn a_branch_grows_over_what_follows_it() {
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                arity: 1,
                body: one_step(NodeKind::Op(Prim::Not)),
            },
        );
        // Both answers of a two-wide branch, read by one box.
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                arity: 2,
                body: takes_all(NodeKind::Op(Prim::Add)),
            },
        );
        // A body that reads *past* the answers: one block of the branch,
        // and one wire from outside it.
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                arity: 1,
                body: takes_all(NodeKind::Op(Prim::Add)),
            },
        );
        // A body holding a branch of its own, duplicated with it.
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                arity: 1,
                body: sides(&Rule::SelectSame { arity: 1, at: 0 }).unwrap().0,
            },
        );
        // A body that leaves nothing states no equation, and neither does
        // a select of no width: there is no branch to grow.
        for refused in [
            Rule::SelectHoist {
                arity: 1,
                body: dead_box(NodeKind::Op(Prim::Not)),
            },
            Rule::SelectHoist {
                arity: 0,
                body: one_step(NodeKind::Op(Prim::Not)),
            },
        ] {
            assert!(matches!(
                sides(&refused),
                Err(Error::Ill {
                    why: Ill::Refused,
                    ..
                })
            ));
        }
    }

    /// An answer the host boundary reads is not what stops the branch
    /// moving.
    ///
    /// The select is gone on the far side of the equation, so the window
    /// cannot export its answers the way `shannon` exports the wire it
    /// splits — every one of them has to be read *inside* the body. An
    /// answer that goes straight out is handed back as one of the body's
    /// own outputs, passed through from the input standing for it, and the
    /// new select then chooses between the very blocks the old one chose
    /// between. Read off a real graph, applied, and both sides run on the
    /// machine to check it.
    #[test]
    fn an_answer_read_from_outside_passes_through_the_body() {
        // `select(2)` on five wires: one answer feeds a `negate`, the other
        // leaves by the boundary.
        let mut graph = Graph::empty(5);
        let branch = graph.next_branch();
        let answers = graph.add(
            NodeKind::Select { arity: 2, branch },
            (0..5).map(Source::Input).collect(),
        );
        let negated = graph.add(NodeKind::Op(Prim::Negate), vec![answers[0]]);
        graph.close(vec![negated[0], answers[1]]);
        graph.check().unwrap();
        let before = graph.clone();

        let select = only(&NodeKind::Select { arity: 2, branch }, &graph);
        let steps = propose(&graph, &[Law::SelectHoist], select);
        let [step] = &steps[..] else {
            panic!("one branch to move, and {} proposals", steps.len());
        };
        let back = apply(&mut graph, step).unwrap();
        graph.check().unwrap();

        // Two copies of the body, and the select now as wide as the body's
        // answers rather than as the blocks it was choosing between.
        assert_eq!(
            graph
                .live()
                .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
                .count(),
            2,
            "the body did not go into both arms:\n{}",
            graph
        );
        let moved = only(&NodeKind::Select { arity: 2, branch }, &graph);
        assert_ne!(moved, select, "the select was not rebuilt:\n{}", graph);
        assert_eq!(
            graph.sources(moved)[0],
            Source::Input(0),
            "the condition is the one the branch always turned on:\n{}",
            graph
        );

        // The same program, on the machine, at every assignment.
        for values in samples(5) {
            assert_eq!(
                eval_on(&before, &values),
                eval_on(&graph, &values),
                "the branch moved and the program changed, on {:?}",
                values
            );
        }

        // And the way back is the same embedding over the other side.
        apply(&mut graph, &back).unwrap();
        graph.check().unwrap();
        assert!(
            isomorphic(&before, &graph),
            "undoing the move did not land where it started:\n{}",
            graph
        );
    }

    /// The fold: a literal window runs on the machine itself, and the
    /// answer side is built from what came back.
    #[test]
    fn a_literal_window_is_its_answer() {
        the_machine_agrees(
            Law::Fold,
            Rule::Fold {
                prim: Prim::Add,
                operands: vec![Value::Int(3), Value::Int(4)],
                reads: vec![0, 1],
            },
        );
        // One literal read twice — the shape a `dedup` leaves.
        the_machine_agrees(
            Law::Fold,
            Rule::Fold {
                prim: Prim::Equal,
                operands: vec![Value::Int(7)],
                reads: vec![0, 0],
            },
        );
        // More answers than operands: the fold follows the arity table.
        the_machine_agrees(
            Law::Fold,
            Rule::Fold {
                prim: Prim::Untuple(2),
                operands: vec![Value::Tuple(vec![Value::Int(1), Value::Bool(true)])],
                reads: vec![0],
            },
        );
        // Junk in, junk out — the machine's junk, not a second opinion.
        the_machine_agrees(
            Law::Fold,
            Rule::Fold {
                prim: Prim::AsBool,
                operands: vec![Value::Int(0)],
                reads: vec![0],
            },
        );
        // A literal is not a window, and neither is a crossing.
        for prim in [Prim::Push(Value::Int(1)), Prim::Swap] {
            assert!(matches!(
                sides(&Rule::Fold {
                    prim,
                    operands: vec![Value::Int(1), Value::Int(2)],
                    reads: vec![0, 1],
                }),
                Err(Error::Ill {
                    why: Ill::Refused,
                    ..
                })
            ));
        }
    }

    /// `is_bool` of an answer the instruction set promises is a bool.
    #[test]
    fn a_promised_bool_tests_true() {
        the_machine_agrees(
            Law::TestedBool,
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::IsInt),
            },
        );
        the_machine_agrees(
            Law::TestedBool,
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::Equal),
            },
        );
        the_machine_agrees(
            Law::TestedBool,
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::IsBool),
            },
        );
        // An answer the set does not promise is no window.
        assert!(matches!(
            sides(&Rule::TestedBool {
                kind: NodeKind::Op(Prim::Add),
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// `and` with a literal operand is decided by `truthy` alone: a truthy
    /// literal leaves the other operand's coercion, the one falsy value
    /// leaves `false` — short-circuiting, as an equation, held to the
    /// machine over every sample and both operand positions.
    #[test]
    fn an_and_with_a_literal_is_decided_by_truthiness() {
        for value in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(7),
        ] {
            for literal in [Side::Deep, Side::Top] {
                the_machine_agrees(
                    Law::AndLiteral,
                    Rule::AndLiteral {
                        literal,
                        value: value.clone(),
                    },
                );
            }
        }
    }

    /// The tuple rows: taking apart or coercing what `tuple n` built, and
    /// one wire compared with itself — each held to the machine.
    #[test]
    fn a_built_tuple_cancels_coerces_and_equals_itself() {
        for n in [1, 2, 3] {
            the_machine_agrees(Law::TupleCancel, Rule::TupleCancel { n });
            the_machine_agrees(Law::AsTupleBuilt, Rule::AsTupleBuilt { n });
        }
        the_machine_agrees(Law::EqualRefl, Rule::EqualRefl);
    }

    /// A literal condition, and the select is the blocks it chooses —
    /// including the shape a `dedup` makes, where the condition and a
    /// block are one pushed value.
    #[test]
    fn a_select_on_a_literal_is_its_blocks() {
        for value in [Value::Bool(true), Value::Bool(false), Value::Int(0)] {
            the_machine_agrees(
                Law::SelectConst,
                Rule::SelectConst {
                    value: value.clone(),
                    arity: 1,
                    lit_blocks: Vec::new(),
                },
            );
            the_machine_agrees(
                Law::SelectConst,
                Rule::SelectConst {
                    value,
                    arity: 2,
                    lit_blocks: vec![1, 2],
                },
            );
        }
    }

    /// Rebuilding what `untuple n` took apart is the coercion.
    #[test]
    fn retupling_is_the_coercion() {
        the_machine_agrees(Law::Retuple, Rule::Retuple { n: 1 });
        the_machine_agrees(Law::Retuple, Rule::Retuple { n: 2 });
        assert!(matches!(
            sides(&Rule::Retuple { n: 0 }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// A value already coerced survives being taken apart and put back.
    ///
    /// The width is the whole content: `as_tuple n` leaves a tuple of
    /// exactly `n` elements whatever it was handed, so `untuple n` has `n`
    /// parts to give and `tuple n` puts back the very value — which the
    /// sample list checks on a tuple of the right width, one of the wrong
    /// width, and three values that are no tuple at all.
    #[test]
    fn a_coerced_tuple_survives_the_round_trip() {
        for n in 1..=3 {
            the_machine_agrees(Law::AsTupleRoundTrip, Rule::AsTupleRoundTrip { n });
        }
        // A round trip of nothing is not one, the same refusal `retuple`
        // makes: `tuple 0` reads no part of the `untuple 0` in front of it,
        // so the window would not hold a round trip at all.
        assert!(matches!(
            sides(&Rule::AsTupleRoundTrip { n: 0 }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
    }

    /// A tuple the window watched being built answers what shape it is.
    ///
    /// Both widths are payload and both cases are the law: equal widths
    /// answer `true`, a mismatch `false`. The machine settles each, and
    /// the sample list's own tuple is beside the point here — the operand
    /// under test is built inside the window, from whatever the boundary
    /// hands in.
    #[test]
    fn a_built_tuple_answers_what_shape_it_is() {
        for built in 0..=2 {
            for asked in 0..=3 {
                the_machine_agrees(Law::IsTupleBuilt, Rule::IsTupleBuilt { built, asked });
            }
        }

        // And it is read off the test, at the tuple the pattern anchors on.
        let mut graph = Graph::empty(2);
        let tuple = graph.add(
            NodeKind::Op(Prim::Tuple(2)),
            vec![Source::Input(0), Source::Input(1)],
        );
        let asked = graph.add(NodeKind::Op(Prim::IsTuple(Some(3))), tuple.clone());
        graph.close(vec![tuple[0], asked[0]]);
        graph.check().unwrap();

        let steps = propose(
            &graph,
            &[Law::IsTupleBuilt],
            only(&NodeKind::Op(Prim::IsTuple(Some(3))), &graph),
        );
        let [step] = &steps[..] else {
            panic!("one built tuple, one test:\n{}", graph)
        };
        assert_eq!(
            step.rule,
            Rule::IsTupleBuilt { built: 2, asked: 3 },
            "the mismatch is the law's answer, not a reason to decline"
        );
        apply(&mut graph, step).unwrap();
        graph.check().unwrap();
        assert!(
            graph
                .live()
                .any(|(_, kind)| kind == &NodeKind::Op(Prim::Push(Value::Bool(false)))),
            "a `tuple 2` is no tuple of three:\n{}",
            graph
        );

        // A width-blind `is_tuple` is a different question, and this law
        // does not answer it: the row is about what the width decides.
        let mut graph = Graph::empty(2);
        let tuple = graph.add(
            NodeKind::Op(Prim::Tuple(2)),
            vec![Source::Input(0), Source::Input(1)],
        );
        let asked = graph.add(NodeKind::Op(Prim::IsTuple(None)), tuple.clone());
        graph.close(vec![tuple[0], asked[0]]);
        assert!(
            propose(
                &graph,
                &[Law::IsTupleBuilt],
                only(&NodeKind::Op(Prim::IsTuple(None)), &graph)
            )
            .is_empty()
        );
    }

    /// `as_bool` is the branch it is — the coercion `truthy` names, said as
    /// the decision it makes.
    #[test]
    fn as_bool_is_a_branch_on_truthiness() {
        the_machine_agrees(Law::AsBoolBranch, Rule::AsBoolBranch);
    }

    /// A coercion is a guarded identity: the value where its test holds,
    /// and a default where it does not.
    ///
    /// The width guard is what this is really checking. The width-blind
    /// `is_tuple` would claim `as_tuple 2` is the identity on every tuple,
    /// so the sample list carries a tuple of a width no `n` here names, and
    /// the machine settles it.
    #[test]
    fn a_coercion_is_a_guarded_identity() {
        for prim in [
            Prim::AsBool,
            Prim::AsInt,
            Prim::AsTuple(0),
            Prim::AsTuple(1),
            Prim::AsTuple(2),
        ] {
            the_machine_agrees(Law::CoercionGuard, Rule::CoercionGuard { prim });
        }
        // Only the three coercions have a type to guard on; a payload that
        // is any other prim states no equation.
        for prim in [Prim::Not, Prim::IsTuple(Some(2)), Prim::Push(Value::Int(1))] {
            assert!(
                matches!(
                    sides(&Rule::CoercionGuard { prim: prim.clone() }),
                    Err(Error::Ill {
                        why: Ill::Refused,
                        ..
                    })
                ),
                "{:?} is no coercion",
                prim
            );
        }
    }

    /// The two unpackings are read off the box they unpack, and the round
    /// trip off the shape it collapses — each where a proof would point.
    #[test]
    fn the_new_rows_are_proposed_where_they_apply() {
        // Both readings of a coercion are offered at the one box they
        // read, and neither is a list's to drive.
        let mut graph = Graph::empty(1);
        let forced = graph.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)]);
        graph.close(forced);
        graph.check().unwrap();
        let offered: Vec<Law> = propose(
            &graph,
            &Law::every(),
            only(&NodeKind::Op(Prim::AsBool), &graph),
        )
        .iter()
        .map(|step| step.rule.law())
        .collect();
        for law in [Law::AsBoolBranch, Law::CoercionGuard] {
            assert!(
                offered.contains(&law),
                "{} is not offered at an `as_bool`",
                law
            );
            assert!(
                !folding().contains(&law)
                    && !structural().contains(&law)
                    && !branching().contains(&law),
                "{} grows a graph; no list should drive it",
                law
            );
        }

        // The round trip, with the coercion's port read by something else
        // as well — which is exactly what exporting it on both sides buys.
        let mut graph = Graph::empty(1);
        let coerced = graph.add(NodeKind::Op(Prim::AsTuple(2)), vec![Source::Input(0)]);
        let parts = graph.add(NodeKind::Op(Prim::Untuple(2)), coerced.clone());
        let rebuilt = graph.add(NodeKind::Op(Prim::Tuple(2)), parts);
        let elsewhere = graph.add(NodeKind::Op(Prim::IsTuple(None)), coerced);
        graph.close(vec![rebuilt[0], elsewhere[0]]);
        graph.check().unwrap();
        assert!(
            !graph.is_monogamous(),
            "the coercion is read twice:\n{}",
            graph
        );

        let steps = propose(
            &graph,
            &[Law::AsTupleRoundTrip],
            only(&NodeKind::Op(Prim::Tuple(2)), &graph),
        );
        let [step] = &steps[..] else {
            panic!("one round trip:\n{}", graph)
        };
        assert_eq!(step.rule, Rule::AsTupleRoundTrip { n: 2 });
        assert_eq!(
            step.at.nodes[0],
            only(&NodeKind::Op(Prim::AsTuple(2)), &graph),
            "the pattern is built coercion-first, so that is where it anchors"
        );
        apply(&mut graph, step).unwrap();
        graph.check().unwrap();

        // The untuple and the tuple went; the coercion stands, and both
        // readers of it — the one outside the window, and the boundary
        // output the rebuilt tuple used to serve — name it.
        assert_eq!(graph.live_count(), 2, "two boxes left:\n{}", graph);
        let coerced = Source::Port {
            node: only(&NodeKind::Op(Prim::AsTuple(2)), &graph),
            port: 0,
        };
        assert_eq!(graph.outputs()[0], coerced, "\n{}", graph);
        assert_eq!(
            graph.sources(only(&NodeKind::Op(Prim::IsTuple(None)), &graph)),
            [coerced],
            "\n{}",
            graph
        );
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
        // `at < arity` is the then side; both halves, and a wider branch
        // where the other blocks come from outside.
        for (arity, at) in [(1, 0), (1, 1), (2, 1), (2, 3)] {
            the_machine_agrees(Law::SpecializeBool, Rule::SpecializeBool { arity, at });
        }
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
        // `equal-refl`'s answer side is a box, and still declines: its
        // boundary input — the discarded wire — is one the pattern never
        // touches, so its image is a choice.
        let (_terms, graph) = built("push 1 push 2 add");
        let (_, rhs) = sides(&Rule::EqualRefl).unwrap();
        assert!(find(&graph, &rhs).is_empty());

        // `not-not` is the one right-hand side that is a box, and it reads
        // fine.
        let (_terms, graph) = built("as_bool");
        let (_, rhs) = sides(&Rule::NotNot).unwrap();
        assert_eq!(find(&graph, &rhs).len(), 1);
    }

    /// The walk can start anywhere: pinning any box of a side to its own
    /// image finds the identity embedding, and the answer comes back in
    /// pattern order whatever order the search visited it in.
    #[test]
    fn a_pattern_is_found_from_any_of_its_boxes() {
        for rule in table() {
            for side in {
                let (lhs, rhs) = sides(&rule).unwrap();
                [lhs, rhs]
            } {
                if !pins_itself(&side) {
                    continue;
                }
                for i in 0..side.nodes.len() {
                    assert!(
                        find_pinned(&side, &side, i, NodeId::at(i)).contains(&identity(&side)),
                        "{:?}: pinned at box {}, the identity was not found:\n{}",
                        rule.law(),
                        i,
                        side
                    );
                }
            }
        }
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

    // ---- the table, against a graph ----

    /// One payload per row of the table, and between them every law.
    fn table() -> Vec<Rule> {
        vec![
            Rule::IdElim { n: 2 },
            Rule::SwapElim,
            Rule::CopyElim { n: 1 },
            Rule::DeadNode {
                kind: NodeKind::Op(Prim::Add),
            },
            Rule::Dedup {
                kind: NodeKind::Op(Prim::Add),
            },
            Rule::NotNot,
            Rule::AndLiteral {
                literal: Side::Top,
                value: Value::Bool(true),
            },
            Rule::TupleCancel { n: 2 },
            Rule::AsTupleBuilt { n: 2 },
            Rule::EqualRefl,
            Rule::SelectSame { arity: 1, at: 0 },
            Rule::SelectConst {
                value: Value::Bool(false),
                arity: 1,
                lit_blocks: vec![1],
            },
            Rule::SpecializeEqual {
                arity: 1,
                at: 0,
                value: Value::Int(7),
                literal: Side::Top,
            },
            Rule::SpecializeBool { arity: 1, at: 0 },
            Rule::SpecializeChoice {
                arity: 1,
                inner: 1,
                moves: vec![(0, 0)],
            },
            Rule::Shannon {
                kind: NodeKind::Op(Prim::IsBool),
                body: one_step(NodeKind::Op(Prim::Not)),
            },
            Rule::SelectHoist {
                arity: 1,
                body: one_step(NodeKind::Op(Prim::Not)),
            },
            Rule::Fold {
                prim: Prim::Add,
                operands: vec![Value::Int(1), Value::Int(2)],
                reads: vec![0, 1],
            },
            Rule::PromisedBool {
                kind: NodeKind::Op(Prim::Not),
            },
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::IsInt),
            },
            Rule::Retuple { n: 2 },
            Rule::AsTupleRoundTrip { n: 2 },
            Rule::IsTupleBuilt { built: 2, asked: 2 },
            Rule::IsTupleBuilt { built: 2, asked: 3 },
            Rule::AsBoolBranch,
            Rule::CoercionGuard {
                prim: Prim::AsTuple(2),
            },
            Rule::CoercionGuard { prim: Prim::AsInt },
            Rule::CoercionGuard { prim: Prim::AsBool },
        ]
    }

    /// Every law there is, the lists included and the several they leave
    /// out — a driver holds `view-value` back on purpose, and the two
    /// unpackings grow a graph, so no list hands any of them out. Taken
    /// from the enum rather than rebuilt here, so a law added to the table
    /// is a law this file's round trips cover.
    fn every_law() -> Vec<Law> {
        Law::every()
    }

    /// Every proposal at every box of `graph`, applied to a copy of it and
    /// held to [`Graph::check`](super::Graph::check) — the laws it read off,
    /// in the order it read them.
    fn each_proposal(graph: &Graph, note: &str) -> Vec<Law> {
        let mut spent = Vec::new();
        for (id, _) in graph.live() {
            for step in propose(graph, &every_law(), id) {
                let law = step.rule.law();
                let mut copy = graph.clone();
                apply(&mut copy, &step)
                    .unwrap_or_else(|e| panic!("{}: {:?} proposed and refused: {}", note, law, e));
                copy.check().unwrap_or_else(|e| {
                    panic!("{}: {:?} left a torn graph: {}\n{}", note, law, e, copy)
                });
                spent.push(law);
            }
        }
        spent
    }

    /// Every law is read back off the very shape it states.
    ///
    /// [`sides`] turns a payload into the graph the law is about, and
    /// [`read_off`] is supposed to recognise that graph and hand a payload
    /// back. Running the two against each other closes the loop a law at a
    /// time: a matcher that drifts from the table stops recognising the
    /// table's own shapes, and says so here.
    ///
    /// The corpus cannot ask this. A graph fresh out of [`build`] has no
    /// shape that a rewrite made, so four of the branch laws — everything
    /// downstream of `select-view` — never match one at all, however many
    /// sentences are walked.
    #[test]
    fn a_law_is_read_back_off_the_shape_it_states() {
        // A law added to the table and not to the list above would be a row
        // nothing here reads back.
        let covered: Vec<Law> = table().iter().map(Rule::law).collect();
        for law in every_law() {
            assert!(
                covered.contains(&law),
                "{:?} has no payload in `table`",
                law
            );
        }
        for rule in table() {
            let law = rule.law();
            let (lhs, _) = sides(&rule).unwrap();
            let note = format!("{:?}", law);
            let spent = each_proposal(&lhs, &note);
            assert!(
                spent.contains(&law),
                "{:?}: the matcher does not read its own shape back:\n{}",
                law,
                lhs
            );
        }
    }

    /// A window inside a graph, with a port read more than once.
    ///
    /// This is the shape [`build`] never makes and every rewrite after the
    /// first `copy-elim` does, so it is the one the corpus could not offer
    /// either: a match's [`Match::outputs`] carries the *split* of a port's
    /// readers, and on a monogamous graph the split has only one way to go.
    /// Here it has two readers to divide, and both have to come out naming
    /// what the deleted box was reading.
    #[test]
    fn a_step_re_points_the_readers_the_window_does_not_hold() {
        let mut graph = Graph::empty(0);
        let nine = graph.add(NodeKind::Op(Prim::Push(Value::Int(9))), Vec::new());
        let wire = graph.add(NodeKind::Id(1), nine.clone());
        let not = graph.add(NodeKind::Op(Prim::Not), wire.clone());
        let negate = graph.add(NodeKind::Op(Prim::Negate), wire.clone());
        graph.close(vec![not[0], negate[0]]);
        graph.check().unwrap();
        assert!(!graph.is_monogamous(), "the point of the test:\n{}", graph);

        let id = only(&NodeKind::Id(1), &graph);
        let steps = propose(&graph, &[Law::IdElim], id);
        assert_eq!(steps.len(), 1, "one window, both readers in it");
        apply(&mut graph, &steps[0]).unwrap();
        graph.check().unwrap();

        // Both readers came out naming the `9`, and the wire is gone.
        let not = only(&NodeKind::Op(Prim::Not), &graph);
        let negate = only(&NodeKind::Op(Prim::Negate), &graph);
        let push = only(&NodeKind::Op(Prim::Push(Value::Int(9))), &graph);
        for reader in [not, negate] {
            assert_eq!(
                graph.sources(reader),
                [Source::Port {
                    node: push,
                    port: 0
                }],
                "a reader outside the window was left naming a deleted box:\n{}",
                graph
            );
        }
        assert_eq!(graph.live_count(), 3);
    }

    /// The same again on programs rather than on shapes: on a handful of
    /// sentences, every law that should be read off a box is, and every
    /// proposal applies and leaves the graph whole.
    ///
    /// Naming the laws is what makes this bite. A payload read off wrong
    /// states a shape the graph does not have, so it is never matched and
    /// never proposed — a rule going quiet is invisible to a test that only
    /// watches what *is* proposed, and the list is what notices.
    ///
    /// A handful is the point. This ran over the whole corpus once — 4302
    /// sentences, a quarter of a million proposals, two and a half minutes —
    /// and what it spent that on was repetition: the proposals came to 179
    /// distinct payloads, the last of them read off sentence 926, and half
    /// were `dedup` between two copies of one literal, which is quadratic in
    /// how many times a sentence pushes it.
    #[test]
    fn every_proposal_on_a_program_is_accepted() {
        // Between them, every law a built graph can offer. The four the
        // list cannot reach want a shape a rewrite makes, and are covered
        // above against the shapes the table itself states.
        // A fresh graph pads its literals behind `id` boxes, so the fold
        // has nothing to read until `id-elim` has fired — the value layer
        // only reaches a graph the structural layer has cleaned.
        offers("push 1 push 2 add", &[Law::IdElim]);
        offers("push 1 push 1 add", &[Law::IdElim, Law::Dedup]);
        offers("swap swap", &[Law::SwapElim]);
        offers("push 9 pick 0", &[Law::CopyElim]);
        offers(
            "dip { swap } swap dip { swap }",
            &[Law::IdElim, Law::SwapElim],
        );
        offers(
            "pick 1 pick 1 equal drop 0",
            &[
                Law::IdElim,
                Law::SwapElim,
                Law::CopyElim,
                Law::DeadNode,
                Law::PromisedBool,
                Law::Shannon,
            ],
        );
        offers(
            "branch { pick 0 drop 0 not } { not }",
            &[
                Law::IdElim,
                Law::CopyElim,
                Law::DeadNode,
                Law::PromisedBool,
                Law::Shannon,
            ],
        );
        offers(
            "pick 0 push 1 equal branch { not } { negate }",
            &[Law::IdElim, Law::CopyElim, Law::PromisedBool, Law::Shannon],
        );
        // One operation in both arms. It used to be the hoists' shape and
        // it is `copy-elim`'s now: a branch's views are a plain copy, so
        // the two `add`s come to read one source and `dedup` is what makes
        // them one box.
        offers("branch { add } { add }", &[Law::CopyElim]);
        offers(
            "push 1 pick 1 branch { add } { add }",
            &[Law::IdElim, Law::SwapElim, Law::CopyElim],
        );
        // Work after a branch, which is what `select-hoist` reads: the
        // region downstream of the select's answers, lifted out as the
        // body the branch grows over. Nothing about the condition is
        // asked, so this is the one row here that offers on a branch
        // whatever made the wire it turns on.
        offers(
            "branch { negate } { negate } negate",
            &[Law::CopyElim, Law::SelectHoist],
        );

        // A literal condition: the select is the blocks it chooses.
        offers(
            "push true branch { push 1 } { push 2 }",
            &[Law::SelectConst],
        );
    }

    /// The laws a body offers, and no others.
    fn offers(body: &str, want: &[Law]) {
        let (_terms, graph) = built(body);
        let spent = each_proposal(&graph, body);
        for law in want {
            assert!(
                spent.contains(law),
                "{}: {:?} was read off nothing:\n{}",
                body,
                law,
                graph
            );
        }
        for law in &spent {
            assert!(
                want.contains(law),
                "{}: {:?} was proposed and is not on the list",
                body,
                law
            );
        }
    }

    /// The vocabulary, checked against itself: every law spells one name,
    /// no two share a name, and every list a strategy drives is drawn
    /// from it. [`Law::name`]'s match is exhaustive, so a law added to
    /// the enum has to be named there; this is what makes it get added to
    /// [`Law::every`] as well, which is what [`crate::hant`] parses
    /// against.
    #[test]
    fn every_law_is_named_once() {
        let all = Law::every();
        assert_eq!(
            all.len(),
            25,
            "a law joined the table: name it, and list it in `Law::every`"
        );
        let mut names: Vec<&str> = all.iter().map(|law| law.name()).collect();
        names.sort_unstable();
        let spelled = names.len();
        names.dedup();
        assert_eq!(names.len(), spelled, "two laws share a spelling");
        for law in [structural(), branching(), folding()].concat() {
            assert!(all.contains(&law), "{:?} is on no vocabulary", law);
        }
    }

    /// [`instances`] answers which equations a law comes to in one graph,
    /// with the *where* left open — the payloads the graph's own boxes
    /// spell, and nothing it does not say.
    #[test]
    fn the_instances_of_a_law_are_the_payloads_the_graph_spells() {
        let (_terms, graph) = built("pick 1 pick 1 equal drop 0");

        // `dedup` carries a kind, so the instances are the kinds present
        // — each of them once, however many boxes spell it.
        let deduped: Vec<NodeKind> = instances(&graph, Law::Dedup)
            .into_iter()
            .map(|rule| match rule {
                Rule::Dedup { kind } => kind,
                other => panic!("{:?} is not a dedup", other),
            })
            .collect();
        for (_, kind) in graph.live() {
            assert!(
                matches!(kind, NodeKind::Select { .. }) || deduped.contains(kind),
                "no `dedup` payload for {:?}",
                kind
            );
        }
        for kind in &deduped {
            assert!(
                graph.live().any(|(_, live)| live == kind),
                "{:?} is a payload no box spells",
                kind
            );
            assert_eq!(
                deduped.iter().filter(|other| *other == kind).count(),
                1,
                "{:?} twice",
                kind
            );
        }

        // And a law no box witnesses comes to nothing: there is no
        // `tuple` here, so no `tuple-cancel` payload to read.
        assert!(instances(&graph, Law::TupleCancel).is_empty());

        // Every instance is an equation that builds, which is what makes
        // it something to look for on either side.
        for law in Law::every() {
            for rule in instances(&graph, law) {
                assert_eq!(rule.law(), law);
                sides(&rule).unwrap_or_else(|e| panic!("{:?}: {:?}", rule, e));
            }
        }
    }
}
