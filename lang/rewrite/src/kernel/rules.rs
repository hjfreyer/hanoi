//! The table: each law a pair of graphs the module says are the same
//! program, and a rewrite the business of pointing at one and swapping in
//! the other.
//!
//! [`super`] builds a graph and stops there; nothing shrinks one but a
//! strategy, and a strategy belongs to whoever is proving something
//! rather than to the module the graph lives in. So what is here is the
//! page — this module is the thing `rewrite/src/rules.rs` was for terms,
//! over graphs instead — and the handful of operations a driver is built
//! out of: [`sides`], [`find`](crate::kernel::graph::find), [`propose`],
//! [`apply`], [`replay`]. A law is a row anyone can read, and adding one
//! is not editing an engine.
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
//! What a rule *wants* is said in its pattern rather than tested for:
//! [`Law::SelectHoist`] exports its body's outputs and never the select's
//! answers, and carries the region it moves as payload;
//! [`Law::SelectLiteral`] carries its arms. Nothing asks a question a
//! match could answer.
//!
//! What a pattern does **not** say is *and nothing else reads this*. A
//! rewrite replaces the value a window exports and rebuilds whatever read
//! it, so a reader the window never mentioned is not a loose end:
//! `not-not` fires on a first `not` somebody else reads, and that
//! somebody goes on reading it.
//!
//! ## Which laws are here
//!
//! Not the wiring. `id-elim`, `swap-elim`, `copy-elim`, `dead-node` and
//! `dedup` are not rows and could not be: there is no graph for either
//! side of them to be. A box is its kind and the sources it reads, so a
//! value read twice is two references, a value read never is a box the
//! boundary does not reach, and two boxes computing the same thing are
//! one box. [docs/rules.md](../../../../docs/rules.md) opens with the
//! whole list, the associativities and Yang–Baxter among them.
//!
//! [`Law::Commute`] is the one that looks like wiring and is not. A
//! crossing is not recorded, so everything about `swap` is unstatable —
//! but *which operand of a box is which* is recorded, so
//! `swap ; op = op` for a commutative `op` is a claim the graph can make
//! and only the instruction set can settle. The row is about the operand
//! order and never mentions a crossing.
//!
//! What is here is the two things the representation cannot decide: what
//! a branch means ([`branching`]) and what an operation computes
//! ([`folding`]). [`Law::NotNot`] — `not ; not = as_bool` — is the elder
//! of the second: nothing about the wiring relates `not(not(x))` to
//! `as_bool(x)`, so this is a law about what the machine computes, and
//! `vm` is what measures it.
//!
//! ## One row for a family
//!
//! Three rows read a **fact off the instruction set** rather than naming
//! an instruction, and each stands for what would otherwise be a family:
//! [`Law::Commute`] over
//! [`commutative`](bytecode::Instruction::commutative), [`Law::Idem`] over
//! [`idempotent`](bytecode::Instruction::idempotent), and
//! [`Law::TestedBool`] over
//! [`yields_bool`](bytecode::Instruction::yields_bool) and whichever type
//! test it is asked with. `idem` is the three coercions and `comm` the
//! five operators that answer either way round, and neither list is
//! written here: `vm` measures both, the way it measures every other fact
//! about what the machine does, and a row per member would be several
//! copies of one sentence with a fourth to write whenever the instruction
//! set grew one.
//!
//! ## The value layer, and the two rows no list drives
//!
//! [`folding`] is the value layer: what an operation *computes*, with
//! the machine itself as the judge — [`Law::Fold`] runs a literal window on
//! `vm`, and the rest are facts about particular instructions.
//!
//! Two of them are about a value the window watched being **built**, which
//! is a shape the window knows without asking the machine anything:
//! [`Law::AsTupleBuilt`] says coercing it changes nothing, and
//! [`Law::IsTupleBuilt`] says testing its width answers. The second is what
//! lets the compiler's `type` and `enum` guard be `pick 0 ; is_tuple n`
//! rather than a coercion compared against a copy — see
//! [docs/totality.md](../../../../docs/totality.md), where that guard has now
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
//! graph for a different reason: it duplicates a **region**, which it
//! carries as payload. What it says is `select(C, T, E) ; A = select(C, T ; A, E ; A)` — the
//! commuting conversion, what runs *after* a branch runs inside whichever
//! arm the branch takes. Said as a composition on purpose: the answers
//! are read inside the window, and what the rewrite replaces is what `A`
//! leaves — an answer read from outside the carried region keeps the
//! select it always read.
//!
//! A branch grows *backwards* for free: work in front of one is shared by
//! both arms as a matter of naming, and doing it twice is having it once.
//! This is the same freedom at the other end —
//! without it everything downstream of a select is out of the branch
//! layer's reach, and a select can be deleted but never moved.
//!
//! Nothing is **pinned**: the branch is already there, its condition wire
//! is passed to the moved select untouched, and the only thing assumed
//! about that wire is the truthiness a select was reading anyway. So it
//! holds of **any** branch, whatever computed the condition — a promise
//! about the condition is [`case_split`]'s business, and this row has
//! none.
//!
//! [`Law::CondHoist`] is the same conversion at the one port that row
//! cannot reach without carrying the branch it moves — the
//! **condition**: `select(select(C, T1, E1), T2, E2)` is
//! `select(C, select(T1, T2, E2), select(E1, T2, E2))`. It is a row
//! rather than a payload of its sibling because the window is narrower.
//! `select-hoist` carries a region, and the region [`propose`] reads is
//! the whole cone below a select, so growing a branch past another that
//! way copies everything after it too; here there is no payload at all —
//! both selects are one answer wide — and what the far side copies is one
//! select. It grows a graph all the
//! same — two boxes into three — so no list drives it either, and the
//! `tree` tactic spends the two in order: every branch past everything
//! but another branch, and then out of every condition a branch
//! answered.
//!
//! ## The branch layer, and where it reaches
//!
//! [`branching`] is the branch layer: [`Law::SelectSame`],
//! [`Law::SelectLiteral`], [`Law::NotBranch`], [`Law::SpecializeEqual`],
//! [`Law::SpecializeBool`] and [`Law::SpecializeChoice`]. Between them they
//! fold a literal condition into the blocks it chooses, delete a branch
//! whose arms answer alike, swallow a negation into the arms it exchanges,
//! and write what a test decided into the block that tested it.
//!
//! Every one of them is stated at the `select`, because a `select` is the
//! whole of what a branch is. Lifting work both arms do out in front is
//! not among them, and is not a rewrite at all: both arms are handed the
//! same sources, so the same work done in both is one box from the moment
//! it is written. `branch { A } { A } = drop-top ; A` is `select-same`
//! and nothing else.
//!
//! ### The case split is not a row
//!
//! η — `body(w) = if w { body(true) } else { body(false) }`, for a wire
//! the instruction set promises is a bool — was a row of its own once,
//! and is not one. It is three rows the table already has, spent in
//! order, and [`case_split`] is that composite:
//!
//! ```text
//! body(w)                               promised-bool
//!   = body(as_bool w)                   as-bool-branch
//!   = body(select(w, true, false))      select-hoist
//!   = select(w, body(true), body(false))
//! ```
//!
//! Each step contributes one part of what the row used to say at once.
//! [`Law::PromisedBool`] is where the **promise** is spent, and it is the
//! only step of the three that asks anything of the wire — asking is the
//! whole of what the old row's refusal was. [`Law::AsBoolBranch`] is
//! where the **pin** appears: the branch a coercion is reads the wire
//! itself and answers with the two literals, so a copy under the `true`
//! block reads `true` and a copy under the `false` block reads `false`.
//! [`Law::SelectHoist`] moves the **region** over that branch, and the
//! cone it reads is the cone the old row carried — so what the three
//! steps leave is what the one step left, box for box.
//!
//! One reading is not the same afterwards, and it is the coercion's: a
//! wire the host boundary reads *directly* used to come out of the split
//! untouched, and now comes out as `select(w, true, false)`, which is
//! `as_bool w`, which is `w` for a wire that was promised to be one. The
//! reading the old row wanted there is gone with it, and
//! [`downstream_of`] has one meaning again rather than a flag.
//!
//! ### What a block is, and what a window may say about one
//!
//! A block is a wire like any other, and nothing stands between an arm and
//! what it reads. So a block that is the very value the condition tested
//! *is* that value, and [`Law::SpecializeEqual`] says so by naming its
//! sources twice in its pattern — the operands of the `equal` are the two
//! blocks — which is why these rules are as short as they are.
//!
//! What licenses them is the **discard** — the fact that the select throws
//! the untaken block away — and the discard is at the select, which is
//! where they are stated. So what they reach is a block, and not the inside
//! of an arm: the bool a branch turned on becomes `true` where the select
//! reads it, while the boxes of the then arm go on reading the value
//! itself. A rule that
//! reached inside would have to say which boxes are the arm's own, and
//! nothing in the graph records that — a branch's arms are the boxes only
//! that side's blocks read, which is a fact about the whole graph rather
//! than about a window.
//!
//! [`Law::SpecializeBool`] holds one box more than the branch: the
//! `as_bool` that made the condition. A bool is the one kind of condition
//! whose truthiness *is* its value, and having the coercion in the window
//! is how the rule says the condition is one — without it a condition of
//! `5` is truthy and its then block reads `5`, not `true`.
//! [`Law::PromisedBool`] is what puts the coercion there, which is the
//! whole use of writing an instruction set's promise down as a box.
//!
//! ## Where the trust sits
//!
//! [`sides`] is the whole of this module's share: it builds the table, and
//! what it builds is a [`Pair`], which [`crate::kernel::graph`] holds to being
//! splice-able before anything is put down. The checking a rewrite needs —
//! a claimed embedding held to agreeing at every port, then the re-pointing
//! — is [`Pair::apply`], and [`apply`] is that with a law's name attached.
//! [`find`](crate::kernel::graph::find) and [`propose`] are search, they are wrong
//! the way a bad guess is wrong, and every answer they give goes through
//! `apply` anyway.
//!
//! [`find`](crate::kernel::graph::find) is partial, in the two places a pattern does
//! not pin its own match: a pattern with **no boxes** has nothing to anchor
//! on (`tuple-cancel`'s right side, say, which is `id(n)` outright), and a
//! pattern with a boundary input **nothing in it reads** cannot say which
//! wire that input stands for. A step at such a side is stated rather than
//! searched for — which is exactly why [`Match`] is a claim anyone may
//! write down.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::kernel::graph::{
    Direction, Embedding, Graph, Match, Mismatch, NodeId, NodeKind, Pair, Sink, Source, Unpaired,
    check_match, find_at, lift,
};
use bytecode::{Instruction, Library, SentenceIndex, Value};

use crate::kernel::term::{Arity, Prim};

// ---- the laws --------------------------------------------------------------------

/// Which equation, with its blanks still open.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Law {
    NotNot,
    AndLiteral,
    OrLiteral,
    TupleCancel,
    AsTupleBuilt,
    EqualRefl,
    // The branch layer. Every one of these is stated at the `select`, with
    // the condition in its own window — see the module docs for why that is
    // the only place some of them can be stated soundly at all.
    SelectSame,
    SelectLiteral,
    NotBranch,
    SpecializeEqual,
    SpecializeBool,
    SpecializeChoice,
    SelectHoist,
    CondHoist,
    // The value layer: what an operation computes, measured on the machine.
    PromisedBool,
    Fold,
    TestedBool,
    Retuple,
    AsTupleRoundTrip,
    IsTupleBuilt,
    // The two rows read off a fact about the instruction rather than off a
    // particular one: doing it twice, and doing it the other way round.
    Idem,
    Commute,
    // The two unpackings: a coercion said as the program it is. Both grow
    // a graph, so no list drives them — see [`folding`].
    AsBoolBranch,
    CoercionGuard,
    // Definitional unfolding: a call is its body. Not a law of the table
    // but a fact of the library, and the one row whose payload the kernel
    // holds to the library before it is spent — see [`Rule::Open`].
    Open,
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
            Law::NotNot => "not-not",
            Law::AndLiteral => "and-literal",
            Law::OrLiteral => "or-literal",
            Law::TupleCancel => "tuple-cancel",
            Law::AsTupleBuilt => "as-tuple-built",
            Law::EqualRefl => "equal-refl",
            Law::SelectSame => "select-same",
            Law::SelectLiteral => "select-literal",
            Law::NotBranch => "not-branch",
            Law::SpecializeEqual => "specialize-equal",
            Law::SpecializeBool => "specialize-bool",
            Law::SpecializeChoice => "specialize-choice",
            Law::SelectHoist => "select-hoist",
            Law::CondHoist => "cond-hoist",
            Law::PromisedBool => "promised-bool",
            Law::Fold => "fold",
            Law::TestedBool => "tested-bool",
            Law::Retuple => "retuple",
            Law::AsTupleRoundTrip => "as-tuple-round-trip",
            Law::IsTupleBuilt => "is-tuple-built",
            Law::Idem => "idem",
            Law::Commute => "comm",
            Law::AsBoolBranch => "as-bool-branch",
            Law::CoercionGuard => "coercion-guard",
            Law::Open => "open",
        }
    }

    /// Every law of the table, in the order the enum declares them.
    ///
    /// Not a list to *drive* — [`structural`], [`branching`] and
    /// [`folding`] are the lists a strategy spends. This is the
    /// vocabulary: what a name can resolve to, and what a table of names is
    /// checked against. [`Law::Open`] is not in it: it is a fact of the
    /// library rather than a row of the table, nothing reads one off a
    /// box, and no strategy spells it — `inline` states it.
    pub fn every() -> Vec<Law> {
        vec![
            Law::NotNot,
            Law::AndLiteral,
            Law::OrLiteral,
            Law::TupleCancel,
            Law::AsTupleBuilt,
            Law::EqualRefl,
            Law::SelectSame,
            Law::SelectLiteral,
            Law::NotBranch,
            Law::SpecializeEqual,
            Law::SpecializeBool,
            Law::SpecializeChoice,
            Law::SelectHoist,
            Law::CondHoist,
            Law::PromisedBool,
            Law::Fold,
            Law::TestedBool,
            Law::Retuple,
            Law::AsTupleRoundTrip,
            Law::IsTupleBuilt,
            Law::Idem,
            Law::Commute,
            Law::AsBoolBranch,
            Law::CoercionGuard,
        ]
    }

    /// Whether this law's payload is a **region** — a piece of the host
    /// lifted out whole, rather than the widths and kinds every other
    /// payload is.
    ///
    /// One law is: [`Law::SelectHoist`], whose body [`read_off`] builds
    /// out of the cone below the box it is anchored at. That has a
    /// consequence for anything looking for one, and it is the reason
    /// this is asked. Every other law's window is a
    /// handful of boxes that are all *the law's own* — either `not` of
    /// `not ; not` is the pair, and naming either is naming that window.
    /// A region-carrying law's window is one box the law is about and a
    /// whole cone it merely carries, so a box in the cone is not a
    /// second name for the same equation: it is a box some *other*
    /// branch's equation would carry too. Naming it would say nothing
    /// about which branch was meant.
    ///
    /// So it is **anchored**: the box a driver names is the box the
    /// payload is read off, which is what [`propose`] already answers.
    pub fn carries_a_region(self) -> bool {
        matches!(self, Law::SelectHoist)
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
/// Widths a payload determines are not carried — a rule reads them off the
/// kinds it names, because carrying them as well would let a rule state a
/// pair whose two halves disagree.
#[derive(Debug, Clone, PartialEq)]
pub enum Rule {
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
    /// The literal is inside the window and not part of the equation: the
    /// rewrite replaces the `and`'s answer, and a deduped literal with
    /// readers of its own goes on standing for them. One the `and` alone
    /// read is left unreachable, which is the whole of deletion here.
    ///
    /// This is the row that lets a case split spend a **conjunction**: a
    /// guard `and(a, b)` branch-tested as one opaque bool decomposes only
    /// when a split on `a` can fold the `and` its literal leaves behind.
    ///
    /// `literal` names the operand the pushed value feeds — the payload
    /// carries which, so the two sides of the equation agree on where the
    /// boundary input sits.
    AndLiteral { literal: Side, value: Value },
    /// `or` with a literal operand, which is [`Rule::AndLiteral`] read
    /// through the other connective and decided by the same `truthy`. The
    /// poles swap, and nothing else does: the one **falsy** value
    /// contributes only the coercion, so the answer is `as_bool` of the
    /// other operand, and a truthy literal decides the whole answer —
    /// `push true`, the other operand discarded.
    ///
    /// Everything the sibling row says about the window holds here for the
    /// same reasons: the literal is not part of the equation; the discard
    /// is the one totality and purity license; and this is what lets a case
    /// split spend a **disjunction** one disjunct at a time.
    ///
    /// `literal` names the operand the pushed value feeds.
    OrLiteral { literal: Side, value: Value },
    /// Taking apart what `tuple n` built answers the built elements:
    /// `tuple n ; untuple n = id(n)` — tuple cancellation. The rewrite
    /// re-points the untuple's readers at the element wires; the tuple is
    /// not part of the equation, and in a host it goes on standing for
    /// whoever else reads it, since a substitution deletes nothing. The
    /// machine's promise that `untuple` inverts `tuple` exactly is what
    /// makes this a row rather than wiring.
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
    /// answer side leaves it unread, the discard totality licenses.
    EqualRefl,

    // ---- the branch layer ----
    /// A block a `select` answers with either way is what it answers: `if c
    /// then x else x = x`. A branch answering one thing either way is not
    /// a branch, so the select goes with the block, and the condition
    /// drops out of the program with it.
    ///
    /// The row that `branch { A } { A } = drop-top ; A` comes to: the two
    /// arms' boxes are one by interning, and a condition nothing else
    /// reads drops out of the program with the select.
    SelectSame,
    /// β: a literal condition is the blocks it chooses. Sound on **every**
    /// value and not only on booleans, because `truthy` is total: `false`
    /// is the one falsy value and everything else takes the then block.
    ///
    /// The untaken arm is outside the window: its boxes lose their one
    /// reader when the select goes, and a box the boundary no longer
    /// reaches is not part of the program.
    ///
    /// `lit_blocks` names which of the two blocks — 0 the then, 1 the else
    /// — read the **literal itself**, the shape a `dedup` makes when the
    /// condition and an answer are one pushed value, because a boundary
    /// input may not stand for a port inside the window.
    SelectLiteral {
        value: Value,
        lit_blocks: Vec<usize>,
    },
    /// A negated condition is the branch with its arms the other way
    /// round: `not ; if { A } else { B } = if { B } else { A }`.
    ///
    /// `not v` is `Bool(!truthy(v))`, and `false` is the one falsy value —
    /// so `not v` is truthy exactly where `v` is falsy, and the two selects
    /// choose opposite blocks of the very same pair. Sound on **every**
    /// value and not only on bools, for the reason
    /// [`Rule::SelectLiteral`] is: a select reads truthiness and `not`
    /// answers it.
    ///
    /// The `not` is inside the window and not exported: the row swaps
    /// only the blocks this select chose between, and a negation
    /// something else reads goes on standing for that reader.
    ///
    /// No payload: a select has two blocks and both move, since the branch
    /// decided them the other way round.
    NotBranch,
    /// A branch that answers with one operand of its own `equal` where the
    /// test held and the other where it did not is answering with the
    /// second, whatever the test said:
    ///
    /// ```text
    /// select(equal(x, y), y, x)  =  x
    /// ```
    ///
    /// `equal` answers `Bool(a == b)` and is structural identity on every
    /// value the machine has, so a truthy condition is `x == y` and
    /// nothing weaker — the then block *is* the else block wherever the
    /// then block is reached. The two are one value there, and the branch
    /// is choosing between a value and itself.
    ///
    /// Stated at the select, and it has to be: one end of a branch cannot
    /// see the **discard** — the fact that the select throws the untaken
    /// block away — and reasoning from "the condition holds" is exactly
    /// what the discard licenses. What it reaches is a block, not the
    /// inside of an arm.
    ///
    /// The select goes, like [`Rule::SelectSame`]'s, and the `equal` in a
    /// host goes on standing for whatever else reads it. `answered` says
    /// which operand of the `equal` the else block is — the one the
    /// equation comes to — and the then block is the other. Both readings
    /// are the same row, because `equal` reads its operands the same way
    /// round: the mirror shape `select(equal(x, y), x, y)` is `y`.
    SpecializeEqual { answered: Side },
    /// The very value a branch tested, when it is a **bool**, is what the
    /// branch decided: `true` in the then block, `false` in the else block.
    /// A truthy bool is `true` and a falsy one is `false` — there is
    /// nothing else for it to be — so both halves are exact.
    ///
    /// The **`as_bool` is in the window**, and that is the side condition:
    /// it sits where the condition is made, and its being there is what
    /// says the condition is a bool. Without it the rule would be false — a
    /// condition of `5` is truthy, and the then block would read `5` rather
    /// than `true`. [`Law::PromisedBool`] is the row that puts one there,
    /// which is the whole use of writing an instruction set's promise down
    /// as a box.
    ///
    /// `then` says which block is the coercion's answer, and so which
    /// literal this folds to: `true` on the then side, `false` on the else.
    SpecializeBool { then: bool },
    /// A branch **inside an arm** whose condition is the very value the
    /// outer branch tested is already decided: its then blocks in the outer
    /// then arm, its else blocks in the outer else arm — the same value
    /// tested twice answers the same, and `false` is the one falsy value.
    ///
    /// [`Rule::SpecializeBool`] with the inner `select` where the `as_bool`
    /// was, and stated at the outer select for the same reason: that is
    /// where the discard is, and the discard is what makes reasoning from
    /// "the condition held" sound. The inner select stays — only the outer
    /// blocks that read its answers come to read the blocks it would
    /// choose.
    ///
    /// `side` says which block of the outer branch this is about, and that
    /// is the whole payload: both selects are one answer wide, so which
    /// block of the inner one the move comes to is what `side` already
    /// said. Reasoning from "the condition held" does not reach the other
    /// block, which is why the row is about one side at a time.
    SpecializeChoice { side: bool },
    /// The commuting conversion, as an equation: what runs **after** a
    /// branch runs inside whichever arm the branch takes.
    ///
    /// ```text
    /// select(C, T, E) ; A  =  select(C, T ; A, E ; A)
    /// ```
    ///
    /// Written as a composition: the answers are read inside the window,
    /// and what the rewrite replaces is what `A` leaves. `A` may read
    /// wires that are not answers, so in full it is
    /// `(select(C, T, E) * id(k)) ; A`, and `k` is what `body` carries
    /// past the answers.
    ///
    /// A branch grows *backwards* for free: work in front of one is shared
    /// by both arms as a matter of wiring, and two boxes doing it twice are
    /// one box by `dedup`. Nothing said the same at the select's end, so a
    /// branch could never grow **forwards**: everything downstream of a
    /// select was beyond the reach of the whole branch layer, and a select
    /// could only ever be got rid of, never moved. This is that row.
    ///
    /// `body` is `A` — the region downstream of the answer, carried as
    /// payload the way [`Rule::SelectLiteral`] carries its arms. Its
    /// inputs `0..n` are the answers, its inputs `n..n+k` are the `id(k)`
    /// alongside them, and its outputs are what the region leaves.
    ///
    /// **Nothing is pinned.** The condition wire is untouched — the same
    /// value governs the select on either side of the equation — so
    /// nothing is assumed about it beyond the truthiness a select reads,
    /// and **any** branch splits, whatever made its condition. Running
    /// both copies and keeping one is the licence every branch spends:
    /// total, pure, the untaken copy an answer nobody reads. Pinning a
    /// wire to a literal is what [`case_split`] does, and it spends a
    /// promise for it; this row spends none.
    ///
    /// The interface says what the rewrite replaces: the left side
    /// exports `body`'s outputs and never the select's answers, so the
    /// substitution re-points what the region leaves and nothing else.
    /// An answer read from outside the carried region is no obstacle —
    /// the old select goes on standing for that reader — and
    /// `downstream_of` hands an answer the host boundary reads back as
    /// one of `body`'s own outputs, passed straight through, so the new
    /// select chooses between the blocks the old one chose between.
    ///
    /// Like the two unpackings, it **grows** a graph, so no list drives
    /// it and a proof names where to spend it.
    SelectHoist { body: Graph },
    /// The same conversion at the one port [`Rule::SelectHoist`] cannot
    /// reach without carrying the branch it moves: the **condition**.
    ///
    /// ```text
    /// select(select(C, T1, E1), T2, E2)
    ///   =  select(C, select(T1, T2, E2), select(E1, T2, E2))
    /// ```
    ///
    /// A branch whose condition is what another branch answered runs
    /// under that branch instead, once per block it chooses between —
    /// and each copy turns on the block itself, which is the value the
    /// inner select was going to hand over anyway. Sound for the reason
    /// every row of this layer is: a select keeps the block `truthy`
    /// picks, so on a truthy `C` both sides are `select(T1, T2, E2)` and
    /// on a falsy one both are `select(E1, T2, E2)`. Nothing is pinned
    /// and nothing is promised about any wire — `C`, `T1` and `E1` reach
    /// the selects that read them untouched — so this holds of **any**
    /// two branches.
    ///
    /// No payload: both branches are one answer wide, so there is nothing
    /// left to say — not which answer the condition is, and not how wide
    /// either select is. Whatever else reads the inner branch is no part
    /// of the window, and the box goes on standing for those readers.
    ///
    /// The sibling of [`Rule::SelectHoist`] and a narrower window than
    /// one, which is the whole of why it is a row. `select-hoist` carries
    /// a *region* as payload, and [`propose`] reads that region as the
    /// select's whole downstream cone: hoisting past a branch that way
    /// duplicates everything after it as well. Here the payload is three
    /// widths, the window is two boxes, and what the far side copies is
    /// one select and nothing else. Like its sibling it **grows** a graph
    /// — two boxes become three — so no list drives it and a proof names
    /// where to spend it.
    CondHoist,

    // ---- the value layer ----
    /// An operation on literal operands is the answer the machine gives:
    /// the fold, run on the machine itself so there is no second semantics
    /// to drift. [`sides`] executes the window and **builds** the answer
    /// side from what came back — a payload does not carry an answer it
    /// could lie about.
    ///
    /// `operands` are the distinct literals in the window and `reads[i]`
    /// names the one the operation's input `i` reads, so one literal read
    /// twice (`equal` after a `dedup`) is one box in the pattern.
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
    /// branch decided about the value it tested, and it says it of a
    /// condition an `as_bool` made — the coercion being how an arbitrary
    /// truthy value becomes the bool the branch settled. A condition that
    /// is *already* a bool carries no coercion, so the rule cannot see it.
    /// Spending this law first puts one there.
    ///
    /// Nothing about the equation needs a side condition: it is true of a
    /// promised bool however many `as_bool`s already stand on it. Not
    /// re-proposing it forever is [`propose`]'s business, and search is
    /// where a termination argument belongs.
    PromisedBool { kind: NodeKind },
    /// A type test of an answer the instruction set promises is a bool is
    /// **decided**, and the answer itself is untouched: `op ; is_T` folds
    /// the test to `push (T is Bool)`. The promise is
    /// [`yields_bool`](bytecode::Instruction::yields_bool), measured by
    /// `vm`; the rewrite replaces only the test's answer, and `op` goes on
    /// standing for whoever else reads it.
    ///
    /// One row for the whole family, because one fact answers all of it. A
    /// codomain does not only say which test succeeds — it says which
    /// tests **fail**, and the failures are worth as much: `op ; is_int` is
    /// `push false` on a promised bool, and that is what folds a shape
    /// guard asking the wrong question. `test` is which test, and the
    /// answer is read off it and the promise together.
    ///
    /// `is_tuple` is a test at either reading, the width-blind one
    /// included: a `Bool` is no tuple of any width, so both answer `false`.
    /// A `prim` that is no type test at all states no equation here.
    TestedBool { kind: NodeKind, test: Prim },
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
    /// `retuple` and `idem` reach the same place in two steps — the tail
    /// becomes a second `as_tuple n`, and the pair collapses — where the
    /// whole window is one; [`folding`] lists this row first so the longer
    /// window wins. The coercion itself is not part of the equation: the
    /// rewrite replaces the rebuilt tuple's value, and the coercion goes
    /// on standing for whoever else reads it.
    AsTupleRoundTrip { n: usize },
    /// Asking a value `tuple m` built whether it is a tuple of width `n`
    /// is asking whether `m` is `n`: `tuple m ; is_tuple n` = `tuple m ;
    /// push (m == n)`.
    ///
    /// The sibling of [`Rule::AsTupleBuilt`], and it exists for the same
    /// reason: a value the window watched being built has a shape the
    /// window knows, so a test of that shape is decided rather than
    /// computed. `as-tuple-built` says the coercion changes nothing; this
    /// says the test answers. The tuple itself is untouched either way,
    /// standing for whatever else reads it.
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
    /// Doing it twice is doing it once: `op ; op = op`, for any `op` the
    /// instruction set says is
    /// [idempotent](bytecode::Instruction::idempotent).
    ///
    /// One row for a family, and the family is the three coercions —
    /// `as_bool ; as_bool`, `as_int ; as_int`, `as_tuple n ; as_tuple n`.
    /// Which is no accident and is also not this module's to know: a
    /// coercion's whole content is its **codomain**, so what it leaves is
    /// already of the type it forces; the fact lives on the instruction and
    /// `vm` measures it, the way it measures
    /// [`commutative`](bytecode::Instruction::commutative) and
    /// [`yields_bool`](bytecode::Instruction::yields_bool). A row per
    /// coercion would be three copies of one sentence and a fourth to write
    /// whenever the instruction set grew one.
    ///
    /// The middle port is not exported, for [`Rule::NotNot`]'s reason: the
    /// equation is about the composite's answer, and a first coercion
    /// something else reads goes on standing for that reader. Backwards it
    /// is the clone — one box becomes two — which is what a proof wants
    /// when the shape it is heading for spells the coercion twice.
    ///
    /// The width rides in `kind`, as it does everywhere: `as_tuple 2 ;
    /// as_tuple 3` is two different questions and no instance of this at
    /// all.
    Idem { kind: NodeKind },
    /// The other way round is the same answer: `swap ; op = op`, for any
    /// `op` the instruction set says is
    /// [commutative](bytecode::Instruction::commutative).
    ///
    /// A crossing is not a box — two names in the other order is all a
    /// `swap` is — so what this equation relates is one box reading `(a,
    /// b)` and one box reading `(b, a)`, and the `swap` of the surface
    /// spelling has nowhere to appear. That is also why the row is *needed*
    /// where the wiring laws are not: the operands are recorded, so their
    /// order is something the graph says, and only the instruction set can
    /// say it does not matter.
    ///
    /// The junk answer commutes too, which is what makes the fact total:
    /// `add` on a symbol and an int has no sum to give whichever order they
    /// arrive in, and answers `0` both ways.
    ///
    /// **No list drives it.** It neither grows a graph nor shrinks one — it
    /// permutes, and a driver run to fixpoint would swap the same two
    /// operands forever. So a proof names it, `fire(comm)` or `at(#box,
    /// comm)`, the way it names an unpacking.
    Commute { kind: NodeKind },
    /// `as_bool` is the branch it is: `as_bool x = if x { true } else
    /// { false }`.
    ///
    /// [`Instruction::AsBool`](bytecode::Instruction::AsBool) is
    /// [`truthy`](bytecode::Value::truthy) made into an instruction, and a
    /// `select` keeps the block `truthy` says — so the two are the same
    /// program by construction, with the arms answering the two values
    /// `truthy` can report. Nothing is read inside either arm, so the
    /// branch is the `select` and the two literals, and nothing else.
    ///
    /// This is the unpacking that puts a *decision* where a coercion
    /// stood, which is what a proof about the two cases of a truthiness
    /// test needs: after it, the ordinary branch layer can specialize each
    /// arm, and `select-literal` can fold the whole branch away wherever
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
    /// A call is its body: `call target = body`, definitional unfolding
    /// said as the pair it is — the call's own one-box window against the
    /// graph of the sentence it names.
    ///
    /// The one payload that carries a *graph the library determines*
    /// rather than widths and kinds. [`sides`] builds the pair from the
    /// payload like every other row and asks nothing of the library, so
    /// a step stating a wrong body is a well-formed rewrite by a false
    /// equation — which is why the kernel's judgement,
    /// [`certify`](crate::kernel::goal::certify), holds every `Open` it
    /// replays to the body the library lowers before spending it. Nothing
    /// proposes one: `read_off` has no library to read a body from, and
    /// opening calls is a proof step (`inline`) rather than a law a
    /// strategy drives.
    Open { target: SentenceIndex, body: Graph },
}

impl Rule {
    /// Which row of the table this is an instance of.
    pub fn law(&self) -> Law {
        match self {
            Rule::NotNot => Law::NotNot,
            Rule::AndLiteral { .. } => Law::AndLiteral,
            Rule::OrLiteral { .. } => Law::OrLiteral,
            Rule::TupleCancel { .. } => Law::TupleCancel,
            Rule::AsTupleBuilt { .. } => Law::AsTupleBuilt,
            Rule::EqualRefl => Law::EqualRefl,
            Rule::SelectSame => Law::SelectSame,
            Rule::SelectLiteral { .. } => Law::SelectLiteral,
            Rule::NotBranch => Law::NotBranch,
            Rule::SpecializeEqual { .. } => Law::SpecializeEqual,
            Rule::SpecializeBool { .. } => Law::SpecializeBool,
            Rule::SpecializeChoice { .. } => Law::SpecializeChoice,
            Rule::SelectHoist { .. } => Law::SelectHoist,
            Rule::CondHoist => Law::CondHoist,
            Rule::Fold { .. } => Law::Fold,
            Rule::PromisedBool { .. } => Law::PromisedBool,
            Rule::TestedBool { .. } => Law::TestedBool,
            Rule::Retuple { .. } => Law::Retuple,
            Rule::AsTupleRoundTrip { .. } => Law::AsTupleRoundTrip,
            Rule::IsTupleBuilt { .. } => Law::IsTupleBuilt,
            Rule::Idem { .. } => Law::Idem,
            Rule::Commute { .. } => Law::Commute,
            Rule::AsBoolBranch => Law::AsBoolBranch,
            Rule::CoercionGuard { .. } => Law::CoercionGuard,
            Rule::Open { .. } => Law::Open,
        }
    }
}

/// The branch layer: the laws stated at one end of a branch or the other.
///
/// Kept out of [`structural`], for the reason [`Law::NotNot`] is kept out of
/// it. Three of these turn on what an operation *computes* — which
/// values are truthy, that `equal` is identity, that `as_bool` is `truthy` —
/// and nothing about the wiring settles any of them. `vm` is the judge for
/// those, and the tests call it.
///
/// The rest are pure wiring; they are here rather than in [`structural`]
/// because they take a branch apart, and a rewriter that dissolves every
/// branch it can is a strategy, which this module does not decide.
///
/// [`Law::SelectHoist`] and [`Law::CondHoist`] are branch laws and are
/// **not** here, for the reason the unpackings are not in [`folding`]: they
/// grow a graph. A driver run to fixpoint over the first would push every
/// branch past everything downstream of it, duplicating the lot, and over
/// the second would split every branch a condition holds — which is
/// sometimes exactly what a proof wants and never what a cleanup pass does.
/// A strategy names them, and `tree` is the strategy that names both.
pub fn branching() -> Vec<Law> {
    vec![
        Law::SelectLiteral,
        Law::SelectSame,
        // The one row here that reads the condition's *maker* rather than
        // its blocks, and the one that shrinks without deciding anything:
        // a negation in front of a branch is the branch with its arms
        // exchanged, and the negation is gone.
        Law::NotBranch,
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
        // and `retuple` alone would take a round trip that began at a
        // coercion apart in two steps — a second coercion, then `idem` —
        // where the whole window is one.
        Law::AsTupleRoundTrip,
        Law::Retuple,
        Law::IsTupleBuilt,
        Law::NotNot,
        Law::AndLiteral,
        Law::OrLiteral,
        // Two of the pair collapse to one. `comm` is its sibling in the
        // instruction-set facts and is **not** here: it permutes instead of
        // shrinking, so a driver would swap the same two operands forever.
        Law::Idem,
        Law::TupleCancel,
        Law::AsTupleBuilt,
        Law::EqualRefl,
    ]
}

// ---- where a step lands ----------------------------------------------------------

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
    /// A side of the rule, or a graph the payload carries, is not a graph. A
    /// rule that cannot be built cannot be applied.
    Broken(crate::kernel::graph::Error),
}

/// The two ways a [`Pair`] refuses to be one, said as a payload's fault —
/// which is what they are, since a rule builds both sides itself.
impl From<Unpaired> for Ill {
    fn from(why: Unpaired) -> Ill {
        match why {
            Unpaired::Interface(l, r) => Ill::Interface(l, r),
            Unpaired::Broken(e) => Ill::Broken(e),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The payload does not state an equation.
    Ill { law: Law, why: Ill },
    /// [`transplant`] was handed a match that does not put its pattern in
    /// its host, so there was nothing to carry a derivation through.
    NotEmbedded(Mismatch),
    /// The subgraph the match points at is not the side of the equation the
    /// step says it is. This is the only way a step can be wrong.
    NotThere {
        law: Law,
        dir: Direction,
        at: Mismatch,
    },
    /// A carried step selects a reader the embedding cannot say in the
    /// host: the inner graph's own boundary output. Who reads the inner
    /// boundary is the host's business, so such a step does not travel.
    NotCarried,
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
            Error::NotEmbedded(why) => {
                write!(f, "the derivation's graph does not sit there: {}", why)
            }
            Error::NotThere { law, dir, at } => {
                let side = match dir {
                    Direction::Forward => "left",
                    Direction::Backward => "right",
                };
                write!(f, "{:?}'s {} side is not there: {}", law, side, at)
            }
            Error::NotCarried => {
                write!(
                    f,
                    "a step selects the derivation's own boundary, which does not travel"
                )
            }
        }
    }
}

impl std::error::Error for Error {}

// ---- the table, as construction --------------------------------------------------

/// The two graphs a rule says are the same program, built from its payload
/// alone.
///
/// This is the table, and after it the rest is [`crate::kernel::graph`]'s: what
/// comes back is a [`Pair`], which knows nothing of laws and everything
/// about being splice-able, and every rewrite in this module is that pair
/// applied somewhere.
///
/// It reads no graph it was not handed, tests nothing, and decides nothing:
/// a payload that states no equation comes back as [`Error::Ill`] rather
/// than as a silently wrong pair.
pub fn sides(rule: &Rule) -> Result<Pair, Error> {
    let law = rule.law();
    let ill = |why| Error::Ill { law, why };
    let (a, b) = match rule {
        // The window is the call box alone, every port exported; the
        // other side is the body as handed in. The call's arity is the
        // body's, which is what makes the two sides one interface — a
        // body of the wrong arity is refused as a pair, and a body of the
        // wrong *program* is `certify`'s to refuse.
        Rule::Open { target, body } => (
            Graph::of_box(NodeKind::Call {
                target: *target,
                arity: body.arity(),
            }),
            body.clone(),
        ),
        Rule::NotNot => {
            let mut long = Graph::empty(1);
            let first = long.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
            // The middle port is not exported: the equation is about the
            // composite's answer, and a first `not` something else reads
            // goes on standing for that reader.
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
            long.close(and);

            // The answer is `truthy`'s verdict on the literal, measured on
            // the value itself: truthy leaves the other operand's
            // coercion, the one falsy value leaves `false` and the other
            // operand unread.
            let mut short = Graph::empty(1);
            let answer = if value.truthy() {
                short.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)])
            } else {
                short.add(NodeKind::Op(Prim::Push(Value::Bool(false))), Vec::new())
            };
            short.close(answer);

            (long, short)
        }
        Rule::OrLiteral { literal, value } => {
            let mut long = Graph::empty(1);
            let lit = long.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new());
            let operands = match literal {
                Side::Deep => vec![lit[0], Source::Input(0)],
                Side::Top => vec![Source::Input(0), lit[0]],
            };
            let or = long.add(NodeKind::Op(Prim::Or), operands);
            long.close(or);

            // The poles of the sibling row, swapped: the one falsy value
            // leaves the other operand's coercion, and a truthy literal
            // leaves `true` and the other operand unread.
            let mut short = Graph::empty(1);
            let answer = if value.truthy() {
                short.add(NodeKind::Op(Prim::Push(Value::Bool(true))), Vec::new())
            } else {
                short.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)])
            };
            short.close(answer);

            (long, short)
        }
        Rule::TupleCancel { n } => {
            let n = *n;
            let elements: Vec<Source> = (0..n).map(Source::Input).collect();

            let mut long = Graph::empty(n);
            let tuple = long.add(NodeKind::Op(Prim::Tuple(n)), elements.clone());
            let apart = long.add(NodeKind::Op(Prim::Untuple(n)), tuple);
            long.close(apart);

            // `id(n)`, literally: the elements themselves. The tuple is
            // not part of the equation — a tuple something else reads
            // stays standing in the host, since a substitution deletes
            // nothing.
            let mut short = Graph::empty(n);
            short.close(elements);

            (long, short)
        }
        Rule::AsTupleBuilt { n } => {
            let n = *n;
            let elements: Vec<Source> = (0..n).map(Source::Input).collect();

            let mut long = Graph::empty(n);
            let tuple = long.add(NodeKind::Op(Prim::Tuple(n)), elements.clone());
            let coerced = long.add(NodeKind::Op(Prim::AsTuple(n)), tuple);
            long.close(coerced);

            let mut short = Graph::empty(n);
            let tuple = short.add(NodeKind::Op(Prim::Tuple(n)), elements);
            short.close(tuple);

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
        Rule::SelectSame => {
            // Two boundary inputs, not three: the block both sides answer
            // with is **one** input, read twice, and it has to be one in the
            // pattern itself. A match that merely pointed two of the
            // pattern's inputs at one host source would be matching a graph
            // that does not state the equation.
            let mut both = Graph::empty(2);
            let answer = both.add(
                NodeKind::Select,
                vec![Source::Input(0), Source::Input(1), Source::Input(1)],
            );
            both.close(answer);

            // A branch answering one thing either way is not a branch, and
            // the answer side holds no box at all: the block itself is what
            // the equation comes to. The condition loses its one reader with
            // the select, and a box the boundary no longer reaches is not
            // part of the program.
            let mut alone = Graph::empty(2);
            alone.close(vec![Source::Input(1)]);

            (both, alone)
        }

        Rule::SelectLiteral { value, lit_blocks } => {
            let mut named = lit_blocks.clone();
            named.sort_unstable();
            named.dedup();
            if named.len() != lit_blocks.len() || named.iter().any(|&b| b >= 2) {
                return Err(ill(Ill::Refused));
            }
            let width = 2 - lit_blocks.len();
            let outside: Vec<usize> = (0..2).filter(|b| !named.contains(b)).collect();
            let placed = |b: usize| {
                let idx = outside.iter().position(|&o| o == b).expect("one or other");
                Source::Input(idx)
            };

            let mut both = Graph::empty(width);
            let lit = both.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new())[0];
            let blocks: Vec<Source> = (0..2)
                .map(|b| if named.contains(&b) { lit } else { placed(b) })
                .collect();
            let answer = both.add(NodeKind::Select, vec![lit, blocks[0], blocks[1]]);
            both.close(answer);

            // The literal survives on the answer side only where the chosen
            // block reads it; interning makes asking for it twice asking for
            // the one box.
            let b = if value.truthy() { 0 } else { 1 };
            let mut chosen = Graph::empty(width);
            let out = if named.contains(&b) {
                chosen.add(NodeKind::Op(Prim::Push(value.clone())), Vec::new())[0]
            } else {
                placed(b)
            };
            chosen.close(vec![out]);

            (both, chosen)
        }

        Rule::NotBranch => {
            // The condition and the two blocks. Both sides read the same
            // pair and differ only in which the select is handed first.
            let mut negated = Graph::empty(3);
            // The `not` is inside the window, not exported: the equation
            // replaces the select's answer, and a negation something else
            // reads goes on standing for that reader.
            let flipped = negated.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
            let answer = negated.add(
                NodeKind::Select,
                vec![flipped[0], Source::Input(1), Source::Input(2)],
            );
            negated.close(answer);

            let mut direct = Graph::empty(3);
            let answer = direct.add(
                NodeKind::Select,
                vec![Source::Input(0), Source::Input(2), Source::Input(1)],
            );
            direct.close(answer);

            (negated, direct)
        }

        Rule::SpecializeEqual { answered } => {
            // Two boundary inputs, and they are the operands of the test:
            // input 0 the one the else block is, input 1 the one the then
            // block is. Each is said **once** in the pattern, for the reason
            // `select-same` says its shared block once — that a block is the
            // very wire the test read is what the row is about, and a match
            // merely pointing two inputs at one host wire would be matching
            // a graph that does not state it.
            let answer = Source::Input(0);
            let other = Source::Input(1);
            // Which way round the test reads them is the payload's, and
            // nothing else about the operands is: `equal` is commutative,
            // but *which operand is which* is what the graph records.
            let operands = match answered {
                Side::Deep => vec![answer, other],
                Side::Top => vec![other, answer],
            };

            let mut tested = Graph::empty(2);
            let test = tested.add(NodeKind::Op(Prim::Equal), operands);
            let answers = tested.add(NodeKind::Select, vec![test[0], other, answer]);
            tested.close(answers);

            // A branch that answers nothing is not a branch, and neither is
            // a test nothing turns on: the answer side is the operand itself
            // and holds no box at all. The `equal` in a host goes on
            // standing for whatever else reads it.
            let mut decided = Graph::empty(2);
            decided.close(vec![answer]);

            (tested, decided)
        }

        Rule::SpecializeBool { then } => {
            // The block is the then one exactly when that is what the branch
            // decided about the condition.
            let decided = Value::Bool(*then);
            // The block is the coercion's own answer — the condition itself
            // — said once in the pattern rather than tested. That it is a
            // *coerced* answer is the whole of the side condition: a truthy
            // bool is `true`, where a truthy `5` is `5`.
            let build = |folded: bool| {
                let mut g = Graph::empty(2);
                let coerced = g.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)])[0];
                let known = if folded {
                    g.add(NodeKind::Op(Prim::Push(decided.clone())), Vec::new())[0]
                } else {
                    coerced
                };
                let other = Source::Input(1);
                let (t, e) = if *then {
                    (known, other)
                } else {
                    (other, known)
                };
                let answer = g.add(NodeKind::Select, vec![coerced, t, e]);
                g.close(answer);
                g
            };
            (build(false), build(true))
        }

        Rule::SpecializeChoice { side } => {
            // Boundary input 0 is the condition, and **both** selects read
            // it: that is the side condition, said in the pattern rather
            // than tested. Then the inner select's two blocks, then the
            // outer block this row does not touch.
            let cond = Source::Input(0);
            let (inner_then, inner_else) = (Source::Input(1), Source::Input(2));
            let outer_other = Source::Input(3);

            let build = |folded: bool| {
                let mut g = Graph::empty(4);
                // The inner select: unfolded, the outer block reads its
                // answer; folded, it reads the block that answer is, and the
                // equation's answer side never mentions it. In a host it
                // goes on standing for whatever else reads it — its own
                // other side's block, usually.
                let moved = if folded {
                    if *side { inner_then } else { inner_else }
                } else {
                    g.add(NodeKind::Select, vec![cond, inner_then, inner_else])[0]
                };
                let (t, e) = if *side {
                    (moved, outer_other)
                } else {
                    (outer_other, moved)
                };
                let answer = g.add(NodeKind::Select, vec![cond, t, e]);
                g.close(answer);
                g
            };
            (build(false), build(true))
        }

        Rule::SelectHoist { body } => {
            if body.arity().inputs == 0 || body.arity().outputs == 0 {
                return Err(ill(Ill::Refused));
            }
            body.check().map_err(|e| ill(Ill::Broken(e)))?;
            let k = body.arity().inputs - 1;
            let m = body.arity().outputs;
            // The condition, the two blocks of the answer, and whatever the
            // region reads that is not the answer.
            let width = 3 + k;
            let outside: Vec<Source> = (0..k).map(|i| Source::Input(3 + i)).collect();
            let feeds = |block: Source| {
                let mut takes = vec![block];
                takes.extend(outside.iter().copied());
                takes
            };

            let mut chosen = Graph::empty(width);
            let answer = chosen.add(
                NodeKind::Select,
                vec![Source::Input(0), Source::Input(1), Source::Input(2)],
            );
            let out = chosen.implant(body, &feeds(answer[0]));
            chosen.close(out);

            // Both copies run and one is kept, per answer the region leaves.
            let mut hoisted = Graph::empty(width);
            let sure = hoisted.implant(body, &feeds(Source::Input(1)));
            let doubted = hoisted.implant(body, &feeds(Source::Input(2)));
            let out: Vec<Source> = (0..m)
                .map(|j| {
                    hoisted.add(
                        NodeKind::Select,
                        vec![Source::Input(0), sure[j], doubted[j]],
                    )[0]
                })
                .collect();
            hoisted.close(out);

            (chosen, hoisted)
        }

        Rule::CondHoist => {
            // Boundary input 0 is the condition the *inner* branch turns on,
            // then that branch's two blocks, then the two blocks of the
            // branch that moves.
            let (c, t1, e1) = (Source::Input(0), Source::Input(1), Source::Input(2));
            let (t2, e2) = (Source::Input(3), Source::Input(4));

            let mut nested = Graph::empty(5);
            let condition = nested.add(NodeKind::Select, vec![c, t1, e1]);
            let answer = nested.add(NodeKind::Select, vec![condition[0], t2, e2]);
            nested.close(answer);

            // Both copies run and the outermost select keeps one, which is
            // the licence every branch spends. Each turns on a block of the
            // inner branch straight, since the block on the side `C` picks
            // is the very answer the inner select was going to hand over.
            let mut split = Graph::empty(5);
            let sure = split.add(NodeKind::Select, vec![t1, t2, e2]);
            let doubted = split.add(NodeKind::Select, vec![e1, t2, e2]);
            let answer = split.add(NodeKind::Select, vec![c, sure[0], doubted[0]]);
            split.close(answer);

            (nested, split)
        }

        // ---- the value layer ----
        Rule::Fold {
            prim,
            operands,
            reads,
        } => {
            let arity = prim.arity();
            // A window is its operands and nothing else, so the payload
            // has to be exactly them: one operand per input, every one of
            // them read, and none named that is not there. `tuple 0` takes
            // nothing and is a window all the same — an operation that
            // reads no operand has every operand it reads a literal — and
            // the empty payload is the only one it can carry.
            if matches!(prim, Prim::Push(_) | Prim::Swap)
                || reads.len() != arity.inputs
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
            long.close(out);

            let mut short = Graph::empty(0);
            let answers: Vec<Source> = answers
                .into_iter()
                .map(|v| short.add(NodeKind::Op(Prim::Push(v)), Vec::new())[0])
                .collect();
            short.close(answers);

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
        Rule::TestedBool { kind, test } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            let arity = prim.arity();
            // The promise, and the test the promise answers. Nothing else
            // decides the verdict: what the operation *is* never enters,
            // only that the set says what type it leaves.
            let Some(verdict) = asked_of_a_bool(test) else {
                return Err(ill(Ill::Refused));
            };
            if arity.outputs != 1 || !prim.to_instruction().yields_bool() {
                return Err(ill(Ill::Refused));
            }
            let ins: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();

            let mut tested = Graph::empty(arity.inputs);
            let answer = tested.add(kind.clone(), ins);
            let truth = tested.add(NodeKind::Op(test.clone()), answer);
            tested.close(truth);

            // The verdict alone: the equation replaces the test's answer,
            // and the operation goes on standing in the host for whoever
            // else reads it.
            let mut known = Graph::empty(arity.inputs);
            let truth = known.add(NodeKind::Op(Prim::Push(Value::Bool(verdict))), Vec::new());
            known.close(truth);

            (tested, known)
        }
        Rule::Retuple { n } => {
            let n = *n;
            if n == 0 {
                return Err(ill(Ill::Refused));
            }
            let mut roundabout = Graph::empty(1);
            let parts = roundabout.add(NodeKind::Op(Prim::Untuple(n)), vec![Source::Input(0)]);
            // The whole round trip, said by the edges: every slot of the
            // rebuild reads the matching part, or the pattern is not there.
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
            // The pattern holds the whole round trip — the wholeness is
            // said by its edges, not by anything about readers.
            let parts = roundabout.add(NodeKind::Op(Prim::Untuple(n)), coerced);
            let rebuilt = roundabout.add(NodeKind::Op(Prim::Tuple(n)), parts);
            roundabout.close(rebuilt);

            let mut once = Graph::empty(1);
            let coerced = once.add(NodeKind::Op(Prim::AsTuple(n)), vec![Source::Input(0)]);
            once.close(coerced);

            (roundabout, once)
        }
        Rule::IsTupleBuilt { built, asked } => {
            let (built, asked) = (*built, *asked);
            let elements: Vec<Source> = (0..built).map(Source::Input).collect();

            let mut question = Graph::empty(built);
            let tuple = question.add(NodeKind::Op(Prim::Tuple(built)), elements);
            let answer = question.add(NodeKind::Op(Prim::IsTuple(Some(asked))), tuple);
            question.close(answer);

            // The verdict alone: the equation replaces the test's answer,
            // and the tuple goes on standing in the host for whoever else
            // reads it.
            let mut settled = Graph::empty(built);
            let answer = settled.add(
                NodeKind::Op(Prim::Push(Value::Bool(built == asked))),
                Vec::new(),
            );
            settled.close(answer);

            (question, settled)
        }
        Rule::Idem { kind } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            let arity = prim.arity();
            if arity.inputs != 1 || arity.outputs != 1 || !prim.to_instruction().idempotent() {
                return Err(ill(Ill::Refused));
            }

            let mut twice = Graph::empty(1);
            let first = twice.add(kind.clone(), vec![Source::Input(0)]);
            // The middle port is not exported, for `not-not`'s reason: the
            // equation is about the composite's answer.
            let second = twice.add(kind.clone(), first);
            twice.close(second);

            let mut once = Graph::empty(1);
            let only = once.add(kind.clone(), vec![Source::Input(0)]);
            once.close(only);

            (twice, once)
        }
        Rule::Commute { kind } => {
            let NodeKind::Op(prim) = kind else {
                return Err(ill(Ill::Refused));
            };
            let arity = prim.arity();
            if arity.inputs != 2 || !prim.to_instruction().commutative() {
                return Err(ill(Ill::Refused));
            }
            // No `swap` appears on either side, and none could: a crossing
            // is two names in the other order, and this is the two orders.
            let mut asked = Graph::empty(2);
            let answer = asked.add(kind.clone(), vec![Source::Input(0), Source::Input(1)]);
            asked.close(answer);

            let mut crossed = Graph::empty(2);
            let answer = crossed.add(kind.clone(), vec![Source::Input(1), Source::Input(0)]);
            crossed.close(answer);

            (asked, crossed)
        }
        Rule::AsBoolBranch => {
            let mut forced = Graph::empty(1);
            let out = forced.add(NodeKind::Op(Prim::AsBool), vec![Source::Input(0)]);
            forced.close(out);

            // Neither arm reads anything, so the branch is the select
            // alone: the two blocks are the two answers `truthy` can give,
            // and the value itself is spent as the condition.
            let mut asked = Graph::empty(1);
            let yes = asked.add(NodeKind::Op(Prim::Push(Value::Bool(true))), Vec::new());
            let no = asked.add(NodeKind::Op(Prim::Push(Value::Bool(false))), Vec::new());
            let kept = asked.add(NodeKind::Select, vec![Source::Input(0), yes[0], no[0]]);
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
            // the else block the default. Neither arm computes anything.
            let junk = guarded.add(NodeKind::Op(Prim::Push(junk)), Vec::new());
            let kept = guarded.add(NodeKind::Select, vec![holds, Source::Input(0), junk[0]]);
            guarded.close(kept);

            (forced, guarded)
        }
    };
    Pair::new(a, b).map_err(|why| ill(why.into()))
}

/// What a type test answers of a value the instruction set promises is a
/// `Bool`, or `None` for a prim that asks no question about a type.
///
/// The one thing [`Rule::TestedBool`] reads off its `test`, and it is a
/// reading rather than a computation: a promised bool *is* a `Bool`, so
/// `is_bool` holds of it and every other test of a type does not. The
/// widths `is_tuple` may carry make no difference — a `Bool` is a tuple of
/// no width at all.
fn asked_of_a_bool(test: &Prim) -> Option<bool> {
    match test {
        Prim::IsBool => Some(true),
        Prim::IsInt | Prim::IsConstString | Prim::IsSymbol | Prim::IsTuple(_) => Some(false),
        _ => None,
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

// ---- applying a step -------------------------------------------------------------

/// One rewrite, and the step that undoes it.
///
/// A step is a law's name, a direction and a place; this is where those
/// three become a rewrite. [`sides`] turns the payload into a [`Pair`] and
/// [`Pair::apply`] does the rest — checking the match, deleting what it
/// points at, putting the other side down — so the whole of what this adds
/// is the law's name, on the way in to say which pair and on the way out to
/// say what was spent.
///
/// The answer is the **inverse step**, which [`Pair::apply`] hands back as
/// the embedding of what it just put down.
pub fn apply(graph: &mut Graph, step: &Step) -> Result<Step, Error> {
    let pair = sides(&step.rule)?;
    let back = pair
        .apply(graph, step.dir, &step.at)
        .map_err(|at| Error::NotThere {
            law: step.rule.law(),
            dir: step.dir,
            at,
        })?;
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
                at: back.at.rebase(&moved),
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

/// A derivation proved about one graph, spent again inside another.
///
/// `at` says where `pattern` sits in `host` — [`find`](crate::kernel::graph::find)
/// answers with one, or a caller may state it — and `steps` is a run that
/// was written about `pattern` alone. What comes back is **the same run said
/// in the host's coordinates**, so [`replay`] will take it against a fresh
/// copy of `host` and land in the same place.
///
/// This is what makes a proof worth having twice. A [`Match`] names host
/// [`NodeId`]s, so a derivation belongs to the graph it was written for;
/// carrying one through an [`Embedding`] is what lets a lemma proved once be
/// spent wherever its left-hand side turns up.
///
/// Every step is run **twice**: on a copy of `pattern`, to follow where its
/// boxes went, and on `host`, to do the work. The first is what keeps the
/// embedding current — each rewrite makes boxes on both sides, and
/// [`Embedding::extend`] is what pairs them up so the next step can name
/// them. It is also where a step that is not about `pattern` is refused,
/// with the law able to say why.
///
/// Nothing is believed. The outer match goes through
/// [`check_match`] before anything moves, and
/// every carried step through [`apply`] like any other, so a wrongly carried
/// one costs a refusal. `host` is left exactly as it was if any step fails:
/// the work is done on a copy and committed only once the whole run lands.
///
/// `pattern` must be a graph nothing has been deleted from, which is what
/// any [`Match`] is against.
pub fn transplant(
    host: &mut Graph,
    pattern: &Graph,
    at: &Match,
    steps: &[Step],
) -> Result<Derivation, Error> {
    check_match(host, pattern, at).map_err(Error::NotEmbedded)?;
    let mut here = pattern.clone();
    let mut carried = Embedding::of(at);
    let mut work = host.clone();
    let mut run = Derivation::default();
    for step in steps {
        // On the pattern first, so a step that is not about this graph is
        // refused where the law can say so, rather than carried into
        // something the host refuses for a stranger reason.
        let left = apply(&mut here, step)?.at;
        // The one thing an embedding cannot say is a selection on the
        // inner graph's own boundary; every box a step can name, it holds.
        let there = carried.carry(&step.at).ok_or(Error::NotCarried)?;
        run.push(
            &mut work,
            Step {
                rule: step.rule.clone(),
                dir: step.dir,
                at: there,
            },
        )?;
        let landed = run
            .latest_undo()
            .expect("a step was just pushed")
            .at
            .clone();
        carried.extend(&left, &landed);
    }
    *host = work;
    Ok(run)
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
            let Ok(pair) = sides(&rule) else { continue };
            out.extend(find_at(graph, pair.lhs(), seed).into_iter().map(|at| Step {
                rule: rule.clone(),
                dir: Direction::Forward,
                at,
            }));
        }
    }
    out
}

/// The case split, spent where a proof says to: a wire the instruction
/// set promises is a bool becomes a branch over both its cases, with
/// everything downstream of it copied once per case and the case pasted
/// in as a literal.
///
/// ```text
/// body(w)  =  if w { body(true) } else { body(false) }
/// ```
///
/// **Not a row.** It is three of them, spent in order at the boxes each
/// is read off — the promise written down, the coercion unpacked into the
/// branch it is, and the branch grown forward over the region:
///
/// ```text
/// body(w)                               promised-bool
///   = body(as_bool w)                   as-bool-branch
///   = body(select(w, true, false))      select-hoist
///   = select(w, body(true), body(false))
/// ```
///
/// Every step goes through [`Derivation::push`] like any other rewrite,
/// so what this adds to a proof is *where*, and nothing else: three
/// ordinary steps a checker replays blind. See the module docs for what
/// each one contributes, and for the one reading the split leaves
/// differently than the row it replaced.
///
/// The first step is spent only where the promise is not written down
/// for every reader of the answer already — `promised-bool` says so by
/// declining — and the coercion the middle step unpacks is then the one
/// that is standing: `at` itself when it is an `as_bool`, or the
/// `as_bool` reading its answer. So a program that wrote the coercion
/// down itself is split in two steps rather than three, and over that
/// coercion's region.
///
/// Answers the wire the fresh branch turns on, which is what an arm is
/// scoped by. `None`, with the graph untouched, when there is nothing to
/// split: the instruction set promises nothing about `at`'s answer, or
/// nothing but the boundary reads the wire the branch would stand on, and
/// a split whose body is empty decides nothing.
pub fn case_split(
    graph: &mut Graph,
    run: &mut Derivation,
    at: NodeId,
) -> Result<Option<Source>, Error> {
    // What the latest step left behind, of the kind wanted: how a caller
    // reads a rewrite's image without reaching into the splice.
    let made = |run: &Derivation, graph: &Graph, which: fn(&NodeKind) -> bool| {
        run.latest_undo().and_then(|back| {
            back.at
                .nodes
                .iter()
                .rev()
                .copied()
                .find(|&n| which(graph.kind(n)))
        })
    };
    let as_bool = |kind: &NodeKind| matches!(kind, NodeKind::Op(Prim::AsBool));
    let answer = Source::Port { node: at, port: 0 };

    // A coercion already standing on the answer — the box asked about
    // when that is what it is, or an `as_bool` reading it.
    let standing = match as_bool(graph.kind(at)) {
        true => Some(at),
        false => graph.sinks(answer).into_iter().find_map(|sink| match sink {
            Sink::Port { node, .. } if as_bool(graph.kind(node)) => Some(node),
            _ => None,
        }),
    };
    // And the step that writes one down, offered unless every reader of
    // the answer has one already. Where it fires the coercion it leaves
    // reads what those readers read, so the branch comes to stand on the
    // answer itself; where it does not, the branch stands where the
    // coercion that was already there stood.
    let promise = propose(graph, &[Law::PromisedBool], at).into_iter().next();
    let stands_on = match (&promise, standing) {
        (Some(_), _) => answer,
        (None, Some(node)) => Source::Port { node, port: 0 },
        // Nothing promises this answer is a bool, so there is no second
        // case and nothing to pin.
        (None, None) => return Ok(None),
    };
    // Asked before anything moves, because the last of the three steps is
    // the one that would refuse an empty body — and a split that fails
    // half way is a graph with a coercion written into it and no branch.
    if downstream_of(graph, &[stands_on]).is_none() {
        return Ok(None);
    }

    let coercion = match promise {
        Some(step) => {
            run.push(graph, step)?;
            made(run, graph, as_bool).expect("`promised-bool` leaves the coercion it wrote down")
        }
        None => standing.expect("a decline with nothing standing answered above"),
    };

    let unpack = propose(graph, &[Law::AsBoolBranch], coercion)
        .into_iter()
        .next()
        .expect("`as-bool-branch` is read off every coercion");
    run.push(graph, unpack)?;
    let branch = made(run, graph, |kind| matches!(kind, NodeKind::Select))
        .expect("`as-bool-branch` leaves the branch it made");
    // The wire the coercion read, which is the wire every select the hoist
    // leaves turns on as well: the branch moves, its condition does not.
    let condition = graph.sources(branch)[0];

    let hoist = propose(graph, &[Law::SelectHoist], branch)
        .into_iter()
        .next()
        .expect("the region that read the answer reads the branch");
    run.push(graph, hoist)?;
    Ok(Some(condition))
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

/// The instance of `law` one side of which is **bare wires** — no boxes,
/// `wires` boundary inputs handed straight through — with the direction
/// that reads the equation from that side, so the wires are the pattern
/// and the law's window is what goes in.
///
/// This is the payload of an **introduction**. A side with no boxes
/// anchors nowhere ([`pins_itself`](crate::kernel::graph::pins_itself) says why),
/// so no search ever proposes these steps: they are *stated*, the wires
/// named outright, and this is where a statement's width becomes a
/// payload. Two rows are here. `tuple-cancel`'s right side is `id(n)`, so
/// the pair is introduced backward, on any `n` wires. `specialize-equal`
/// answers with one of the operands it compared and holds no
/// box on that side either, so it is introduced backward on **two**
/// wires: the one the branch comes to answer with, and the one it is
/// tested against. `None` for a law both of whose sides hold boxes, for a
/// width whose statement would need a payload the wires do not say, and
/// for one whose bare side would take more payload than a width: nothing
/// here is guessed.
pub fn boxless(law: Law, wires: usize) -> Option<(Rule, Direction)> {
    match (law, wires) {
        (Law::TupleCancel, n) => Some((Rule::TupleCancel { n }, Direction::Backward)),
        // `select(equal(x, y), y, x) = x`: the answer side is
        // the wire `x` and no box at all, so this is the other row a
        // proof can only state. Two wires — the one the branch answers
        // with, then the one it is tested against — and the order is the
        // window's shape, `equal(x, y)` in the order they are named, the
        // way `on(in1 in0, tuple-cancel)` builds the other tuple. `comm`
        // is the row that reads the test the other way round afterwards.
        (Law::SpecializeEqual, 2) => Some((
            Rule::SpecializeEqual {
                answered: Side::Deep,
            },
            Direction::Backward,
        )),
        _ => None,
    }
}

/// Everything downstream of one box's `answers`, lifted out as a graph of
/// its own — the body [`Rule::SelectHoist`] carries.
///
/// The region is the transitive readers of the answers, which makes it
/// downstream-closed: a region box's readers are region boxes or the
/// boundary, so the lifted graph's outputs are exactly what the host
/// boundary read of it, in the host's order. Inputs `0..answers.len()`
/// stand for the answers; the rest is whatever else the region reads, in
/// encounter order. `None` when nothing but the boundary reads them — an
/// expansion with an empty body decides nothing.
///
/// An answer the host boundary reads **directly** comes back as one of
/// the body's own outputs, passed straight through from the input that
/// stands for it — the reading moves to the new select, and the old
/// branch drops out of the program when nothing else holds it. Then the
/// copy on each side leaves that side's block, and the new select chooses
/// between exactly the blocks the old one chose between.
fn downstream_of(graph: &Graph, answers: &[Source]) -> Option<Graph> {
    let mut region: Vec<NodeId> = Vec::new();
    let mut todo: Vec<Source> = answers.to_vec();
    while let Some(src) = todo.pop() {
        for sink in graph.sinks(src) {
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
    let mine: HashSet<NodeId> = region.iter().copied().collect();
    let held = |src: &Source| matches!(src, Source::Port { node, .. } if mine.contains(node));
    // The region is downstream-closed, so what the host boundary reads of
    // it is the whole of what anything outside reads of it.
    let leaves: Vec<Source> = graph
        .outputs()
        .iter()
        .filter(|src| held(src) || answers.contains(src))
        .copied()
        .collect();
    lift(graph, &region, answers, &leaves).map(|lifted| lifted.graph)
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

        // `or` with a literal operand, read exactly as its sibling is: one
        // rule per operand a pushed value feeds, seeded at that literal.
        (Law::OrLiteral, NodeKind::Op(Prim::Or)) => {
            let mut out = Vec::new();
            for (side, port) in [(Side::Deep, 0), (Side::Top, 1)] {
                if let Some((lit, NodeKind::Op(Prim::Push(value)))) = made_by(takes[port]) {
                    out.push((
                        Rule::OrLiteral {
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
        (Law::SelectSame, NodeKind::Select) => {
            if takes[1] == takes[2] {
                one(Rule::SelectSame)
            } else {
                Vec::new()
            }
        }

        // A condition that is already a value: the select is the block it
        // chooses.
        (Law::SelectLiteral, NodeKind::Select) => {
            let Some((lit, NodeKind::Op(Prim::Push(value)))) = made_by(takes[0]) else {
                return Vec::new();
            };
            let lit_blocks: Vec<usize> = (0..2).filter(|&b| takes[1 + b] == takes[0]).collect();
            vec![(
                Rule::SelectLiteral {
                    value: value.clone(),
                    lit_blocks,
                },
                lit,
            )]
        }

        // A condition made by a `not`: the branch is the same branch with
        // its blocks exchanged, and the negation is spent. Seeded at the
        // `not`, which is the pattern's first box.
        (Law::NotBranch, NodeKind::Select) => match made_by(takes[0]) {
            Some((flipped, NodeKind::Op(Prim::Not))) => vec![(Rule::NotBranch, flipped)],
            _ => Vec::new(),
        },

        // A branch turning on an `equal` and answering with the test's own
        // operands — the other one where it held, this one where it did
        // not. Seeded at the `equal`, which is the pattern's first box.
        (Law::SpecializeEqual, NodeKind::Select) => {
            let Some((test, NodeKind::Op(Prim::Equal))) = made_by(takes[0]) else {
                return Vec::new();
            };
            let operands = graph.sources(test);
            let (deep, top) = (operands[0], operands[1]);
            // A test of one wire against itself is `equal-refl`'s, and the
            // branch it decides is `select-same`'s: there is no operand here
            // for the other to be, and the pattern says two.
            if deep == top {
                return Vec::new();
            }
            let (chose, spurned) = (takes[1], takes[2]);
            // `answered` is the operand the else block is, and the then
            // block has to be the other one: the two are the same value
            // exactly where the then block is reached.
            let answered = match (spurned == deep, spurned == top) {
                (true, _) if chose == top => Side::Deep,
                (_, true) if chose == deep => Side::Top,
                _ => return Vec::new(),
            };
            vec![(Rule::SpecializeEqual { answered }, test)]
        }

        // A block that answers with the very value the condition was made
        // of, that condition being manifestly a bool — which is the only way
        // a block gets to say what the branch decided.
        (Law::SpecializeBool, NodeKind::Select) => {
            let cond = takes[0];
            // The `as_bool` that made the condition is the pattern's first
            // box, so it is what the search is anchored at.
            let Some((coercion, NodeKind::Op(Prim::AsBool))) = made_by(cond) else {
                return Vec::new();
            };
            (0..2)
                .filter(|&b| takes[1 + b] == cond)
                .map(|b| (Rule::SpecializeBool { then: b == 0 }, coercion))
                .collect()
        }

        // A branch inside an arm, retesting the value the outer branch
        // tested — read off the outer select, one rule per block of it an
        // inner select on the same condition answers.
        (Law::SpecializeChoice, NodeKind::Select) => (0..2)
            .filter_map(|b| {
                let Source::Port { node: within, .. } = takes[1 + b] else {
                    return None;
                };
                (matches!(graph.kind(within), NodeKind::Select)
                    && graph.sources(within)[0] == takes[0])
                    .then_some((Rule::SpecializeChoice { side: b == 0 }, within))
            })
            .collect(),

        // The instruction set's promise, written down as a box. Proposed
        // only where it is not written down **for every reader**: the
        // equation holds however many `as_bool`s are stacked on the
        // answer, so nothing but this guard stops a driver stacking them
        // forever. Search is where that argument belongs — the law states
        // an equality and no more.
        //
        // Every reader rather than any, because the rewrite redirects
        // every reader: an answer read by an `as_bool` and by something
        // else is an answer whose promise one reader has and the other
        // has not, and firing gives it to both. It terminates on the same
        // argument either way — what the step leaves is an answer whose
        // one reader is the coercion it just wrote down, and this guard
        // declines the next one.
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
                .all(|sink| match sink {
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

        // Everything downstream of a branch's answers, lifted out as the
        // body the branch grows forward over. Read off the `select`, which
        // is also where the pattern begins.
        (Law::SelectHoist, NodeKind::Select) => {
            let answers = [Source::Port { node: id, port: 0 }];
            match downstream_of(graph, &answers) {
                Some(body) => vec![(Rule::SelectHoist { body }, id)],
                None => Vec::new(),
            }
        }

        // A branch whose condition is what another branch answered: the
        // outer one runs under the inner, once per block the inner chooses
        // between. Read off the outer select and anchored at the inner,
        // which is the pattern's first box.
        (Law::CondHoist, NodeKind::Select) => {
            let Source::Port { node, .. } = takes[0] else {
                return Vec::new();
            };
            match graph.kind(node) {
                NodeKind::Select => vec![(Rule::CondHoist, node)],
                _ => Vec::new(),
            }
        }

        // An operation whose every operand is a literal — the fold, and
        // the machine is what answers it. An operation that reads no
        // operand is one of those vacuously: `tuple 0` is a window with
        // nothing in it, anchored at itself because there is no literal
        // behind it to anchor at.
        (Law::Fold, NodeKind::Op(prim)) => {
            if matches!(prim, Prim::Push(_) | Prim::Swap) {
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
            let seed = held.first().map_or(id, |&(node, _)| node);
            vec![(
                Rule::Fold {
                    prim: prim.clone(),
                    operands: held.into_iter().map(|(_, v)| v).collect(),
                    reads,
                },
                seed,
            )]
        }

        // A type test — any of them — of an answer the instruction set
        // promises is a bool. Which test it is decides the answer and not
        // whether there is one, so nothing here compares the two: the
        // promise is the whole side condition.
        (Law::TestedBool, NodeKind::Op(test)) if asked_of_a_bool(test).is_some() => {
            let Some((answered, NodeKind::Op(prim))) = made_by(takes[0]) else {
                return Vec::new();
            };
            if prim.arity().outputs != 1 || !prim.to_instruction().yields_bool() {
                return Vec::new();
            }
            vec![(
                Rule::TestedBool {
                    kind: graph.kind(answered).clone(),
                    test: test.clone(),
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

        // The same box twice over, read off the second and seeded at the
        // first — which is where the pattern anchors.
        (Law::Idem, NodeKind::Op(prim)) => {
            let arity = prim.arity();
            if arity.inputs != 1 || arity.outputs != 1 || !prim.to_instruction().idempotent() {
                return Vec::new();
            }
            match made_by(takes[0]) {
                Some((first, before)) if *before == kind => {
                    vec![(Rule::Idem { kind: kind.clone() }, first)]
                }
                _ => Vec::new(),
            }
        }

        // Two operands the instruction set says are interchangeable.
        // Declined where they are one wire read twice: that box already
        // *is* what the other order would build, so there is nothing for
        // the step to do, and search is where an argument like that
        // belongs.
        (Law::Commute, NodeKind::Op(prim)) => {
            if prim.arity().inputs != 2
                || !prim.to_instruction().commutative()
                || takes[0] == takes[1]
            {
                return Vec::new();
            }
            one(Rule::Commute { kind: kind.clone() })
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
pub(crate) mod tests {
    use super::*;
    use crate::kernel::build;
    use crate::kernel::graph::{find, find_pinned, isomorphic, pins_itself};
    use crate::kernel::term::Context;
    use bytecode::{Value, assemble};

    /// A law holds. Four claims, and the payload is the only input: the two
    /// sides are *built* from it rather than written out here, so this
    /// tests the table itself and not a second copy of it.
    ///
    /// 1. Both sides are graphs, and of one interface — so no step can
    ///    change what a graph takes or leaves.
    /// 2. Each side, taken as a graph in its own right, matches itself.
    /// 3. Applying the rule to one side lands on the other.
    /// 4. The step that comes back undoes it.
    ///
    /// What it does **not** say is that the two sides mean the same thing:
    /// that is the law's own content, and each caller states it in the
    /// terms the law is about. What holds the table as a whole to meaning
    /// is the corpus — see [`crate::strategy`]'s identities.
    fn holds(law: Law, rule: Rule) {
        assert_eq!(rule.law(), law, "the payload names the wrong law");
        let pair =
            sides(&rule).unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        let (lhs, rhs) = (pair.lhs(), pair.rhs());
        assert_eq!(lhs.arity(), rhs.arity());

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
            let mut whole: Graph = (*here).clone();
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
            assert!(
                isomorphic(&whole, there),
                "{:?} {:?} does not land on the other side:\n{}\n{}",
                law,
                dir,
                whole,
                there
            );

            // And the way back really is the way back.
            apply(&mut whole, &back)
                .unwrap_or_else(|e| panic!("{:?} {:?} does not undo: {}", law, dir, e));
            whole.check().unwrap();
            assert!(
                isomorphic(&whole, here),
                "{:?} {:?} does not undo to the side it started on:\n{}\n{}",
                law,
                dir,
                whole,
                here
            );
        }
    }

    /// A graph matched against itself: every box its own image, every
    /// boundary its own, and the boundary outputs served by nothing.
    fn identity(g: &Graph) -> Match {
        Match {
            nodes: (0..g.live_count()).map(NodeId::at).collect(),
            inputs: (0..g.arity().inputs).map(Source::Input).collect(),
            sel: None,
            follow: None,
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
        let term = crate::kernel::term::lower(&mut terms, &library, idx).unwrap();
        let graph = build(&terms, term);
        graph.check().unwrap();
        (terms, graph)
    }

    fn only(kind: &NodeKind, graph: &Graph) -> NodeId {
        let mut found = graph.live().filter(|(_, k)| *k == kind);
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

    // ---- the branch layer ----

    /// Every assignment of a handful of values to `width` inputs.
    ///
    /// Chosen to cover the truthiness table on both poles — `false` is the
    /// one falsy value, and `unit` is junk, which is truthy like everything
    /// else — and the tuple widths on either side of the ones the coercion
    /// laws name: `unit` is a tuple of width 0 and `(1, 2)` one of width 2,
    /// so a law about `as_tuple 2` meets a value it is the identity on, a
    /// tuple it is not, and three things that are no tuple at all.
    pub(crate) fn samples(width: usize) -> Vec<Vec<Value>> {
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
    /// ([`run_window`], so there is no second semantics), and a select
    /// keeping the block `truthy` says.
    pub(crate) fn eval_on(graph: &Graph, inputs: &[Value]) -> Vec<Value> {
        assert_eq!(inputs.len(), graph.arity().inputs, "one value per input");
        let mut held: HashMap<Source, Value> = inputs
            .iter()
            .enumerate()
            .map(|(i, v)| (Source::Input(i), v.clone()))
            .collect();
        for id in crate::kernel::graph::schedule(graph) {
            let took: Vec<Value> = graph
                .sources(id)
                .iter()
                .map(|src| held[src].clone())
                .collect();
            let answers = match graph.kind(id) {
                NodeKind::Op(prim) => run_window(&took, &prim.to_instruction())
                    .expect("every prim is total on the machine"),
                NodeKind::Select => {
                    vec![if took[0].truthy() {
                        took[1].clone()
                    } else {
                        took[2].clone()
                    }]
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
    /// The wiring settles nothing about these: the whole content of the
    /// law is what `equal`, `truthy` or `as_bool` computes. So both sides
    /// *run*, every operation on the machine itself. Sampling is not a
    /// proof, and the proof is in the docs; this is what would catch the
    /// proof being wrong.
    fn the_machine_agrees(law: Law, rule: Rule) {
        assert_eq!(rule.law(), law, "the payload names the wrong law");
        let pair =
            sides(&rule).unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        let (lhs, rhs) = (pair.lhs(), pair.rhs());
        assert_eq!(lhs.arity(), rhs.arity());
        for values in samples(lhs.arity().inputs) {
            assert_eq!(
                eval_on(lhs, &values),
                eval_on(rhs, &values),
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
    ///
    /// [`holds`] says the two sides are one window and that the step is
    /// reversible; what the law *claims* is which of the two inputs the
    /// answer side keeps, and that is stated here. Keeping the condition
    /// instead would pass every mechanical check and be a false law.
    #[test]
    fn a_block_answered_either_way_is_the_answer() {
        holds(Law::SelectSame, Rule::SelectSame);

        let pair = sides(&Rule::SelectSame).unwrap();
        let answer = pair.rhs();
        assert_eq!(
            answer.live_count(),
            0,
            "the answer holds no box:\n{}",
            answer
        );
        assert_eq!(
            answer.outputs(),
            [Source::Input(1)],
            "the answer is the block both arms gave, not the condition:\n{}",
            answer
        );
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

    /// β. Sound on **every** value and not only on booleans, because
    /// `truthy` is total: `false` is the one falsy value, so zero and junk
    /// and the empty tuple all take the then block.
    ///
    /// The window is the literal and the select, and nothing else: the
    /// untaken arm's boxes lose their reader with the select, and a box
    /// the boundary does not reach is not in the program.
    #[test]
    fn a_literal_condition_keeps_its_blocks() {
        for value in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::unit(),
        ] {
            for lit_blocks in [
                Vec::new(),
                // The condition read as a block too — the shape a `dedup`
                // makes of one pushed value.
                vec![0],
                vec![1],
                vec![0, 1],
            ] {
                the_machine_agrees(
                    Law::SelectLiteral,
                    Rule::SelectLiteral {
                        value: value.clone(),
                        lit_blocks,
                    },
                );
            }
        }
    }

    /// The same value tested twice answers the same: a branch inside an
    /// arm, retesting the outer condition, is decided by which arm it sits
    /// in.
    #[test]
    fn a_value_retested_in_an_arm_is_decided() {
        // In the then arm the value was truthy; in the else arm it was
        // `false`, the one falsy value.
        for side in [true, false] {
            the_machine_agrees(Law::SpecializeChoice, Rule::SpecializeChoice { side });
        }
    }

    /// η, spent as the three rows it is: everything downstream of a
    /// promised bool becomes a branch on it, both copies run and one
    /// kept. Every step is one of the table's own, so what is left to
    /// check is that the run lands and that the machine reads the graph
    /// it leaves the way it read the graph it started from.
    #[test]
    fn a_case_split_is_three_rows() {
        // The promise is not written down, so all three rows are spent.
        let spent = splits("pick 0 push 1 equal branch { not } { negate }", Prim::Equal);
        assert_eq!(
            spent,
            vec![Law::PromisedBool, Law::AsBoolBranch, Law::SelectHoist]
        );
        // A body reading past the answer, and one holding a branch of its
        // own.
        splits("pick 1 pick 1 equal pick 1 and", Prim::Equal);
        splits("is_int branch { push 1 } { push 2 } negate", Prim::IsInt);

        // The promise is written down already — every reader of the
        // answer is the coercion — so there is none to write and the
        // split unpacks the one standing.
        assert_eq!(
            splits("is_bool as_bool not", Prim::IsBool),
            vec![Law::AsBoolBranch, Law::SelectHoist]
        );
        // And the coercion may be the very box the split is asked at.
        assert_eq!(
            splits("as_bool not", Prim::AsBool),
            vec![Law::AsBoolBranch, Law::SelectHoist]
        );
    }

    /// A case split at the one box of `body` that is `prim`: the laws it
    /// spent, having checked that the machine reads the graph it left the
    /// way it read the one it was given.
    fn splits(body: &str, prim: Prim) -> Vec<Law> {
        let (_terms, was) = built(body);
        let mut graph = was.clone();
        let mut run = Derivation::default();
        let at = only(&NodeKind::Op(prim), &graph);
        // The wire the fresh branch should turn on: the answer that was
        // split on, or — where the box asked about is the coercion
        // itself — the wire that coercion read, since the branch a
        // coercion unpacks to reads the value rather than the coercion.
        let want = match graph.kind(at) {
            NodeKind::Op(Prim::AsBool) => graph.sources(at)[0],
            _ => Source::Port { node: at, port: 0 },
        };
        let condition = case_split(&mut graph, &mut run, at)
            .expect("the split lands")
            .expect("there is a split to make");
        graph.check().unwrap();
        assert_eq!(
            condition, want,
            "the branch turns on the wire that was split on:\n{}",
            graph
        );
        for values in samples(was.arity().inputs) {
            assert_eq!(
                eval_on(&was, &values),
                eval_on(&graph, &values),
                "{}: the split changed the program on {:?}",
                body,
                values
            );
        }
        run.steps().map(|step| step.rule.law()).collect()
    }

    /// Nothing to split: an answer the set promises nothing about, and one
    /// nothing but the boundary reads. Neither moves the graph.
    #[test]
    fn a_split_with_nothing_to_decide_is_declined() {
        for (body, prim) in [
            // `add` leaves an `Int` on every pair of values, so there is
            // no second case to pin.
            ("pick 1 pick 1 add not", Prim::Add),
            // A promised bool the boundary reads and no box does: the
            // body would be empty, and an empty body decides nothing.
            ("pick 1 pick 1 equal", Prim::Equal),
            // The same, behind a coercion that is standing already: the
            // region a split decides is that coercion's, and it is empty.
            ("is_bool as_bool", Prim::IsBool),
            ("as_bool", Prim::AsBool),
        ] {
            let (_terms, was) = built(body);
            let mut graph = was.clone();
            let mut run = Derivation::default();
            let at = only(&NodeKind::Op(prim), &graph);
            assert_eq!(case_split(&mut graph, &mut run, at), Ok(None), "{}", body);
            assert_eq!(run.len(), 0, "{}: a decline spends nothing", body);
            assert_eq!(graph, was, "{}: a decline moves nothing", body);
        }
    }

    /// The commuting conversion: what runs after a branch runs inside
    /// whichever arm it takes. Nothing is pinned, so no promise about the
    /// condition is spent — but a branch is a choice per output, and no
    /// wiring pushes an application through one, so the machine is the
    /// judge.
    #[test]
    fn a_branch_grows_over_what_follows_it() {
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                body: one_step(NodeKind::Op(Prim::Not)),
            },
        );
        // A body that reads *past* the answer: the block of the branch, and
        // one wire from outside it.
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                body: takes_all(NodeKind::Op(Prim::Add)),
            },
        );
        // A body holding a branch of its own, duplicated with it.
        the_machine_agrees(
            Law::SelectHoist,
            Rule::SelectHoist {
                body: sides(&Rule::SelectSame).unwrap().lhs().clone(),
            },
        );
        // A body that leaves nothing states no equation, and neither does
        // one that reads nothing: there is no answer to grow over.
        for refused in [
            Rule::SelectHoist {
                body: {
                    // A body that leaves nothing: one box, nothing exported.
                    let mut g = Graph::empty(1);
                    g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
                    g.close(Vec::new());
                    g
                },
            },
            Rule::SelectHoist {
                body: {
                    let mut g = Graph::empty(0);
                    let out = g.add(NodeKind::Op(Prim::Push(Value::Int(1))), Vec::new());
                    g.close(out);
                    g
                },
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
    /// The select is gone on the far side of the equation, so an answer
    /// that goes straight out is handed back as one of the body's own
    /// outputs, passed through from the input standing for it, and the
    /// new select then chooses between the very blocks the old one chose
    /// between. Read off a real graph, applied, and both sides run on the
    /// machine to check it.
    #[test]
    fn an_answer_read_from_outside_passes_through_the_body() {
        // A branch on three wires whose one answer feeds a `negate` *and*
        // leaves by the boundary.
        let mut graph = Graph::empty(3);
        let answer = graph.add(NodeKind::Select, (0..3).map(Source::Input).collect());
        let negated = graph.add(NodeKind::Op(Prim::Negate), vec![answer[0]]);
        graph.close(vec![negated[0], answer[0]]);
        graph.check().unwrap();
        let before = graph.clone();

        let select = only(&NodeKind::Select, &graph);
        let steps = propose(&graph, &[Law::SelectHoist], select);
        let [step] = &steps[..] else {
            panic!("one branch to move, and {} proposals", steps.len());
        };
        let back = apply(&mut graph, step).unwrap();
        graph.check().unwrap();

        // Two copies of the body, and a select per answer the body leaves —
        // the `negate` and the answer passed through — rather than the one
        // that was choosing between the blocks.
        assert_eq!(
            graph
                .live()
                .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
                .count(),
            2,
            "the body did not go into both arms:\n{}",
            graph
        );
        let moved: Vec<NodeId> = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Select))
            .map(|(id, _)| id)
            .collect();
        assert_eq!(moved.len(), 2, "one select per answer the body leaves");
        for &id in &moved {
            assert_eq!(
                graph.sources(id)[0],
                Source::Input(0),
                "every copy turns on the condition the branch always did:\n{}",
                graph
            );
        }
        // The passed-through answer's copy chooses between the very blocks
        // the old select chose between — so it **is** the old select, by
        // interning, and the box stays rather than being rebuilt. That is
        // the whole of what the pass-through buys: the reading moves to the
        // copy that grew over the `negate`, and the answer nothing moved
        // keeps the box it always had.
        assert!(
            moved.contains(&select),
            "the untouched answer did not keep its own box:\n{}",
            graph
        );
        assert_eq!(
            graph.outputs()[1],
            Source::Port {
                node: select,
                port: 0
            },
            "\n{}",
            graph
        );

        // The same program, on the machine, at every assignment.
        for values in samples(3) {
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

    /// The same conversion at the condition port: a branch whose
    /// condition is what another branch answered runs under that branch,
    /// once per block it chooses between.
    ///
    /// Nothing is pinned here either — the blocks reach the copies that
    /// turn on them untouched — so what is asked of any wire is the
    /// truthiness a select was reading anyway, and the machine is the
    /// judge for the reason it is `select-hoist`'s.
    #[test]
    fn a_branch_grows_over_the_branch_it_conditions() {
        the_machine_agrees(Law::CondHoist, Rule::CondHoist);
    }

    /// The row read off a graph, applied, and held to the machine — and
    /// what it copies is one select.
    ///
    /// This is the whole of why it is a row beside `select-hoist`: the
    /// cone `propose` reads for that one holds the branch below and
    /// everything after it, so hoisting past a branch that way duplicates
    /// the lot. Here two boxes become three, whatever stands downstream.
    #[test]
    fn only_the_branch_itself_is_copied() {
        // Five wires: a `select(1)` whose answer is the condition of a
        // second, and a `negate` reading what the second answers — work
        // after the branch, which stays exactly where it is.
        let mut graph = Graph::empty(5);
        let condition = graph.add(
            NodeKind::Select,
            vec![Source::Input(0), Source::Input(1), Source::Input(2)],
        );
        let answers = graph.add(
            NodeKind::Select,
            vec![condition[0], Source::Input(3), Source::Input(4)],
        );
        let after = graph.add(NodeKind::Op(Prim::Negate), answers.clone());
        graph.close(after);
        graph.check().unwrap();
        let before = graph.clone();
        let node = |src: Source| match src {
            Source::Port { node, .. } => node,
            other => panic!("not a box: {:?}", other),
        };
        let (inner, outer) = (node(condition[0]), node(answers[0]));

        let steps = propose(&graph, &[Law::CondHoist], outer);
        let [step] = &steps[..] else {
            panic!("one branch to move under, and {} proposals", steps.len());
        };
        let back = apply(&mut graph, step).unwrap();
        graph.check().unwrap();

        // Three selects and one `negate`: the branch that moved is the
        // copied box, and the region after it is untouched.
        let selects = graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Select))
            .count();
        assert_eq!(selects, 3, "the branch did not split in two:\n{}", graph);
        assert_eq!(
            graph
                .live()
                .filter(|(_, k)| matches!(k, NodeKind::Op(Prim::Negate)))
                .count(),
            1,
            "the work after the branch was copied with it:\n{}",
            graph
        );
        assert!(
            !graph.live().any(|(id, _)| id == inner),
            "the branch that made the condition is still in the program:\n{}",
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
        // No operands at all: `tuple 0` reads nothing, so there is nothing
        // for it to read that is not a literal, and the machine answers it
        // the same way it answers a window that had one.
        the_machine_agrees(
            Law::Fold,
            Rule::Fold {
                prim: Prim::Tuple(0),
                operands: Vec::new(),
                reads: Vec::new(),
            },
        );
        // The payload is the window, so a literal no input reads is not
        // part of one — and neither is a window short of its operands.
        for (prim, operands, reads) in [
            (Prim::Tuple(0), vec![Value::Int(1)], Vec::new()),
            (Prim::Add, Vec::new(), Vec::new()),
        ] {
            assert!(matches!(
                sides(&Rule::Fold {
                    prim,
                    operands,
                    reads,
                }),
                Err(Error::Ill {
                    why: Ill::Refused,
                    ..
                })
            ));
        }
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

    /// Every type test of an answer the instruction set promises is a
    /// bool: `is_bool` answers `true` and every other one answers `false`,
    /// which is the whole of what a codomain decides.
    #[test]
    fn a_promised_bool_answers_every_type_test() {
        for kind in [Prim::IsInt, Prim::Equal, Prim::IsBool, Prim::AsBool] {
            for test in [
                Prim::IsBool,
                Prim::IsInt,
                Prim::IsSymbol,
                Prim::IsConstString,
                Prim::IsTuple(None),
                Prim::IsTuple(Some(2)),
            ] {
                the_machine_agrees(
                    Law::TestedBool,
                    Rule::TestedBool {
                        kind: NodeKind::Op(kind.clone()),
                        test,
                    },
                );
            }
        }
        // An answer the set does not promise is no window.
        assert!(matches!(
            sides(&Rule::TestedBool {
                kind: NodeKind::Op(Prim::Add),
                test: Prim::IsBool,
            }),
            Err(Error::Ill {
                why: Ill::Refused,
                ..
            })
        ));
        // And neither is a box that asks nothing about a type. `not` of a
        // promised bool is a true equation of another kind entirely, and
        // this row does not state it.
        for test in [Prim::Not, Prim::AsBool, Prim::TupleLength] {
            assert!(
                matches!(
                    sides(&Rule::TestedBool {
                        kind: NodeKind::Op(Prim::IsInt),
                        test: test.clone(),
                    }),
                    Err(Error::Ill {
                        why: Ill::Refused,
                        ..
                    })
                ),
                "{:?} is no type test",
                test
            );
        }
    }

    /// The other half of the family, read off a graph rather than stated:
    /// the shape guard that asks the wrong question of a promised bool
    /// folds to `false`, and the tuple's width makes no difference to it.
    #[test]
    fn the_wrong_test_of_a_promised_bool_folds_to_false() {
        let mut graph = Graph::empty(2);
        let tested = graph.add(
            NodeKind::Op(Prim::Equal),
            vec![Source::Input(0), Source::Input(1)],
        );
        let asked = graph.add(NodeKind::Op(Prim::IsTuple(Some(2))), tested.clone());
        graph.close(vec![asked[0]]);
        graph.check().unwrap();

        let steps = propose(
            &graph,
            &[Law::TestedBool],
            only(&NodeKind::Op(Prim::IsTuple(Some(2))), &graph),
        );
        let [step] = &steps[..] else {
            panic!("one promised bool, one test:\n{}", graph)
        };
        assert_eq!(
            step.rule,
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::Equal),
                test: Prim::IsTuple(Some(2)),
            }
        );
        apply(&mut graph, step).unwrap();
        graph.check().unwrap();
        assert!(
            graph
                .live()
                .any(|(_, kind)| kind == &NodeKind::Op(Prim::Push(Value::Bool(false)))),
            "a `Bool` is no tuple:\n{}",
            graph
        );
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

    /// `or` with a literal operand, decided by `truthy` alone: the one
    /// falsy value leaves the other operand's coercion, a truthy literal
    /// leaves `true` — the poles of `and-literal`, exchanged.
    #[test]
    fn an_or_with_a_literal_is_decided_by_truthiness() {
        for value in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(7),
            Value::unit(),
        ] {
            for literal in [Side::Deep, Side::Top] {
                the_machine_agrees(
                    Law::OrLiteral,
                    Rule::OrLiteral {
                        literal,
                        value: value.clone(),
                    },
                );
            }
        }
    }

    /// A negated condition is the branch with its arms the other way
    /// round. `not v` is truthy exactly where `v` is falsy — `false` being
    /// the one falsy value — so this is exact on every value and not only
    /// on bools, which is what the sample list checks.
    #[test]
    fn a_negated_condition_swaps_the_arms() {
        the_machine_agrees(Law::NotBranch, Rule::NotBranch);

        // And it is read off the select, seeded at the `not` — the box the
        // pattern begins with — with the blocks coming back exchanged.
        let mut graph = Graph::empty(3);
        let flipped = graph.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let answers = graph.add(
            NodeKind::Select,
            vec![flipped[0], Source::Input(1), Source::Input(2)],
        );
        graph.close(answers);
        graph.check().unwrap();
        let before = graph.clone();

        let select = only(&NodeKind::Select, &graph);
        let steps = propose(&graph, &[Law::NotBranch], select);
        let [step] = &steps[..] else {
            panic!("one negated condition:\n{}", graph)
        };
        assert_eq!(step.rule, Rule::NotBranch);
        assert_eq!(
            step.at.nodes[0],
            only(&NodeKind::Op(Prim::Not), &graph),
            "the pattern is built `not`-first, so that is where it anchors"
        );
        apply(&mut graph, step).unwrap();
        graph.check().unwrap();

        // The negation is gone — nothing else read it — and the branch now
        // turns on the value itself, its blocks exchanged.
        assert_eq!(graph.live_count(), 1, "the `not` is spent:\n{}", graph);
        let moved = only(&NodeKind::Select, &graph);
        assert_eq!(
            graph.sources(moved),
            [Source::Input(0), Source::Input(2), Source::Input(1)],
            "\n{}",
            graph
        );
        for values in samples(3) {
            assert_eq!(
                eval_on(&before, &values),
                eval_on(&graph, &values),
                "the arms swapped and the program changed, on {:?}",
                values
            );
        }
    }

    /// Doing it twice is doing it once, for every operation the
    /// instruction set says so of — which is the three coercions, widths
    /// and all.
    #[test]
    fn an_idempotent_operation_done_twice_is_done_once() {
        for prim in [
            Prim::AsBool,
            Prim::AsInt,
            Prim::AsTuple(1),
            Prim::AsTuple(2),
        ] {
            the_machine_agrees(
                Law::Idem,
                Rule::Idem {
                    kind: NodeKind::Op(prim),
                },
            );
        }
        // Nothing else is. `not ; not` is a row of its own and a different
        // one — the coercion, not the `not` — and `tuple 1` wraps again.
        for prim in [Prim::Not, Prim::Negate, Prim::Tuple(1), Prim::IsBool] {
            assert!(
                matches!(
                    sides(&Rule::Idem {
                        kind: NodeKind::Op(prim.clone()),
                    }),
                    Err(Error::Ill {
                        why: Ill::Refused,
                        ..
                    })
                ),
                "{:?} is not idempotent",
                prim
            );
        }

        // Two of one width collapse; two of different widths are two
        // questions, and no payload the graph offers states them as one.
        let mut graph = Graph::empty(1);
        let inner = graph.add(NodeKind::Op(Prim::AsTuple(2)), vec![Source::Input(0)]);
        let outer = graph.add(NodeKind::Op(Prim::AsTuple(3)), inner);
        graph.close(outer);
        graph.check().unwrap();
        assert!(
            propose(
                &graph,
                &[Law::Idem],
                only(&NodeKind::Op(Prim::AsTuple(3)), &graph)
            )
            .is_empty(),
            "the width is part of the type:\n{}",
            graph
        );
    }

    /// The other order is the same answer, for every operation the
    /// instruction set says so of — the junk answer included, since `add`
    /// on a symbol and an int answers `0` whichever way round they arrive.
    #[test]
    fn a_commutative_operation_reads_its_operands_either_way() {
        for prim in [Prim::Add, Prim::Multiply, Prim::And, Prim::Or, Prim::Equal] {
            the_machine_agrees(
                Law::Commute,
                Rule::Commute {
                    kind: NodeKind::Op(prim),
                },
            );
        }
        // Nothing else does, and a one-operand box has no order at all.
        for prim in [Prim::Subtract, Prim::Less, Prim::Tuple(2), Prim::Not] {
            assert!(
                matches!(
                    sides(&Rule::Commute {
                        kind: NodeKind::Op(prim.clone()),
                    }),
                    Err(Error::Ill {
                        why: Ill::Refused,
                        ..
                    })
                ),
                "{:?} does not commute",
                prim
            );
        }

        // No list drives it: it permutes rather than shrinking, so a
        // driver run to fixpoint would swap the same pair forever.
        assert!(!folding().contains(&Law::Commute));
        assert!(!branching().contains(&Law::Commute));

        // And one wire read twice is already the box the swap would build,
        // so the search does not offer a step that does nothing.
        let mut graph = Graph::empty(1);
        let doubled = graph.add(
            NodeKind::Op(Prim::Add),
            vec![Source::Input(0), Source::Input(0)],
        );
        graph.close(doubled);
        graph.check().unwrap();
        assert!(
            propose(
                &graph,
                &[Law::Commute],
                only(&NodeKind::Op(Prim::Add), &graph)
            )
            .is_empty(),
            "there is nothing to exchange:\n{}",
            graph
        );
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
                !folding().contains(&law) && !branching().contains(&law),
                "{} grows a graph; no list should drive it",
                law
            );
        }

        // The round trip, with the coercion's port read by something else
        // as well — no obstacle, since the rewrite replaces only the
        // rebuilt tuple's value and the coercion stays for its reader.
        let mut graph = Graph::empty(1);
        let coerced = graph.add(NodeKind::Op(Prim::AsTuple(2)), vec![Source::Input(0)]);
        let parts = graph.add(NodeKind::Op(Prim::Untuple(2)), coerced.clone());
        let rebuilt = graph.add(NodeKind::Op(Prim::Tuple(2)), parts);
        let elsewhere = graph.add(NodeKind::Op(Prim::IsTuple(None)), coerced.clone());
        graph.close(vec![rebuilt[0], elsewhere[0]]);
        graph.check().unwrap();
        assert_eq!(
            graph.sinks(coerced[0]).len(),
            2,
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

    /// A payload naming a block the select does not have states no
    /// equation, and is refused before anything is compared.
    #[test]
    fn a_block_the_select_lacks_is_refused() {
        // A select has two blocks, so `2` is not one of them — and a
        // block named twice is a payload naming one block, not two.
        for refused in [
            Rule::SelectLiteral {
                value: Value::Bool(true),
                lit_blocks: vec![2],
            },
            Rule::SelectLiteral {
                value: Value::Bool(true),
                lit_blocks: vec![0, 0],
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

    /// A branch choosing between an `equal`'s two operands answers with
    /// the one it takes when the test **fails**, whatever the test said:
    /// `equal` is structural identity, so where the other block is reached
    /// the two operands are one value.
    ///
    /// Both readings, and the branch goes altogether either way: a select
    /// carries one answer, so answering it is the whole of the box.
    #[test]
    fn a_branch_between_what_it_compared_is_one_of_them() {
        for answered in [Side::Deep, Side::Top] {
            the_machine_agrees(Law::SpecializeEqual, Rule::SpecializeEqual { answered });
        }
    }

    /// `as_bool` of the very value a branch tested is what the branch
    /// decided. Exact on both arms: `as_bool` *is* `truthy` made into an
    /// instruction, and the else block is reached only by `false`.
    #[test]
    fn as_bool_of_a_condition_is_what_the_branch_decided() {
        // Both halves: the then block folds to `true`, the else to `false`.
        for then in [true, false] {
            the_machine_agrees(Law::SpecializeBool, Rule::SpecializeBool { then });
        }
    }

    // ---- the checker does not match ----

    /// The walk can start anywhere: pinning any box of a side to its own
    /// image finds the identity embedding, and the answer comes back in
    /// pattern order whatever order the search visited it in.
    #[test]
    fn a_pattern_is_found_from_any_of_its_boxes() {
        for rule in table() {
            let pair = sides(&rule).unwrap();
            for side in [pair.lhs(), pair.rhs()] {
                if !pins_itself(side) {
                    continue;
                }
                for i in 0..side.live_count() {
                    assert!(
                        find_pinned(side, side, i, NodeId::at(i)).contains(&identity(side)),
                        "{:?}: pinned at box {}, the identity was not found:\n{}",
                        rule.law(),
                        i,
                        side
                    );
                }
            }
        }
    }

    // ---- the table, against a graph ----

    /// One payload per row of the table, and between them every law.
    fn table() -> Vec<Rule> {
        vec![
            Rule::NotNot,
            Rule::AndLiteral {
                literal: Side::Top,
                value: Value::Bool(true),
            },
            Rule::OrLiteral {
                literal: Side::Deep,
                value: Value::Bool(false),
            },
            Rule::TupleCancel { n: 2 },
            Rule::AsTupleBuilt { n: 2 },
            Rule::EqualRefl,
            Rule::SelectSame,
            Rule::SelectLiteral {
                value: Value::Bool(false),
                lit_blocks: vec![1],
            },
            Rule::NotBranch,
            Rule::SpecializeEqual {
                answered: Side::Top,
            },
            Rule::SpecializeBool { then: true },
            Rule::SpecializeChoice { side: true },
            Rule::SelectHoist {
                body: one_step(NodeKind::Op(Prim::Not)),
            },
            Rule::CondHoist,
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
                test: Prim::IsBool,
            },
            Rule::TestedBool {
                kind: NodeKind::Op(Prim::IsInt),
                test: Prim::IsInt,
            },
            Rule::Retuple { n: 2 },
            Rule::AsTupleRoundTrip { n: 2 },
            Rule::IsTupleBuilt { built: 2, asked: 2 },
            Rule::IsTupleBuilt { built: 2, asked: 3 },
            Rule::Idem {
                kind: NodeKind::Op(Prim::AsTuple(2)),
            },
            Rule::Commute {
                kind: NodeKind::Op(Prim::Add),
            },
            Rule::AsBoolBranch,
            Rule::CoercionGuard {
                prim: Prim::AsTuple(2),
            },
            Rule::CoercionGuard { prim: Prim::AsInt },
            Rule::CoercionGuard { prim: Prim::AsBool },
        ]
    }

    /// Every law there is, the lists included and the several they leave
    /// out — `select-hoist`, `cond-hoist` and the two unpackings grow a
    /// graph, so no list hands any of them out. Taken
    /// from the enum rather than rebuilt here, so a law added to the table
    /// is a law this file's round trips cover.
    fn every_law() -> Vec<Law> {
        Law::every()
    }

    /// Every proposal at every box of `graph`, applied to a copy of it and
    /// held to [`Graph::check`](crate::kernel::graph::Graph::check) — the laws it read off,
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
    /// shape that a rewrite made, so the specializing rows — which want a
    /// block that a rewrite has identified with the condition — never
    /// match one at all, however many sentences are walked.
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
            let pair = sides(&rule).unwrap();
            let note = format!("{:?}", law);
            let spent = each_proposal(pair.lhs(), &note);
            assert!(
                spent.contains(&law),
                "{:?}: the matcher does not read its own shape back:\n{}",
                law,
                pair.lhs()
            );
        }
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
        // Between them, every law a built graph can offer. The ones the
        // list cannot reach — the specializing rows — want a shape a
        // rewrite makes, and are covered above against the shapes the
        // table itself states.
        //
        // The lists are short, and that is the point: a graph arrives with
        // no wiring to sweep, so what it offers on the first asking is
        // what it is about.
        // `add` reads two literals, so the fold decides it — and the
        // instruction set says its operands are interchangeable, which is
        // a step at the same box and on no driven list.
        offers("push 1 push 2 add", &[Law::Fold, Law::Commute]);
        // The window with nothing in it. `tuple 0` reads no literal, so
        // there is none behind it to anchor the pattern at and the box
        // anchors itself — and the fold is offered all the same.
        offers("tuple 0", &[Law::Fold]);
        // Every operand a literal, and the answer is the tuple they
        // build.
        offers("push 1 push 2 tuple 2", &[Law::Fold]);
        // And the way back: a literal taken apart is its parts.
        offers("push (1, 2) untuple 2", &[Law::Fold]);
        offers("swap swap", &[]);
        offers("push 9 pick 0", &[]);
        offers("dip { swap } swap dip { swap }", &[]);
        // Nothing at all: the comparison is dropped, so the boundary
        // reaches no box and there is no box to read a law off.
        offers("pick 1 pick 1 equal drop 0", &[]);
        // The answer goes straight to the boundary, so there is no
        // region downstream of it for a case split to decide.
        offers("pick 1 pick 1 equal", &[Law::PromisedBool, Law::Commute]);
        // One wire compared with itself — which is what it is, now that
        // `pick` is a second reference rather than a `copy`.
        offers("pick 0 pick 0 equal", &[Law::EqualRefl, Law::PromisedBool]);
        offers(
            "branch { pick 0 drop 0 not } { not }",
            &[Law::PromisedBool, Law::SelectSame],
        );
        offers(
            "pick 0 push 1 equal branch { not } { negate }",
            &[Law::PromisedBool, Law::Commute],
        );
        // One operation in both arms is *one box*: the two arms are handed
        // the same sources, so they compute the same value and there is
        // one of it.
        offers("branch { add } { add }", &[Law::SelectSame, Law::Commute]);
        offers(
            "push 1 pick 1 branch { add } { add }",
            &[Law::SelectSame, Law::Commute],
        );
        // Work after a branch, which is what `select-hoist` reads: the
        // region downstream of the select's answers, lifted out as the
        // body the branch grows over. Nothing about the condition is
        // asked, so this is the one row here that offers on a branch
        // whatever made the wire it turns on.
        offers(
            "branch { negate } { negate } negate",
            &[Law::SelectSame, Law::SelectHoist],
        );

        // A literal condition: the select is the blocks it chooses.
        offers(
            "push true branch { push 1 } { push 2 }",
            &[Law::SelectLiteral],
        );
    }

    /// Every law the built graph proposes somewhere, and no other.
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
            24,
            "a law joined the table: name it, and list it in `Law::every`"
        );
        let mut names: Vec<&str> = all.iter().map(|law| law.name()).collect();
        names.sort_unstable();
        let spelled = names.len();
        names.dedup();
        assert_eq!(names.len(), spelled, "two laws share a spelling");
        for law in [branching(), folding()].concat() {
            assert!(all.contains(&law), "{:?} is on no vocabulary", law);
        }
    }

    /// The point of the split. A match is a claim about ports, and every
    /// way it can be false is decided by comparing ports — there is no
    /// searching in the checker to go wrong.
    ///
    /// Three ways, and a reader the window does not export is none of
    /// them: substitution strands nothing, so there is nothing to
    /// account for.
    #[test]
    fn a_match_that_does_not_fit_is_refused() {
        let (_terms, mut graph) = built("not negate");
        let negate = only(&NodeKind::Op(Prim::Negate), &graph);
        let not = only(&NodeKind::Op(Prim::Not), &graph);

        let refuse = |graph: &mut Graph, step: &Step| match apply(graph, step) {
            Err(Error::NotThere { at, .. }) => at,
            other => panic!("accepted: {:?}", other.map(|_| ())),
        };

        // The right law and the wrong box.
        let step = Step {
            rule: Rule::NotNot,
            dir: Direction::Forward,
            at: Match {
                nodes: vec![negate, not],
                inputs: vec![Source::Input(0)],
                sel: None,
                follow: None,
            },
        };
        assert_eq!(refuse(&mut graph, &step), Mismatch::Kind(negate));

        // The right boxes, and an input port that reads something else.
        let step = Step {
            rule: Rule::NotNot,
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not, not],
                inputs: vec![Source::Input(0)],
                sel: None,
                follow: None,
            },
        };
        assert_eq!(
            refuse(&mut graph, &step),
            Mismatch::Edge(Sink::Port { node: not, port: 0 })
        );

        // A match that is not the shape of the pattern at all.
        let step = Step {
            rule: Rule::NotNot,
            dir: Direction::Forward,
            at: Match {
                nodes: vec![not],
                inputs: vec![Source::Input(0)],
                sel: None,
                follow: None,
            },
        };
        assert_eq!(refuse(&mut graph, &step), Mismatch::Shape);

        // And nothing above changed the graph.
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 2);
    }

    /// A right-hand side is looked for like any other graph.
    ///
    /// It was not, and the reason was the reader-split: a side exporting
    /// one port twice left nothing in the host to say which of that port's
    /// readers belonged to which export, so those steps had to be stated.
    /// A substitution never asks, so backward is a direction like forward.
    #[test]
    fn a_right_hand_side_is_looked_for_like_any_other() {
        let (_terms, graph) = built("as_bool");
        let pair = sides(&Rule::NotNot).unwrap();
        let found = find(&graph, pair.rhs());
        assert_eq!(found.len(), 1, "`not-not`'s answer is standing right there");

        // And it is a step: the coercion comes back as the two `not`s.
        let mut graph = graph.clone();
        apply(
            &mut graph,
            &Step {
                rule: Rule::NotNot,
                dir: Direction::Backward,
                at: found[0].clone(),
            },
        )
        .expect("a backward step is a step");
        graph.check().unwrap();
        assert_eq!(graph.live_count(), 2, "two `not`s:\n{}", graph);
    }

    // ---- a derivation carried somewhere else ----

    /// `not ; not ; not`, and its three boxes deepest first.
    fn three_nots() -> (Graph, Vec<NodeId>) {
        let mut g = Graph::empty(1);
        let first = g.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
        let second = g.add(NodeKind::Op(Prim::Not), first);
        let third = g.add(NodeKind::Op(Prim::Not), second);
        g.close(third);
        g.check().unwrap();
        let ids: Vec<NodeId> = g.live().map(|(id, _)| id).collect();
        (g, ids)
    }

    /// A run about `not ; not` alone: spend `not-not`, then open the
    /// `as_bool` it leaves into the branch it is.
    ///
    /// Two steps, and the second names a box the *first one made* — which is
    /// the whole difficulty in carrying a run somewhere else, since that box
    /// has a different id wherever it is put down.
    fn open_a_double_negative() -> (Graph, Vec<Step>) {
        let lemma = sides(&Rule::NotNot).unwrap().lhs().clone();
        let mut alone = lemma.clone();
        let first = Step {
            rule: Rule::NotNot,
            dir: Direction::Forward,
            at: identity(&lemma),
        };
        let made = apply(&mut alone, &first).unwrap().at.nodes[0];
        let second = Step {
            rule: Rule::AsBoolBranch,
            dir: Direction::Forward,
            at: Match {
                nodes: vec![made],
                inputs: vec![Source::Input(0)],
                sel: None,
                follow: None,
            },
        };
        apply(&mut alone, &second).unwrap();
        alone.check().unwrap();
        assert!(
            alone.live().any(|(_, k)| matches!(k, NodeKind::Select)),
            "the run ends in the branch `as_bool` is:\n{}",
            alone
        );
        (lemma, vec![first, second])
    }

    /// The whole point of an embedding: a run written about one graph, spent
    /// where that graph was found inside another, and the record it leaves
    /// replaying against that other on its own.
    #[test]
    fn a_derivation_travels_to_where_its_graph_was_found() {
        let (lemma, proof) = open_a_double_negative();
        let branch = sides(&Rule::AsBoolBranch).unwrap().rhs().clone();

        // A host holding the lemma's left-hand side twice, one copy
        // overlapping the other, so neither embedding is the whole graph.
        let (host, boxes) = three_nots();
        let found = find(&host, &lemma);
        assert_eq!(found.len(), 2, "either adjacent pair:\n{}", host);

        for at in &found {
            let deepest = at.nodes[0] == boxes[0];
            let mut there = host.clone();
            let run = transplant(&mut there, &lemma, at, &proof).unwrap();
            there.check().unwrap_or_else(|e| panic!("{}\n{}", e, there));
            assert_eq!(run.len(), proof.len());

            // The `not` the run never touched is still there, still on the
            // right side of what the run left. That is what carrying the
            // *boundary* buys: the lemma's own input and output stood for a
            // box of the host at each end, and the branch that replaced the
            // pair is wired to them.
            let mut want = Graph::empty(1);
            let out = if deepest {
                let opened = want.implant(&branch, &[Source::Input(0)]);
                want.add(NodeKind::Op(Prim::Not), opened)
            } else {
                let kept = want.add(NodeKind::Op(Prim::Not), vec![Source::Input(0)]);
                want.implant(&branch, &kept)
            };
            want.close(out);
            assert!(isomorphic(&there, &want), "\n{}\n{}", there, want);

            // And the record is a proof about the host: it replays against a
            // fresh copy of it and lands in the same place.
            let record: Vec<Step> = run.steps().cloned().collect();
            let mut again = host.clone();
            replay(&mut again, &record).unwrap();
            assert!(isomorphic(&again, &there), "\n{}\n{}", again, there);

            // The run undoes as well, since every carried step went through
            // `apply` and handed back its inverse.
            run.undo(&mut there).unwrap();
            assert!(isomorphic(&there, &host), "\n{}\n{}", there, host);
        }
    }

    /// Nothing is carried on trust: a match that does not put the run's graph
    /// where it says, and a step that is not about that graph, are both
    /// refused with the host untouched.
    #[test]
    fn a_derivation_carried_through_nothing_is_refused() {
        let (lemma, proof) = open_a_double_negative();
        let (host, boxes) = three_nots();

        // The two boxes are there, and in the other order they are a match —
        // but not in this one, so the pattern's edge does not hold.
        let backwards = Match {
            nodes: vec![boxes[1], boxes[0]],
            inputs: vec![Source::Input(0)],
            sel: None,
            follow: None,
        };
        let mut there = host.clone();
        assert!(matches!(
            transplant(&mut there, &lemma, &backwards, &proof),
            Err(Error::NotEmbedded(_))
        ));
        assert_eq!(there, host, "a refusal changes nothing");

        // A step that is not about the lemma is refused by the lemma, before
        // the host is touched at all.
        let at = find(&host, &lemma)[0].clone();
        let stray = Step {
            rule: Rule::EqualRefl,
            dir: Direction::Forward,
            at: identity(&lemma),
        };
        let mut there = host.clone();
        assert!(matches!(
            transplant(&mut there, &lemma, &at, &[stray]),
            Err(Error::NotThere { .. })
        ));
        assert_eq!(there, host, "a refusal changes nothing");

        // And so is a run whose *second* step goes wrong: the first landed
        // on the copy, and the host still never moved.
        let mut half = proof.clone();
        half[1].at.nodes[0] = NodeId::at(99);
        let mut there = host.clone();
        assert!(transplant(&mut there, &lemma, &at, &half).is_err());
        assert_eq!(there, host, "a refusal changes nothing");
    }
}
