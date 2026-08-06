//! The equations, and the steps that invoke them.
//!
//! An equation closes over its arguments and from them generates two program
//! sequences — a left-hand side and a right-hand side — which it asserts always
//! behave identically. That is the whole of what a rule is here. It does not
//! search, does not decide where it applies, and does not know which direction
//! it is being read in; [`crate::applier`] does the applying and
//! [`crate::matcher`] does the finding.
//!
//! This is the layer that used to be tangled together with the search. The old
//! rules matched a window *and* produced its replacement, which meant every
//! equation was written once per direction — `collapse` and `expand`, `sink`
//! and `float` — and every one carried a termination measure that had nothing
//! to do with whether the equation was true. Both go away here: a direction is
//! something a step says, and a script is finite by construction, so
//! termination is entirely the generator's problem.
//!
//! ## What an argument may be
//!
//! Everything the two sides are built from, including facts that originate in
//! the library. The claimed arity of `X` in [`Rule::Interchange`] is an
//! argument, not a lookup, so `lhs` and `rhs` are pure functions of the
//! arguments. What keeps that honest is [`Rule::check`], which the applier is
//! required to run first and which verifies every claim against the real
//! [`Program`]. **A script is never trusted.** It communicates a construction,
//! and every fact that construction rests on is re-derived by the applier.
//!
//! ## The global precondition
//!
//! The tool works only on sentences that are neither `#[recursive]` nor able to
//! fail, and refuses others up front (see `main`). Both properties are closed
//! over reachability, so every node any tree here can hold is total and
//! non-recursive. Several conditions the old rules needed therefore collapse:
//! [`Rule::Annihilate`] asks only for an arity where `speculable` used to
//! require a syntactic whitelist, because there is no `assert` left to run on a
//! path that would not have run it. Each such place says so, since lifting the
//! restriction means putting the condition back.

use bytecode::value::numeric_cmp;
use bytecode::{Instruction, SentenceIndex, Value};

use crate::arity::full_arity;
use crate::ir::{Node, frame_depth, with_frame_depth};
use crate::location::Location;
use crate::program::Program;

/// Which way a step reads its equation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Direction {
    /// Find the left-hand side, leave the right.
    Forward,
    /// Find the right-hand side, leave the left.
    Reverse,
}

impl Direction {
    /// The opposite reading of the same equation.
    ///
    /// Undoing a derivation is reversing every step and running it backwards,
    /// which is what `applier`'s round-trip tests do with this.
    #[allow(dead_code)]
    pub(crate) fn flipped(self) -> Direction {
        match self {
            Direction::Forward => Direction::Reverse,
            Direction::Reverse => Direction::Forward,
        }
    }

    /// How a script listing shows the direction.
    pub(crate) fn arrow(self) -> &'static str {
        match self {
            Direction::Forward => "->",
            Direction::Reverse => "<-",
        }
    }
}

/// A reason an equation does not apply to the arguments it was given.
///
/// Every one of these is a statement about the arguments, never about the tree
/// they were going to be applied to — that is [`crate::applier::ApplyError`]'s
/// business. During a live run any of these means the matcher that proposed the
/// step got something wrong.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SideCondition {
    /// `unfold` was asked to open a sentence with no finite expansion.
    RecursiveTarget { target: SentenceIndex },
    /// The node an equation wanted to move past has no frame to speak of — a
    /// plain instruction, or the `jump` that a `Call { depth: 0 }` is.
    NotFramed { found: String },
    /// A node's arity could not be worked out. Under the global precondition
    /// this should not be reachable from a real tree, and reaching it means
    /// either a synthetic node in a test or a bug.
    ArityUnknown { found: String },
    /// The arity an argument claimed is not the one the library gives.
    ClaimedArityMismatch {
        claimed: (i64, i64),
        actual: (i64, i64),
    },
    /// Interchange: the hidden window does not clear what the moved node leaves
    /// behind, so the two genuinely interfere.
    FrameTooShallow { depth: usize, outputs: i64 },
    /// A frame depth came out negative or too large to represent.
    DepthOverflow { shifted: i64 },
    /// `eval` was handed an operator it has no answer for, or the wrong number
    /// of operands for one it does.
    NotEvaluable { op: String, operands: usize },
    /// `commute` was handed an operator that does not answer the same either
    /// way round.
    NotCommutative { op: String },
    /// `bool_result` was handed an operator that does not always leave a bool.
    NotBoolResult { op: String },
    /// `retest` was handed something other than a branch to collapse.
    NotABranch { arm: &'static str, found: String },
}

impl std::fmt::Display for SideCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SideCondition::RecursiveTarget { target } => write!(
                f,
                "#{} is #[recursive] and has no finite expansion",
                usize::from(*target)
            ),
            SideCondition::NotFramed { found } => {
                write!(f, "`{}` has no frame to move a window through", found)
            }
            SideCondition::ArityUnknown { found } => {
                write!(f, "the arity of `{}` is not known", found)
            }
            SideCondition::ClaimedArityMismatch { claimed, actual } => write!(
                f,
                "the step claims arity {:?} but the library says {:?}",
                claimed, actual
            ),
            SideCondition::FrameTooShallow { depth, outputs } => write!(
                f,
                "a window {} deep does not clear the {} value(s) left behind",
                depth, outputs
            ),
            SideCondition::DepthOverflow { shifted } => {
                write!(
                    f,
                    "the shifted frame depth {} is not representable",
                    shifted
                )
            }
            SideCondition::NotEvaluable { op, operands } => {
                write!(f, "`{}` cannot be folded on {} operand(s)", op, operands)
            }
            SideCondition::NotCommutative { op } => {
                write!(
                    f,
                    "`{}` does not answer the same with its operands swapped",
                    op
                )
            }
            SideCondition::NotBoolResult { op } => {
                write!(f, "`{}` does not always leave a boolean on top", op)
            }
            SideCondition::NotABranch { arm, found } => {
                write!(
                    f,
                    "the {} arm opens with `{}`, which is not a branch and so \
                     tests nothing",
                    arm, found
                )
            }
        }
    }
}

/// Which arm of a branch a law is talking about.
///
/// [`crate::ir::Selector`] has a third case for a dip body, which has no
/// meaning here; two variants is the whole of what [`Rule::Retest`] can mean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arm {
    Then,
    Else,
}

impl Arm {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Arm::Then => "then",
            Arm::Else => "else",
        }
    }
}

/// An equation: two program sequences that always behave identically.
///
/// Each variant states its law in its doc comment as `LHS = RHS`, together with
/// what it takes on faith and what [`Rule::check`] verifies. Adding one is
/// meant to be rare — a new equation is a new axiom, and everything the search
/// can do is a consequence of these.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Rule {
    /// `dip k { dip j { A } }` = `dip (k+j) { A }`.
    ///
    /// Hiding `k` values and then hiding `j` more of what is left is hiding
    /// `k + j`, so a dip whose whole body is another dip is a nesting level
    /// that says nothing.
    ///
    /// Read forward this is the old `collapse`; read backward, at the split
    /// `(1, k-1)`, it is the old `expand`, which wrote a hidden region in unary
    /// one level per hidden value. Two rules, one law — and the split the
    /// backward reading needs is an argument rather than a special case.
    Collapse {
        k: usize,
        j: usize,
        a: Vec<Node>,
        /// Provenance of the outer and inner frames, kept so that the listing
        /// still says where code came from after the two are merged.
        outer: Vec<String>,
        inner: Vec<String>,
    },

    /// `dip 0 { A }` = `A`.
    ///
    /// A frame that hides nothing runs its body on exactly the stack outside
    /// it. Read forward this is the old `flatten_call`, and it is what lets
    /// every other equation reach across a call once it has been unfolded:
    /// rules see one sequence at a time, so a branch one frame down and an
    /// instruction outside it are simply not in the same window until this has
    /// fired.
    ///
    /// Read backward it *introduces* a frame around a run of nodes, which is
    /// how a shared prefix gets wrapped up before [`Rule::Hoist`] carries it
    /// out of a branch.
    ElimDip0 { a: Vec<Node>, origins: Vec<String> },

    /// `X ; D_k` = `D_(k-m+n) ; X`, where `X : n -> m` and `k >= m`.
    ///
    /// The interchange law, and the one piece of real arithmetic in the set.
    /// `D` is a framed node — a dip, or a call that hides something — and its
    /// hidden window has to sit entirely below everything `X` leaves behind,
    /// which is `k >= m`. The same window is `k - m + n` deep on the other side
    /// of `X`.
    ///
    /// One equation covers every `X`: push (0→1), drop (1→0), arithmetic (2→2),
    /// `pick d` (d+1→d+2), `roll d` (d+1→d+1), and a nested dip alike. It also
    /// covers both old rules, because `k >= m` read from the left and `j >= n`
    /// read from the right are the same condition: with `j = k - m + n`,
    /// `j >= n` iff `k >= m`. Forward is the old `sink`, backward the old
    /// `float`.
    ///
    /// `framed` carries the left-hand side's depth `k`, and `D` may be an
    /// unexpanded call as readily as a spelled-out dip: the condition is about
    /// the frame, and the callee's body has no say in it. A `Call { depth: 0 }`
    /// is a plain jump with no frame at all and is rejected.
    Interchange {
        x: Node,
        /// The framed node as it stands on the left-hand side.
        framed: Node,
        /// `x`'s arity, claimed by the step and checked against the library.
        n: i64,
        m: i64,
    },

    /// `dip k { A } ; dip k { B }` = `dip k { A B }`.
    ///
    /// The second hides exactly what the first restored, so the region can just
    /// stay hidden across both. Read backward it splits one frame into two at a
    /// point the arguments name.
    Fuse {
        k: usize,
        a: Vec<Node>,
        b: Vec<Node>,
        a_origins: Vec<String>,
        b_origins: Vec<String>,
    },

    /// `dip (k+1) { X } ; branch { A } { B }`
    ///   = `branch { dip k { X } ; A } { dip k { X } ; B }`.
    ///
    /// A `dip (k+1)` hides the condition and `k` values above whatever `X`
    /// touches; the branch pops the condition, so inside an arm the same window
    /// is one shallower. Forward is the old `unfactor_branch`, pushing a
    /// computation into both arms so that a law which only holds on one side
    /// can see it.
    ///
    /// Backward is the old `factor_branch`, and this is where the two-layer
    /// split earns its keep. That rule hoisted a shared *prefix* of any length
    /// and spliced it out in one motion; here it is a script — wrap the prefix
    /// in a frame in each arm with [`Rule::ElimDip0`] backward, then read this
    /// equation backward to lift the two frames into one. Three steps, each of
    /// which is an instance of a law, instead of one rule that knew a whole
    /// procedure.
    ///
    /// The arms are found by effect rather than by label, since two identical
    /// blocks compiled to different sentences never share one.
    Hoist {
        k: usize,
        x: Vec<Node>,
        origins: Vec<String>,
        then_arm: Vec<Node>,
        else_arm: Vec<Node>,
        then_origin: String,
        else_origin: String,
    },

    /// `branch { A } { B } ; C` = `branch { A C } { B C }`.
    ///
    /// `C` runs after whichever arm was taken, so moving it inside both changes
    /// nothing. The point is to put it somewhere a law can see it in context.
    ///
    /// `C` is a whole sequence, where the old `distribute_branch` took a single
    /// node and had to be iterated. Backward it factors a shared suffix out of
    /// both arms, which the old set could not express at all — `factor_branch`
    /// only ever worked on prefixes.
    Distribute {
        then_arm: Vec<Node>,
        else_arm: Vec<Node>,
        suffix: Vec<Node>,
        then_origin: String,
        else_origin: String,
    },

    /// `push c ; branch { A } { B }` = the arm `c` selects.
    ///
    /// **Any** literal decides, not only a `Bool`. A branch takes the then arm
    /// exactly when the condition is `Bool(true)` and the else arm on
    /// everything else, so `push 1; branch` is decided just as firmly as
    /// `push false; branch` — it goes to the else arm. The selector is
    /// [`Value::truthy`] and must stay that way: reading it as a test for
    /// *being* a boolean would send junk down the wrong path.
    FoldBranch {
        c: Value,
        then_arm: Vec<Node>,
        else_arm: Vec<Node>,
        then_origin: String,
        else_origin: String,
    },

    /// `push v1 ; … ; push vn ; op` = the pushes of what `op` answers.
    ///
    /// **Folding is evaluation.** Every operator here is total, so running it
    /// on known values and pushing the answer is the same program; there is no
    /// operand it could have rejected and no check the fold discards. What the
    /// equation owes is not a licence but an obligation — to agree with the
    /// interpreter exactly, on junk as much as on anything else — which is why
    /// [`eval_op`] goes through `bytecode::value` rather than through a second
    /// reading of the same rules.
    ///
    /// Subsumes the old `fold_const` and `fold_const_unary`, which differed
    /// only in how many operands they read.
    Eval { op: Instruction, inputs: Vec<Value> },

    /// `X ; drop^m` = `drop^n`, where `X : n -> m`.
    ///
    /// Computing a value and throwing it away is throwing away the operands
    /// instead. Subsumes the old `annihilate_drop` (m = 1) and
    /// `annihilate_flagged` (m = 2, which existed because a fallible
    /// instruction leaves its flag beside its value).
    ///
    /// The arity is the *whole* condition, which it was not before. The old
    /// rules asked for a syntactic whitelist so that an `assert` buried in a
    /// dip body could not be dropped along with its results; under the global
    /// precondition no such node exists, so this reaches calls, dips and
    /// branches that used to be refused. Lifting that restriction means
    /// bringing the predicate back.
    /// `X` is a whole sequence, not a single node. Read backward that is what
    /// makes this the introduction rule: the arguments say *what computation to
    /// conjure*, and nothing in the window it replaces could have said it.
    Annihilate { x: Vec<Node>, n: usize, m: usize },

    /// `roll 1 ; op` = `op`, for a commutative `op`.
    ///
    /// `roll 1` swaps the top two values, so for an operator that answers the
    /// same either way round the swap is invisible. The commutative set is
    /// `add`, `multiply`, `and`, `or` and `equal`, and it lives on the
    /// instruction ([`Instruction::commutative`]) rather than here — it is a
    /// fact about the instruction set, and `vm` measures it against the
    /// interpreter rather than taking the list on faith.
    ///
    /// Read forward this deletes a shuffle. Read backward it *introduces* one,
    /// which is how the operands of a commutative operator get swapped so that
    /// what is underneath them lines up with something else — the same job
    /// [`Rule::Annihilate`] backwards does for a whole computation.
    ///
    /// The flag a fallible operator leaves is symmetric too, so this holds for
    /// `add` on operands it cannot add: `0, false` either way round.
    Commute { op: Instruction },

    /// `pick 0 ; is_bool ; branch { branch { push true } { push false } } { }`
    /// = nothing.
    ///
    /// **A boolean is either `true` or `false`.** Copy the value, ask whether
    /// it is a boolean, and if it is, branch on it and push back the literal
    /// that branching just told you it was; if it is not, do nothing. Either
    /// way the value is unchanged, so the whole thing is the identity.
    ///
    /// The only law here that takes no arguments at all, and the only one that
    /// can put a `branch` on an *unknown* condition into a term.
    ///
    /// Read backward it is a **case split**, and that is the direction that
    /// matters. Every other way of learning something about a value needs the
    /// value to be a literal already; this manufactures the two cases in which
    /// it is one. Inside the inner arms the opaque value has been replaced by
    /// `push true` and `push false`, so [`Rule::Eval`] and [`Rule::FoldBranch`]
    /// can act on what was previously beyond them — the "path condition becomes
    /// a value" move, with no side condition to satisfy.
    ///
    /// The guard is what makes it unconditional. Stating it instead as
    /// `X ; branch { push true } { push false }` = `X` for an `X` that yields a
    /// boolean would need a syntactic predicate over instructions, and would
    /// then decline exactly the interesting cases — a value that arrived by
    /// `pick`, or out of a call. Asking `is_bool` in the term costs a branch
    /// and answers for every value.
    ///
    /// Both sides leave the stack as they found it, but the left needs a value
    /// to look at where the right does not. That asymmetry is the same one
    /// [`Rule::Counit`] has, and `--check` allows it: what a sequence *requires*
    /// may fall, what it *leaves* may not move.
    SplitBool,

    /// `pick d ; drop` = nothing.
    ///
    /// Copying a value and discarding the copy: neither happened. This is the
    /// counit law of the comonoid whose comultiplication is `pick`, and it is
    /// deliberately *not* an instance of [`Rule::Annihilate`] — `pick d` is
    /// `(d+1 -> d+2)`, so that equation would ask for `d+2` drops and answer
    /// with `d+1` of them.
    ///
    /// Together with [`Rule::Annihilate`] this generates the **vacuous** law,
    ///
    /// ```text
    /// pick (n-1)^n ; X ; drop^m  =  nothing        for X : n -> m
    /// ```
    ///
    /// — compute on copies, discard the results, and the originals were never
    /// touched. That is a lemma rather than an axiom: `n` backward counits nest
    /// a run of picks against a run of drops, and one backward annihilation
    /// turns the drops into `X`. Backward it is the only way to introduce work
    /// into a term at all, which is how a cancelling pair gets in beside the
    /// value it will eventually meet. It belongs to the generator, which may
    /// emit the whole derivation as one firing; see
    /// `applier::tests::vacuous_is_derivable_from_annihilate_and_counit`.
    Counit { d: usize },

    /// `pick 0 ; branch { branch { A } { B } ; R } { Q }`
    ///   = `pick 0 ; branch { drop ; A ; R } { Q }`, and the mirror of it.
    ///
    /// **The same value tested twice answers the same.** The condition is a
    /// copy, so an arm of the outer branch already knows which way its own
    /// branch will go: inside the *then* arm the value is truthy and the inner
    /// branch takes `A`, inside the *else* arm it is `false` and the inner
    /// branch takes `D`. The other inner arm cannot run, and goes.
    ///
    /// [`Arm`] says which arm the inner branch is in, so the two readings are
    /// one equation. Firing both — the outer branch has a branch in each arm —
    /// leaves `pick 0 ; branch { drop ; A } { drop ; D }`, which [`Rule::Hoist`]
    /// backwards and [`Rule::CounitUnder`] finish as `branch { A } { D }`.
    ///
    /// ## Why the shape is what it is
    ///
    /// The inner *branch* is not an arbitrary restriction. Inside the then arm
    /// the value is known only to be **truthy**, not what it is — replacing it
    /// with `push true` would be wrong, since `is_int` answers differently on
    /// `42` than on `true`. A branch is the only construct that observes
    /// exactly truthiness, so it is the only thing this can say anything about.
    ///
    /// The else arm knows more: `false` is the unique falsy value, so there the
    /// value is a literal. Stated that way the law would be more general on
    /// that side and would grow the term; this direction shrinks it, which is
    /// what a pass wants.
    ///
    /// ## What is already derivable, and is therefore not this
    ///
    /// When the two inner branches are *the same*, no axiom is needed:
    /// [`Rule::Distribute`] backwards factors the shared inner branch out of
    /// both arms, leaving `branch { } { }` for [`Rule::Annihilate`] at `m = 0`
    /// and then [`Rule::Counit`]. Three steps, no new law. What this adds is
    /// only that the **off-diagonal arms are dead**, which nothing reaches: an
    /// arm cannot see the branch it is inside, and driving it through
    /// [`Rule::SplitBool`] stalls in the same "not a bool" arm that
    /// [`Rule::BoolResult`] does.
    Retest {
        arm: Arm,
        /// The inner branch, whole. [`Rule::check`] holds it to being one.
        inner: Node,
        /// What follows the inner branch in that arm.
        rest: Vec<Node>,
        /// The outer branch's other arm, untouched.
        other: Vec<Node>,
        then_origin: String,
        else_origin: String,
    },

    /// `pick 0 ; dip 1 { drop }` = nothing.
    ///
    /// Copy a value and discard the **original**: the copy is the same value,
    /// so neither happened. [`Rule::Counit`] is the other way round — copy and
    /// discard the *copy* — and the two are the two counit laws of the comonoid
    /// whose comultiplication is `pick`. They come in pairs, and only one of
    /// them was here.
    ///
    /// Only at depth 0. Deeper, `pick d ; dip (d+1) { drop }` is not the
    /// identity at all but a `roll d`: copying to the top and deleting the
    /// original *moves* the value. That is a different law and is not written.
    CounitUnder,

    /// `push c ; pick 0` = `push c ; push c`.
    ///
    /// Copying a constant is pushing it again. It is what makes a refinement
    /// pay: code downstream reads a slot with `pick`, and a `pick` is opaque to
    /// every equation that folds literals, so rewriting it back into a `push`
    /// is what lets [`Rule::Eval`] see two constants and decide.
    CopyConst { c: Value },

    /// `pick d ; pick 0` = `pick d ; dip 1 { pick d }`.
    ///
    /// **Duplication is coassociative.** Making a third copy from the copy and
    /// making it from the original are the same thing, because they are the
    /// same value.
    ///
    /// Neither side is smaller, which is the point: the right-hand side puts a
    /// copy *in a frame*, and a framed computation is one [`Rule::Interchange`]
    /// can carry. A bare `pick` cannot travel, so the copy a later step needs
    /// would otherwise be stranded where it was made.
    CopyAssoc { d: usize },

    /// `pick (n-1)^n ; X ; dip m { X }` = `X ; pick (m-1)^m`, for `X : n -> m`.
    ///
    /// **Copying is natural.** Copy the inputs and run `X` on both the copy and
    /// the original, or run it once and copy the outputs: the same thing, since
    /// `X` applied twice to the same values answers the same twice. Read
    /// forward it is common-subexpression elimination; read backward it is how
    /// a second copy of a computation gets delivered to somewhere that needs
    /// one.
    ///
    /// `pick (n-1)` done `n` times duplicates the top `n` values as a block —
    /// `a b` becomes `a b a b` — and the second application has to run under
    /// the first one's results, which is what the frame is for.
    ///
    /// The law of the comonoid this set already half-describes: [`Rule::Counit`]
    /// is its counit and [`Rule::CopyAssoc`] its coassociativity, and this says
    /// every `X` is a homomorphism for it. [`Rule::CopyConst`] is the case
    /// `X = push c`, and is now a lemma rather than an axiom — the `n = 0`
    /// instance reads `push c ; dip 1 { push c }` = `push c ; pick 0`, and one
    /// [`Rule::Interchange`] and one [`Rule::ElimDip0`] turn the left side into
    /// `push c ; push c`. See
    /// `applier::tests::copy_const_is_derivable_from_copy_nat`, which runs the
    /// derivation rather than asserting the claim.
    ///
    /// ## What it assumes, which nothing else here does
    ///
    /// **Determinism.** Every other equation in this set is sound even for an
    /// `X` that answered differently each time it ran: `annihilate` throws the
    /// answers away, `interchange` reorders computations that cannot see each
    /// other, and the rest never mention an opaque `X` at all. This one is the
    /// exception, and it is the reason the law cannot be derived from the
    /// others rather than merely having resisted derivation — read `X` as a
    /// random oracle and every other equation still holds while this one fails.
    ///
    /// It costs nothing today, because the instruction set is pure and a
    /// sentence of arity `(n -> m)` can only see the `n` values it is given. It
    /// is written down for the same reason the totality precondition is: an
    /// effectful instruction would take this law with it, and nothing else.
    CopyNat { x: Vec<Node>, n: usize, m: usize },

    /// `op ; is_bool` = `op ; drop ; push true`, for an `op` that always leaves
    /// a boolean on top.
    ///
    /// Asking whether a value is a boolean when the instruction that produced
    /// it can only produce booleans. `is_bool ; is_bool` is the case that wants
    /// it, and with [`Rule::Annihilate`] to take the `op ; drop` away it is
    /// `drop ; push true`, which is what one wanted to write in the first
    /// place.
    ///
    /// `op` stays on both sides on purpose, which makes this the smallest thing
    /// that has to be assumed: the existing set does the rest. The law then
    /// covers a *flag* as readily as a predicate — `add` is `(2 -> 2)` and the
    /// flag is what `is_bool` would be asking about, so `add ; is_bool` folds
    /// even though nothing can delete the `add`.
    ///
    /// ## Why it is an axiom
    ///
    /// **A codomain is not something a rewrite can reach.** [`Rule::SplitBool`]
    /// splits a value into the cases where it *is* a boolean, and in the case
    /// where it is not, the value stays opaque — so driving `is_bool ; is_bool`
    /// that way leaves an else arm holding `is_bool` again. That arm is dead,
    /// and its deadness is precisely the fact being sought.
    ///
    /// It is independent rather than merely elusive. Read `is_bool` as
    /// answering `42` for `true`, `true` for `false`, and `false` otherwise:
    /// `split_bool` still holds, since 42 is truthy and the inner branch still
    /// recovers the value, and every other equation is generic in what
    /// `is_bool` means. This law fails there. The gap is that a branch observes
    /// **truthiness**, and `false` is the only falsy value, so being truthy is
    /// strictly weaker than being a boolean.
    ///
    /// So the fact lives on the instruction, as `Instruction::yields_bool`, and
    /// `vm` measures it against the machine the way it measures commutativity.
    BoolResult { op: Instruction },

    /// `tuple n ; untuple n` = `push true`.
    ///
    /// Building a tuple and immediately taking it apart returns the stack to
    /// where it started, and says so: `untuple n` cannot fail on something
    /// `tuple n` just built, so the flag it leaves is a literal `true`, and that
    /// literal is the whole residue of the pair.
    ///
    /// The converse pair `untuple n ; tuple n` is *not* a no-op — it
    /// junk-normalizes and strands a flag — which is why this equation is about
    /// one order and not the other.
    CancelTuple { n: usize },
}

impl Rule {
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Rule::Collapse { .. } => "collapse",
            Rule::ElimDip0 { .. } => "elim_dip0",
            Rule::Interchange { .. } => "interchange",
            Rule::Fuse { .. } => "fuse",
            Rule::Hoist { .. } => "hoist",
            Rule::Distribute { .. } => "distribute",
            Rule::FoldBranch { .. } => "fold_branch",
            Rule::Eval { .. } => "eval",
            Rule::Annihilate { .. } => "annihilate",
            Rule::Commute { .. } => "commute",
            Rule::SplitBool => "split_bool",
            Rule::Counit { .. } => "counit",
            Rule::CounitUnder => "counit_under",
            Rule::Retest { .. } => "retest",
            Rule::CopyConst { .. } => "copy_const",
            Rule::CopyAssoc { .. } => "copy_assoc",
            Rule::CopyNat { .. } => "copy_nat",
            Rule::BoolResult { .. } => "bool_result",
            Rule::CancelTuple { .. } => "cancel_tuple",
        }
    }

    /// Verifies every fact the arguments claim, against the library.
    ///
    /// The applier must run this before generating either side. [`Rule::lhs`]
    /// and [`Rule::rhs`] assume it has passed and will panic rather than
    /// invent a shape if it has not.
    pub(crate) fn check(&self, prog: &Program) -> Result<(), SideCondition> {
        match self {
            Rule::Interchange { x, framed, n, m } => {
                let depth = frame_depth(framed).ok_or_else(|| SideCondition::NotFramed {
                    found: crate::ir::sketch(std::slice::from_ref(framed)),
                })?;
                let actual = claimed_arity(prog, std::slice::from_ref(x), (*n, *m))?;
                if (depth as i64) < actual.1 {
                    return Err(SideCondition::FrameTooShallow {
                        depth,
                        outputs: actual.1,
                    });
                }
                shifted_depth(depth, actual).map(|_| ())
            }
            // One thing only: that the arity the step claims for `x` is the one
            // the library gives. Under the global precondition that is the
            // whole condition — there is no partial or effectful node for a
            // syntactic predicate to exclude.
            Rule::Annihilate { x, n, m } => {
                claimed_arity(prog, x, (*n as i64, *m as i64)).map(|_| ())
            }
            // The same one claim, and the same whole condition. Determinism is
            // the other thing this law rests on, and it is a property of the
            // instruction set rather than of these arguments — there is nothing
            // here to check it against.
            Rule::CopyNat { x, n, m } => claimed_arity(prog, x, (*n as i64, *m as i64)).map(|_| ()),
            // The one thing the arguments claim about themselves: that there is
            // a branch there to collapse. `lhs` and `rhs` both read its arms.
            Rule::Retest { arm, inner, .. } => {
                if matches!(inner, Node::Branch { .. }) {
                    Ok(())
                } else {
                    Err(SideCondition::NotABranch {
                        arm: arm.name(),
                        found: crate::ir::sketch(std::slice::from_ref(inner)),
                    })
                }
            }
            Rule::BoolResult { op } => {
                if op.yields_bool() {
                    Ok(())
                } else {
                    Err(SideCondition::NotBoolResult {
                        op: format!("{}", op),
                    })
                }
            }
            Rule::Commute { op } => {
                if op.commutative() {
                    Ok(())
                } else {
                    Err(SideCondition::NotCommutative {
                        op: format!("{}", op),
                    })
                }
            }
            Rule::Eval { op, inputs } => match eval_op(op, inputs) {
                Some(_) => Ok(()),
                None => Err(SideCondition::NotEvaluable {
                    op: format!("{}", op),
                    operands: inputs.len(),
                }),
            },
            // The rest are schematic in their arguments and hold for every
            // instantiation, so there is nothing to check.
            Rule::Collapse { .. }
            | Rule::ElimDip0 { .. }
            | Rule::Fuse { .. }
            | Rule::Hoist { .. }
            | Rule::Distribute { .. }
            | Rule::FoldBranch { .. }
            | Rule::SplitBool
            | Rule::Counit { .. }
            | Rule::CounitUnder
            | Rule::CopyConst { .. }
            | Rule::CopyAssoc { .. }
            | Rule::CancelTuple { .. } => Ok(()),
        }
    }

    /// The left-hand side. Pure in the arguments; assumes [`Rule::check`].
    pub(crate) fn lhs(&self) -> Vec<Node> {
        match self {
            Rule::Collapse {
                k,
                j,
                a,
                outer,
                inner,
            } => vec![Node::Dip {
                depth: *k,
                origins: outer.clone(),
                body: vec![Node::Dip {
                    depth: *j,
                    origins: inner.clone(),
                    body: a.clone(),
                }],
            }],

            Rule::ElimDip0 { a, origins } => vec![Node::Dip {
                depth: 0,
                origins: origins.clone(),
                body: a.clone(),
            }],

            Rule::Interchange { x, framed, .. } => vec![x.clone(), framed.clone()],

            Rule::Fuse {
                k,
                a,
                b,
                a_origins,
                b_origins,
            } => vec![
                Node::Dip {
                    depth: *k,
                    origins: a_origins.clone(),
                    body: a.clone(),
                },
                Node::Dip {
                    depth: *k,
                    origins: b_origins.clone(),
                    body: b.clone(),
                },
            ],

            Rule::Hoist {
                k,
                x,
                origins,
                then_arm,
                else_arm,
                then_origin,
                else_origin,
            } => vec![
                Node::Dip {
                    depth: k + 1,
                    origins: origins.clone(),
                    body: x.clone(),
                },
                Node::Branch {
                    then_origin: then_origin.clone(),
                    then_body: then_arm.clone(),
                    else_origin: else_origin.clone(),
                    else_body: else_arm.clone(),
                },
            ],

            Rule::Distribute {
                then_arm,
                else_arm,
                suffix,
                then_origin,
                else_origin,
            } => {
                let mut out = vec![Node::Branch {
                    then_origin: then_origin.clone(),
                    then_body: then_arm.clone(),
                    else_origin: else_origin.clone(),
                    else_body: else_arm.clone(),
                }];
                out.extend(suffix.iter().cloned());
                out
            }

            Rule::FoldBranch {
                c,
                then_arm,
                else_arm,
                then_origin,
                else_origin,
            } => vec![
                Node::Op(Instruction::Push(c.clone())),
                Node::Branch {
                    then_origin: then_origin.clone(),
                    then_body: then_arm.clone(),
                    else_origin: else_origin.clone(),
                    else_body: else_arm.clone(),
                },
            ],

            Rule::Eval { op, inputs } => {
                let mut out: Vec<Node> = inputs.iter().cloned().map(push).collect();
                out.push(Node::Op(op.clone()));
                out
            }

            Rule::Annihilate { x, m, .. } => {
                let mut out = x.clone();
                out.extend(std::iter::repeat_n(Node::Op(Instruction::Drop), *m));
                out
            }

            Rule::Commute { op } => {
                vec![Node::Op(Instruction::Roll(1)), Node::Op(op.clone())]
            }

            Rule::SplitBool => vec![
                Node::Op(Instruction::Pick(0)),
                Node::Op(Instruction::IsBool),
                Node::Branch {
                    then_origin: "a bool".to_string(),
                    then_body: vec![Node::Branch {
                        then_origin: "true".to_string(),
                        then_body: vec![push(Value::Bool(true))],
                        else_origin: "false".to_string(),
                        else_body: vec![push(Value::Bool(false))],
                    }],
                    else_origin: "not a bool".to_string(),
                    else_body: Vec::new(),
                },
            ],

            Rule::Counit { d } => {
                vec![Node::Op(Instruction::Pick(*d)), Node::Op(Instruction::Drop)]
            }

            Rule::CounitUnder => vec![
                Node::Op(Instruction::Pick(0)),
                Node::Dip {
                    depth: 1,
                    origins: Vec::new(),
                    body: vec![Node::Op(Instruction::Drop)],
                },
            ],

            Rule::Retest {
                arm,
                inner,
                rest,
                other,
                then_origin,
                else_origin,
            } => {
                let mut held = vec![inner.clone()];
                held.extend(rest.iter().cloned());
                retest_shape(*arm, held, other, then_origin, else_origin)
            }

            Rule::CopyConst { c } => vec![push(c.clone()), Node::Op(Instruction::Pick(0))],

            Rule::CopyAssoc { d } => vec![
                Node::Op(Instruction::Pick(*d)),
                Node::Op(Instruction::Pick(0)),
            ],

            Rule::CopyNat { x, n, m } => {
                let mut out = copy_block(*n);
                out.extend(x.iter().cloned());
                out.push(Node::Dip {
                    depth: *m,
                    origins: Vec::new(),
                    body: x.clone(),
                });
                out
            }

            Rule::BoolResult { op } => vec![Node::Op(op.clone()), Node::Op(Instruction::IsBool)],

            Rule::CancelTuple { n } => vec![
                Node::Op(Instruction::Tuple(*n)),
                Node::Op(Instruction::Untuple(*n)),
            ],
        }
    }

    /// The right-hand side. Pure in the arguments; assumes [`Rule::check`].
    pub(crate) fn rhs(&self) -> Vec<Node> {
        match self {
            Rule::Collapse {
                k,
                j,
                a,
                outer,
                inner,
            } => {
                let mut origins = outer.clone();
                origins.extend(inner.iter().cloned());
                vec![Node::Dip {
                    depth: k + j,
                    origins,
                    body: a.clone(),
                }]
            }

            Rule::ElimDip0 { a, .. } => a.clone(),

            Rule::Interchange { x, framed, n, m } => {
                let depth = frame_depth(framed).expect("check() accepted an unframed node");
                let shifted =
                    shifted_depth(depth, (*n, *m)).expect("check() accepted an unusable depth");
                vec![
                    with_frame_depth(framed, shifted).expect("check() accepted an unframed node"),
                    x.clone(),
                ]
            }

            Rule::Fuse {
                k,
                a,
                b,
                a_origins,
                b_origins,
            } => {
                let mut origins = a_origins.clone();
                origins.extend(b_origins.iter().cloned());
                let mut body = a.clone();
                body.extend(b.iter().cloned());
                vec![Node::Dip {
                    depth: *k,
                    origins,
                    body,
                }]
            }

            Rule::Hoist {
                k,
                x,
                origins,
                then_arm,
                else_arm,
                then_origin,
                else_origin,
            } => {
                let prefixed = |arm: &[Node]| {
                    let mut out = vec![Node::Dip {
                        depth: *k,
                        origins: origins.clone(),
                        body: x.clone(),
                    }];
                    out.extend(arm.iter().cloned());
                    out
                };
                vec![Node::Branch {
                    then_origin: then_origin.clone(),
                    then_body: prefixed(then_arm),
                    else_origin: else_origin.clone(),
                    else_body: prefixed(else_arm),
                }]
            }

            Rule::Distribute {
                then_arm,
                else_arm,
                suffix,
                then_origin,
                else_origin,
            } => {
                let with_suffix = |arm: &[Node]| {
                    let mut out = arm.to_vec();
                    out.extend(suffix.iter().cloned());
                    out
                };
                vec![Node::Branch {
                    then_origin: then_origin.clone(),
                    then_body: with_suffix(then_arm),
                    else_origin: else_origin.clone(),
                    else_body: with_suffix(else_arm),
                }]
            }

            Rule::FoldBranch {
                c,
                then_arm,
                else_arm,
                ..
            } => {
                if c.truthy() {
                    then_arm.clone()
                } else {
                    else_arm.clone()
                }
            }

            Rule::Eval { op, inputs } => eval_op(op, inputs)
                .expect("check() accepted an operator that cannot be folded")
                .into_iter()
                .map(push)
                .collect(),

            Rule::Annihilate { n, .. } => {
                std::iter::repeat_n(Node::Op(Instruction::Drop), *n).collect()
            }

            Rule::Commute { op } => vec![Node::Op(op.clone())],

            Rule::SplitBool | Rule::Counit { .. } | Rule::CounitUnder => Vec::new(),

            Rule::Retest {
                arm,
                inner,
                rest,
                other,
                then_origin,
                else_origin,
            } => {
                let Node::Branch {
                    then_body,
                    else_body,
                    ..
                } = inner
                else {
                    unreachable!("check() accepted something that is not a branch")
                };
                // The arm the outer condition selects. In the then arm the
                // value is truthy, so the inner branch goes then; in the else
                // arm it is `false`, so it goes else.
                let live = match arm {
                    Arm::Then => then_body,
                    Arm::Else => else_body,
                };
                let mut held = vec![Node::Op(Instruction::Drop)];
                held.extend(live.iter().cloned());
                held.extend(rest.iter().cloned());
                retest_shape(*arm, held, other, then_origin, else_origin)
            }

            Rule::CopyConst { c } => vec![push(c.clone()), push(c.clone())],

            Rule::CopyAssoc { d } => vec![
                Node::Op(Instruction::Pick(*d)),
                Node::Dip {
                    depth: 1,
                    origins: Vec::new(),
                    body: vec![Node::Op(Instruction::Pick(*d))],
                },
            ],

            Rule::CopyNat { x, m, .. } => {
                let mut out = x.clone();
                out.extend(copy_block(*m));
                out
            }

            Rule::BoolResult { op } => vec![
                Node::Op(op.clone()),
                Node::Op(Instruction::Drop),
                push(Value::Bool(true)),
            ],

            Rule::CancelTuple { .. } => vec![push(Value::Bool(true))],
        }
    }
}

/// `pick 0 ; branch { .. } { .. }` with `held` in the arm the law names.
///
/// Both sides of [`Rule::Retest`] are this shape and differ only in what the
/// arm holds, which is what makes the equation one law read at two arms rather
/// than two laws that happen to look alike.
fn retest_shape(
    arm: Arm,
    held: Vec<Node>,
    other: &[Node],
    then_origin: &str,
    else_origin: &str,
) -> Vec<Node> {
    let (then_body, else_body) = match arm {
        Arm::Then => (held, other.to_vec()),
        Arm::Else => (other.to_vec(), held),
    };
    vec![
        Node::Op(Instruction::Pick(0)),
        Node::Branch {
            then_origin: then_origin.to_string(),
            then_body,
            else_origin: else_origin.to_string(),
            else_body,
        },
    ]
}

fn push(v: Value) -> Node {
    Node::Op(Instruction::Push(v))
}

/// Duplicates the top `k` values as a block: `pick (k-1)`, `k` times.
///
/// `a b` becomes `a b a b`. Each pick reaches past the copies made so far to
/// the next original, which is why the depth does not change — after `j` of
/// them the next original is still `k-1` down.
pub(crate) fn copy_block(k: usize) -> Vec<Node> {
    match k.checked_sub(1) {
        Some(d) => std::iter::repeat_n(Node::Op(Instruction::Pick(d)), k).collect(),
        // Nothing to copy: a computation that reads nothing needs no inputs
        // duplicated, which is what makes `copy_const` the `n = 0` case.
        None => Vec::new(),
    }
}

/// The arity the library gives `x`, once the step's claim has been held to it.
fn claimed_arity(
    prog: &Program,
    x: &[Node],
    claimed: (i64, i64),
) -> Result<(i64, i64), SideCondition> {
    let actual = full_arity(prog, x).ok_or_else(|| SideCondition::ArityUnknown {
        found: crate::ir::sketch(x),
    })?;
    if actual != claimed {
        return Err(SideCondition::ClaimedArityMismatch { claimed, actual });
    }
    Ok(actual)
}

/// Where a hidden window `depth` deep sits on the other side of an `(n -> m)`.
fn shifted_depth(depth: usize, (n, m): (i64, i64)) -> Result<usize, SideCondition> {
    let shifted = depth as i64 - m + n;
    usize::try_from(shifted).map_err(|_| SideCondition::DepthOverflow { shifted })
}

/// What an operator answers on operands that are already known.
///
/// The obligation is to agree with the interpreter exactly, so `and`/`or` go
/// through [`Value::truthy`] and the comparisons through [`numeric_cmp`],
/// both of which live in `bytecode::value` for precisely this reason.
///
/// A fallible operator answers with its flag as well: `less` on two symbols is
/// not a comparison it can claim to have made, so it leaves `false, false`.
/// `None` means this is not an operator [`Rule::Eval`] can fold, which
/// includes handing one the wrong number of operands.
pub(crate) fn eval_op(inst: &Instruction, inputs: &[Value]) -> Option<Vec<Value>> {
    match (inst, inputs) {
        (Instruction::Equal, [a, b]) => Some(vec![Value::Bool(a == b)]),
        (Instruction::And, [a, b]) => Some(vec![Value::Bool(a.truthy() && b.truthy())]),
        (Instruction::Or, [a, b]) => Some(vec![Value::Bool(a.truthy() || b.truthy())]),
        (Instruction::Greater | Instruction::Less, [a, b]) => {
            let want = match inst {
                Instruction::Greater => std::cmp::Ordering::Greater,
                _ => std::cmp::Ordering::Less,
            };
            // Unordered covers both a non-numeric operand and a NaN: neither is
            // a comparison the instruction can claim to have made.
            Some(match numeric_cmp(a, b) {
                Some(ord) => vec![Value::Bool(ord == want), Value::Bool(true)],
                None => vec![Value::Bool(false), Value::Bool(false)],
            })
        }

        (Instruction::IsInt, [a]) => Some(vec![Value::Bool(matches!(a, Value::Int(_)))]),
        (Instruction::IsBool, [a]) => Some(vec![Value::Bool(matches!(a, Value::Bool(_)))]),
        (Instruction::IsFloat, [a]) => Some(vec![Value::Bool(matches!(a, Value::Float(_)))]),
        (Instruction::IsConstString, [a]) => {
            Some(vec![Value::Bool(matches!(a, Value::ConstString(_)))])
        }
        (Instruction::IsSymbol, [a]) => Some(vec![Value::Bool(matches!(a, Value::Symbol(_)))]),
        (Instruction::IsTuple, [a]) => Some(vec![Value::Bool(matches!(a, Value::Tuple(_)))]),
        (Instruction::Not, [a]) => Some(vec![Value::Bool(!a.truthy())]),
        // One input and two slots, so on a non-tuple it hands the value back
        // rather than inventing a length for it.
        (Instruction::TupleLength, [a]) => Some(match a {
            Value::Tuple(t) => vec![Value::Int(t.len() as i64), Value::Bool(true)],
            other => vec![other.clone(), Value::Bool(false)],
        }),

        _ => None,
    }
}

/// One entry of a rewrite script.
///
/// Two kinds, and the difference is where the equation comes from. A
/// [`Rule`] is a law of the calculus: schematic in its arguments and valid for
/// every instantiation of them. An [`StepKind::Unfold`] is not — that
/// `Call { k, S }` may be replaced by `S`'s body is the axiom the *library*
/// contributes by defining `S`, and it says nothing about any other sentence.
///
/// Keeping them apart is what stops library content from riding inside a
/// script. The applier reads the body from the library itself, so a step names
/// a sentence and never quotes it.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum StepKind {
    Rule(Rule),
    /// `Call { depth, target }` = the body of `target`, spliced.
    ///
    /// Forward is the old `inline`. Backward is *folding*: recognizing a
    /// sentence's body in the tree and contracting it back to a call, a
    /// direction the old rule set had no way to express.
    ///
    /// The cost of unfolding is provenance — a spliced body no longer says
    /// which sentence it came from — which is why nothing unfolds by default.
    Unfold {
        depth: usize,
        target: SentenceIndex,
    },
}

impl StepKind {
    pub(crate) fn name(&self) -> &'static str {
        match self {
            StepKind::Rule(r) => r.name(),
            StepKind::Unfold { .. } => "unfold",
        }
    }
}

/// A rule, a direction, and a place: everything needed to redo one rewrite.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Step {
    pub(crate) kind: StepKind,
    pub(crate) dir: Direction,
    pub(crate) loc: Location,
}

impl std::fmt::Display for Step {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.kind.name(), self.dir.arrow(), self.loc)
    }
}

/// A derivation: the steps that take one program to another.
pub(crate) type Script = Vec<Step>;

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use bytecode::Library;

    fn prog() -> Program<'static> {
        Program::new(Box::leak(Box::new(Library::new())))
    }

    fn op(i: Instruction) -> Node {
        Node::Op(i)
    }

    fn dip(depth: usize, body: Vec<Node>) -> Node {
        Node::Dip {
            depth,
            origins: Vec::new(),
            body,
        }
    }

    fn branch(then_body: Vec<Node>, else_body: Vec<Node>) -> Node {
        Node::Branch {
            then_origin: "then".to_string(),
            then_body,
            else_origin: "else".to_string(),
            else_body,
        }
    }

    /// `n` copies of the top `n` values, in the order they were read.
    ///
    /// Not part of any equation: it is the shape the **vacuous** derivation
    /// builds out of [`Rule::Counit`], and what a generator emitting that
    /// derivation would need to recognize its own handiwork.
    pub(crate) fn copies(n: usize) -> Vec<Node> {
        // The same helper `Rule::CopyNat` builds its sides from, so the shape
        // the vacuous derivation expects and the shape the law states cannot
        // drift apart.
        copy_block(n)
    }

    fn drops(n: usize) -> Vec<Node> {
        std::iter::repeat_n(op(Instruction::Drop), n).collect()
    }

    // -- the frame equations ------------------------------------------------

    #[test]
    fn collapse_adds_the_two_hidden_depths() {
        let r = Rule::Collapse {
            k: 2,
            j: 3,
            a: vec![op(Instruction::Add)],
            outer: Vec::new(),
            inner: Vec::new(),
        };
        assert_eq!(
            r.lhs(),
            vec![dip(2, vec![dip(3, vec![op(Instruction::Add)])])]
        );
        assert_eq!(r.rhs(), vec![dip(5, vec![op(Instruction::Add)])]);
    }

    #[test]
    fn collapse_read_backwards_is_the_old_expand() {
        // `expand` peeled exactly one level: dip 3 { A } becomes
        // dip 1 { dip 2 { A } }. That is this equation at the split (1, 2),
        // with the origins riding inward to the level that holds the body.
        let r = Rule::Collapse {
            k: 1,
            j: 2,
            a: vec![op(Instruction::Add)],
            outer: Vec::new(),
            inner: vec!["#7 s".to_string()],
        };
        assert_eq!(
            r.rhs(),
            vec![Node::Dip {
                depth: 3,
                origins: vec!["#7 s".to_string()],
                body: vec![op(Instruction::Add)],
            }]
        );
        assert_eq!(
            r.lhs(),
            vec![Node::Dip {
                depth: 1,
                origins: Vec::new(),
                body: vec![Node::Dip {
                    depth: 2,
                    origins: vec!["#7 s".to_string()],
                    body: vec![op(Instruction::Add)],
                }],
            }]
        );
    }

    #[test]
    fn elim_dip0_splices_the_body() {
        let r = Rule::ElimDip0 {
            a: vec![op(Instruction::Add), op(Instruction::Drop)],
            origins: Vec::new(),
        };
        assert_eq!(
            r.lhs(),
            vec![dip(0, vec![op(Instruction::Add), op(Instruction::Drop)])]
        );
        assert_eq!(r.rhs(), vec![op(Instruction::Add), op(Instruction::Drop)]);
    }

    #[test]
    fn fuse_concatenates_two_bodies_at_the_same_depth() {
        let r = Rule::Fuse {
            k: 2,
            a: vec![op(Instruction::Add)],
            b: vec![op(Instruction::Drop)],
            a_origins: vec!["a".to_string()],
            b_origins: vec!["b".to_string()],
        };
        assert_eq!(r.lhs().len(), 2);
        assert_eq!(
            r.rhs(),
            vec![Node::Dip {
                depth: 2,
                origins: vec!["a".to_string(), "b".to_string()],
                body: vec![op(Instruction::Add), op(Instruction::Drop)],
            }]
        );
    }

    // -- interchange --------------------------------------------------------

    #[test]
    fn interchange_widens_a_window_past_an_operator_that_consumes_two() {
        // `add` is (2 -> 2), the second output being its success flag: 2 >= 2
        // clears the window, and the same window is 2 - 2 + 2 = 2 deep beyond.
        let r = Rule::Interchange {
            x: op(Instruction::Add),
            framed: dip(2, Vec::new()),
            n: 2,
            m: 2,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.lhs(), vec![op(Instruction::Add), dip(2, Vec::new())]);
        assert_eq!(r.rhs(), vec![dip(2, Vec::new()), op(Instruction::Add)]);
    }

    #[test]
    fn interchange_narrows_a_window_past_a_push() {
        // `push` is (0 -> 1): a window 1 deep clears it and is 0 deep beyond.
        let r = Rule::Interchange {
            x: push(Value::Int(1)),
            framed: dip(1, Vec::new()),
            n: 0,
            m: 1,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.rhs(), vec![dip(0, Vec::new()), push(Value::Int(1))]);
    }

    #[test]
    fn interchange_refuses_a_window_that_would_reach_what_x_produced() {
        let r = Rule::Interchange {
            x: op(Instruction::Add),
            framed: dip(1, Vec::new()),
            n: 2,
            m: 2,
        };
        assert_eq!(
            r.check(&prog()),
            Err(SideCondition::FrameTooShallow {
                depth: 1,
                outputs: 2
            })
        );
    }

    #[test]
    fn interchange_refuses_a_plain_jump_but_takes_a_deeper_call() {
        // `Call { depth: 0 }` is a jump and has no frame at all; a `dip 0`
        // does have one, which hides nothing.
        let jump = Node::Call {
            depth: 0,
            target: SentenceIndex::from(0),
        };
        let r = Rule::Interchange {
            x: push(Value::Int(1)),
            framed: jump,
            n: 0,
            m: 1,
        };
        assert!(matches!(
            r.check(&prog()),
            Err(SideCondition::NotFramed { .. })
        ));

        let called = Node::Call {
            depth: 2,
            target: SentenceIndex::from(0),
        };
        let r = Rule::Interchange {
            x: push(Value::Int(1)),
            framed: called.clone(),
            n: 0,
            m: 1,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(
            r.rhs(),
            vec![
                Node::Call {
                    depth: 1,
                    target: SentenceIndex::from(0)
                },
                push(Value::Int(1))
            ]
        );
        let _ = called;
    }

    #[test]
    fn a_fabricated_arity_is_caught_against_the_library() {
        // Claiming `add` is (1 -> 1) would let the window move where it must
        // not. The library is the authority, and it disagrees.
        let r = Rule::Interchange {
            x: op(Instruction::Add),
            framed: dip(1, Vec::new()),
            n: 1,
            m: 1,
        };
        assert_eq!(
            r.check(&prog()),
            Err(SideCondition::ClaimedArityMismatch {
                claimed: (1, 1),
                actual: (2, 2)
            })
        );
    }

    // -- branch equations ---------------------------------------------------

    fn hoist(k: usize, x: Vec<Node>, then_arm: Vec<Node>, else_arm: Vec<Node>) -> Rule {
        Rule::Hoist {
            k,
            x,
            origins: Vec::new(),
            then_arm,
            else_arm,
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        }
    }

    #[test]
    fn hoist_moves_a_framed_block_into_both_arms_one_shallower() {
        let r = hoist(
            1,
            vec![op(Instruction::Add)],
            vec![op(Instruction::Drop)],
            Vec::new(),
        );
        let Node::Dip { depth, .. } = &r.lhs()[0] else {
            panic!("expected a dip")
        };
        assert_eq!(*depth, 2);
        let [
            Node::Branch {
                then_body,
                else_body,
                ..
            },
        ] = &r.rhs()[..]
        else {
            panic!("expected one branch")
        };
        assert_eq!(then_body[0], dip(1, vec![op(Instruction::Add)]));
        assert_eq!(else_body[0], dip(1, vec![op(Instruction::Add)]));
        assert_eq!(then_body.len(), 2);
        assert_eq!(else_body.len(), 1);
    }

    #[test]
    fn hoist_at_zero_leaves_a_frame_for_elim_dip0_to_clear() {
        // The old `factor_branch` spliced in one motion. Here the frame stays,
        // and removing it is a separate step — which is what makes the whole
        // thing a script of laws rather than one rule with a procedure in it.
        let r = hoist(0, vec![op(Instruction::Add)], Vec::new(), Vec::new());
        let [Node::Branch { then_body, .. }] = &r.rhs()[..] else {
            panic!("expected one branch")
        };
        assert_eq!(then_body[0], dip(0, vec![op(Instruction::Add)]));
    }

    #[test]
    fn distribute_takes_a_whole_suffix_into_both_arms() {
        let r = Rule::Distribute {
            then_arm: vec![op(Instruction::Add)],
            else_arm: Vec::new(),
            suffix: vec![op(Instruction::Drop), op(Instruction::Not)],
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        };
        assert_eq!(r.lhs().len(), 3);
        let [
            Node::Branch {
                then_body,
                else_body,
                ..
            },
        ] = &r.rhs()[..]
        else {
            panic!("expected one branch")
        };
        assert_eq!(then_body.len(), 3);
        assert_eq!(else_body.len(), 2);
    }

    #[test]
    fn fold_branch_decides_by_truthiness_not_by_being_a_bool() {
        let arms = |c: Value| Rule::FoldBranch {
            c,
            then_arm: vec![op(Instruction::Add)],
            else_arm: vec![op(Instruction::Drop)],
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        };
        assert_eq!(arms(Value::Bool(true)).rhs(), vec![op(Instruction::Add)]);
        assert_eq!(arms(Value::Bool(false)).rhs(), vec![op(Instruction::Drop)]);
        // Not a bool at all: `false` is the only falsy value, so the branch
        // takes the *then* arm, and so must this.
        assert_eq!(arms(Value::Int(1)).rhs(), vec![op(Instruction::Add)]);
        assert_eq!(arms(Value::unit()).rhs(), vec![op(Instruction::Add)]);
    }

    // -- values -------------------------------------------------------------

    #[test]
    fn eval_agrees_with_the_interpreter_on_junk() {
        // Neither operand is `Bool(false)`, so both are true and `and` is
        // true — not an error, and not a coercion to false either.
        let r = Rule::Eval {
            op: Instruction::And,
            inputs: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.rhs(), vec![push(Value::Bool(true))]);

        // And one `false` operand is enough to decide it.
        let r = Rule::Eval {
            op: Instruction::And,
            inputs: vec![Value::Int(1), Value::Bool(false)],
        };
        assert_eq!(r.rhs(), vec![push(Value::Bool(false))]);
    }

    #[test]
    fn eval_of_a_fallible_comparison_produces_the_flag_too() {
        let r = Rule::Eval {
            op: Instruction::Less,
            inputs: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            r.rhs(),
            vec![push(Value::Bool(true)), push(Value::Bool(true))]
        );
        // Unordered: not a comparison it can claim to have made.
        let r = Rule::Eval {
            op: Instruction::Less,
            inputs: vec![Value::Bool(true), Value::Int(2)],
        };
        assert_eq!(
            r.rhs(),
            vec![push(Value::Bool(false)), push(Value::Bool(false))]
        );
    }

    #[test]
    fn eval_of_tuple_length_hands_a_non_tuple_back() {
        let r = Rule::Eval {
            op: Instruction::TupleLength,
            inputs: vec![Value::Int(7)],
        };
        assert_eq!(r.rhs(), vec![push(Value::Int(7)), push(Value::Bool(false))]);
    }

    #[test]
    fn eval_refuses_an_operator_it_has_no_answer_for() {
        let r = Rule::Eval {
            op: Instruction::Drop,
            inputs: vec![Value::Int(1)],
        };
        assert!(matches!(
            r.check(&prog()),
            Err(SideCondition::NotEvaluable { .. })
        ));
        // Right operator, wrong number of operands.
        let r = Rule::Eval {
            op: Instruction::And,
            inputs: vec![Value::Int(1)],
        };
        assert!(matches!(
            r.check(&prog()),
            Err(SideCondition::NotEvaluable { .. })
        ));
    }

    #[test]
    fn annihilate_trades_outputs_for_inputs() {
        // `add` is (2 -> 2): two drops after it are two drops before it.
        let r = Rule::Annihilate {
            x: vec![op(Instruction::Add)],
            n: 2,
            m: 2,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.lhs(), {
            let mut v = vec![op(Instruction::Add)];
            v.extend(drops(2));
            v
        });
        assert_eq!(r.rhs(), drops(2));
    }

    #[test]
    fn annihilate_reaches_a_dip_that_the_old_whitelist_refused() {
        // Under the global precondition there is no hidden `assert`, so a
        // framed computation annihilates like any other. `dip 1 { add }` is
        // (3 -> 3).
        let x = dip(1, vec![op(Instruction::Add)]);
        let r = Rule::Annihilate {
            x: vec![x],
            n: 3,
            m: 3,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.rhs(), drops(3));
    }

    #[test]
    fn copies_reach_back_past_the_copies_already_made() {
        // `a b` becomes `a b a b`, not `a b b a` — the shape the vacuous
        // derivation builds.
        assert_eq!(copies(0), Vec::new());
        assert_eq!(copies(1), vec![op(Instruction::Pick(0))]);
        assert_eq!(
            copies(2),
            vec![op(Instruction::Pick(1)), op(Instruction::Pick(1))]
        );
    }

    #[test]
    fn commute_deletes_the_swap_a_commutative_operator_cannot_see() {
        let r = Rule::Commute {
            op: Instruction::Add,
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(
            r.lhs(),
            vec![op(Instruction::Roll(1)), op(Instruction::Add)]
        );
        assert_eq!(r.rhs(), vec![op(Instruction::Add)]);
    }

    #[test]
    fn commute_refuses_an_operator_that_reads_its_operands_in_order() {
        for inst in [
            Instruction::Subtract,
            Instruction::Divide,
            Instruction::Less,
            Instruction::Greater,
            Instruction::Tuple(2),
            // Not binary at all.
            Instruction::Not,
            Instruction::Drop,
        ] {
            let r = Rule::Commute { op: inst.clone() };
            assert!(
                matches!(r.check(&prog()), Err(SideCondition::NotCommutative { .. })),
                "{:?} was accepted as commutative",
                inst
            );
        }
    }

    #[test]
    fn the_commutative_set_is_the_instructions_own_answer() {
        // The list is not restated here: `vm` measures it against the
        // interpreter, and this only checks the equation asks the instruction.
        for inst in [
            Instruction::Add,
            Instruction::Multiply,
            Instruction::And,
            Instruction::Or,
            Instruction::Equal,
        ] {
            assert!(inst.commutative(), "{:?}", inst);
            assert_eq!(Rule::Commute { op: inst }.check(&prog()), Ok(()));
        }
    }

    #[test]
    fn split_bool_is_a_closed_identity() {
        // No arguments, no side conditions, and one side is nothing at all.
        let r = Rule::SplitBool;
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.rhs(), Vec::new());
        assert_eq!(r.lhs().len(), 3);
        assert_eq!(r.lhs()[0], op(Instruction::Pick(0)));
        assert_eq!(r.lhs()[1], op(Instruction::IsBool));

        // The inner arms hold the literals, which is the whole point: after a
        // split the value is something the folding laws can read.
        let [.., Node::Branch { then_body, .. }] = &r.lhs()[..] else {
            panic!("expected a guard branch")
        };
        let [
            Node::Branch {
                then_body: yes,
                else_body: no,
                ..
            },
        ] = &then_body[..]
        else {
            panic!("expected an inner branch")
        };
        assert_eq!(yes, &vec![push(Value::Bool(true))]);
        assert_eq!(no, &vec![push(Value::Bool(false))]);
    }

    #[test]
    fn split_bool_leaves_the_stack_as_it_found_it() {
        // Net change is what must not move; that the left needs a value to
        // look at and the right does not is the same asymmetry `counit` has.
        let prog = prog();
        let r = Rule::SplitBool;
        let (li, lo) = crate::arity::seq_arity(&prog, &r.lhs());
        assert_eq!((li, lo), (1, Some(1)));
        assert_eq!(crate::arity::seq_arity(&prog, &r.rhs()), (0, Some(0)));
    }

    #[test]
    fn counit_is_not_an_annihilation() {
        // `pick d` is (d+1 -> d+2), so the annihilation equation would ask for
        // d+2 drops. The counit law is the one that holds.
        let r = Rule::Counit { d: 3 };
        assert_eq!(
            r.lhs(),
            vec![op(Instruction::Pick(3)), op(Instruction::Drop)]
        );
        assert_eq!(r.rhs(), Vec::new());
    }

    #[test]
    fn copy_assoc_puts_one_copy_in_a_frame() {
        let r = Rule::CopyAssoc { d: 2 };
        assert_eq!(
            r.rhs(),
            vec![
                op(Instruction::Pick(2)),
                dip(1, vec![op(Instruction::Pick(2))])
            ]
        );
    }

    #[test]
    fn copy_nat_copies_the_inputs_on_one_side_and_the_outputs_on_the_other() {
        // `equal` is (2 -> 1): two picks in front on the left, one after on the
        // right, and the second application under a frame one deep.
        let r = Rule::CopyNat {
            x: vec![op(Instruction::Equal)],
            n: 2,
            m: 1,
        };
        assert_eq!(
            r.lhs(),
            vec![
                op(Instruction::Pick(1)),
                op(Instruction::Pick(1)),
                op(Instruction::Equal),
                dip(1, vec![op(Instruction::Equal)]),
            ]
        );
        assert_eq!(
            r.rhs(),
            vec![op(Instruction::Equal), op(Instruction::Pick(0))]
        );
    }

    #[test]
    fn copy_nat_at_no_inputs_is_the_constant_case() {
        // Nothing to copy, and what is left is `copy_const`'s left-hand side —
        // which is what makes that law a lemma of this one. The derivation is
        // in `applier::tests::copy_const_is_derivable_from_copy_nat`.
        let c = Value::Int(7);
        let r = Rule::CopyNat {
            x: vec![push(c.clone())],
            n: 0,
            m: 1,
        };
        assert_eq!(
            r.lhs(),
            vec![push(c.clone()), dip(1, vec![push(c.clone())])]
        );
        assert_eq!(r.rhs(), Rule::CopyConst { c }.lhs());
    }

    #[test]
    fn copy_nat_holds_the_term_to_the_arity_it_claims() {
        // The one fact the arguments assert about the library, and the applier
        // re-derives it however the step came to be written.
        let wrong = Rule::CopyNat {
            x: vec![op(Instruction::Equal)],
            n: 2,
            m: 2,
        };
        assert!(matches!(
            wrong.check(&prog()),
            Err(SideCondition::ClaimedArityMismatch { .. })
        ));
    }

    #[test]
    fn bool_result_keeps_the_operator_and_answers_the_question() {
        // The smallest thing that has to be assumed: `op` stays on both sides,
        // and `annihilate` is what takes it away afterwards.
        let r = Rule::BoolResult {
            op: Instruction::IsBool,
        };
        assert_eq!(
            r.lhs(),
            vec![op(Instruction::IsBool), op(Instruction::IsBool)]
        );
        assert_eq!(
            r.rhs(),
            vec![
                op(Instruction::IsBool),
                op(Instruction::Drop),
                push(Value::Bool(true)),
            ]
        );
    }

    #[test]
    fn bool_result_asks_the_instruction_rather_than_deciding_for_itself() {
        // The fact is `Instruction::yields_bool`, which `vm` measures against
        // the machine. A `tuple n` leaves a tuple, and no amount of wanting it
        // to makes this law apply.
        assert_eq!(
            Rule::BoolResult {
                op: Instruction::Add
            }
            .check(&prog()),
            Ok(()),
            "a flag is a boolean"
        );
        assert!(matches!(
            Rule::BoolResult {
                op: Instruction::Tuple(2)
            }
            .check(&prog()),
            Err(SideCondition::NotBoolResult { .. })
        ));
        // And a literal is `eval`'s business, which answers better than this.
        assert!(
            Rule::BoolResult {
                op: Instruction::Push(Value::Bool(true))
            }
            .check(&prog())
            .is_err()
        );
    }

    #[test]
    fn retest_deletes_the_arm_that_cannot_run() {
        // The then arm's inner branch is entered on a truthy value, so it goes
        // then; what is left of it is the `drop` of the condition it read.
        let inner = || branch(vec![op(Instruction::Not)], vec![op(Instruction::IsBool)]);
        let r = |arm| Rule::Retest {
            arm,
            inner: inner(),
            rest: vec![op(Instruction::Add)],
            other: vec![op(Instruction::Drop)],
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        };

        let held = |nodes: Vec<Node>| nodes;
        assert_eq!(
            r(Arm::Then).lhs(),
            vec![
                op(Instruction::Pick(0)),
                branch(
                    held(vec![inner(), op(Instruction::Add)]),
                    vec![op(Instruction::Drop)]
                ),
            ]
        );
        assert_eq!(
            r(Arm::Then).rhs(),
            vec![
                op(Instruction::Pick(0)),
                branch(
                    held(vec![
                        op(Instruction::Drop),
                        op(Instruction::Not),
                        op(Instruction::Add)
                    ]),
                    vec![op(Instruction::Drop)]
                ),
            ]
        );

        // The else arm reads the other way: there the value is `false`, so the
        // inner branch goes else.
        assert_eq!(
            r(Arm::Else).rhs(),
            vec![
                op(Instruction::Pick(0)),
                branch(
                    vec![op(Instruction::Drop)],
                    held(vec![
                        op(Instruction::Drop),
                        op(Instruction::IsBool),
                        op(Instruction::Add)
                    ])
                ),
            ]
        );
    }

    #[test]
    fn retest_insists_there_is_a_branch_to_collapse() {
        let r = Rule::Retest {
            arm: Arm::Then,
            inner: op(Instruction::Add),
            rest: Vec::new(),
            other: Vec::new(),
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        };
        assert!(matches!(
            r.check(&prog()),
            Err(SideCondition::NotABranch { .. })
        ));
    }

    #[test]
    fn the_two_counits_discard_opposite_copies() {
        // One law each way round, and the set had only one of them.
        assert_eq!(
            Rule::Counit { d: 0 }.lhs(),
            vec![op(Instruction::Pick(0)), op(Instruction::Drop)]
        );
        assert_eq!(
            Rule::CounitUnder.lhs(),
            vec![
                op(Instruction::Pick(0)),
                dip(1, vec![op(Instruction::Drop)])
            ]
        );
        assert_eq!(Rule::CounitUnder.rhs(), Vec::new());
    }

    #[test]
    fn cancel_tuple_leaves_the_flag_behind() {
        let r = Rule::CancelTuple { n: 3 };
        assert_eq!(r.rhs(), vec![push(Value::Bool(true))]);
    }

    // -- properties over the whole set --------------------------------------

    /// One instance of every equation, for the sweeps below.
    fn every_equation() -> Vec<Rule> {
        vec![
            Rule::Collapse {
                k: 2,
                j: 3,
                a: vec![op(Instruction::Add)],
                outer: vec!["o".to_string()],
                inner: vec!["i".to_string()],
            },
            Rule::ElimDip0 {
                a: vec![op(Instruction::Add)],
                origins: vec!["o".to_string()],
            },
            Rule::Interchange {
                x: op(Instruction::Add),
                framed: dip(2, vec![op(Instruction::Drop)]),
                n: 2,
                m: 2,
            },
            Rule::Fuse {
                k: 1,
                a: vec![op(Instruction::Add)],
                b: vec![op(Instruction::Drop)],
                a_origins: vec!["a".to_string()],
                b_origins: vec!["b".to_string()],
            },
            hoist(
                1,
                vec![op(Instruction::Add)],
                vec![op(Instruction::Drop)],
                vec![op(Instruction::Not)],
            ),
            Rule::Distribute {
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Not)],
                suffix: vec![op(Instruction::Drop)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::FoldBranch {
                c: Value::Bool(true),
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Add)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::Eval {
                op: Instruction::And,
                inputs: vec![Value::Bool(true), Value::Bool(false)],
            },
            Rule::Annihilate {
                x: vec![op(Instruction::Add)],
                n: 2,
                m: 2,
            },
            Rule::Commute {
                op: Instruction::Add,
            },
            Rule::SplitBool,
            Rule::Counit { d: 3 },
            Rule::CopyConst { c: Value::Int(7) },
            Rule::CopyAssoc { d: 2 },
            Rule::CopyNat {
                x: vec![op(Instruction::Equal)],
                n: 2,
                m: 1,
            },
            Rule::BoolResult {
                op: Instruction::IsBool,
            },
            Rule::CounitUnder,
            Rule::Retest {
                arm: Arm::Then,
                inner: branch(vec![op(Instruction::Not)], vec![op(Instruction::IsBool)]),
                rest: Vec::new(),
                other: vec![op(Instruction::Drop)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::CancelTuple { n: 3 },
        ]
    }

    #[test]
    fn every_equation_passes_its_own_check() {
        for r in every_equation() {
            assert_eq!(r.check(&prog()), Ok(()), "{} rejected itself", r.name());
        }
    }

    #[test]
    fn every_equation_preserves_net_stack_effect() {
        // The two sides are claimed to behave identically, so they had better
        // agree about how much stack they leave. This is the same property
        // `--check` enforces at every firing, asserted here on the laws
        // themselves rather than on their uses.
        let prog = prog();
        for r in every_equation() {
            let (li, lo) = crate::arity::seq_arity(&prog, &r.lhs());
            let (ri, ro) = crate::arity::seq_arity(&prog, &r.rhs());
            let net = |i: i64, o: Option<i64>| o.map(|o| o - i);
            assert_eq!(
                net(li, lo),
                net(ri, ro),
                "{} changes the net stack effect",
                r.name()
            );
        }
    }

    #[test]
    fn no_equation_is_the_identity() {
        // An equation whose sides coincide could be "applied" forever without
        // changing anything, which is a way for a search not to terminate.
        for r in every_equation() {
            assert_ne!(r.lhs(), r.rhs(), "{} rewrites nothing", r.name());
        }
    }

    #[test]
    fn every_equation_is_named_exactly_once() {
        let mut names: Vec<&str> = every_equation().iter().map(|r| r.name()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "two equations share a name");
        // Every variant of the enum appears in the sweep above. Keeping this
        // number honest is the point: an equation is an axiom, and the set is
        // meant to grow only when something genuinely cannot be derived.
        //
        // Nineteen variants, eighteen axioms: `copy_const` is the constant case
        // of `copy_nat` and is kept only because it is one step where the
        // derivation is three, and `values` and `cleanup` fire it constantly.
        // `applier::tests::copy_const_is_derivable_from_copy_nat` is what says
        // so out loud.
        assert_eq!(before, 19);
    }
}
