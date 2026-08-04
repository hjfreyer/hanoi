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
//! the library. The claimed arity of `X` in [`Rule2::Interchange`] is an
//! argument, not a lookup, so `lhs` and `rhs` are pure functions of the
//! arguments. What keeps that honest is [`Rule2::check`], which the applier is
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
//! [`Rule2::Annihilate`] asks only for an arity where `speculable` used to
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
        }
    }
}

/// An equation: two program sequences that always behave identically.
///
/// Each variant states its law in its doc comment as `LHS = RHS`, together with
/// what it takes on faith and what [`Rule2::check`] verifies. Adding one is
/// meant to be rare — a new equation is a new axiom, and everything the search
/// can do is a consequence of these.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Rule2 {
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
    /// how a shared prefix gets wrapped up before [`Rule2::Hoist`] carries it
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
    /// in a frame in each arm with [`Rule2::ElimDip0`] backward, then read this
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

    /// `pick d ; drop` = nothing.
    ///
    /// Copying a value and discarding the copy: neither happened. This is the
    /// counit law of the comonoid whose comultiplication is `pick`, and it is
    /// deliberately *not* an instance of [`Rule2::Annihilate`] — `pick d` is
    /// `(d+1 -> d+2)`, so that equation would ask for `d+2` drops and answer
    /// with `d+1` of them.
    ///
    /// Together with [`Rule2::Annihilate`] this generates the **vacuous** law,
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

    /// `push c ; pick 0` = `push c ; push c`.
    ///
    /// Copying a constant is pushing it again. It is what makes a refinement
    /// pay: code downstream reads a slot with `pick`, and a `pick` is opaque to
    /// every equation that folds literals, so rewriting it back into a `push`
    /// is what lets [`Rule2::Eval`] see two constants and decide.
    CopyConst { c: Value },

    /// `pick d ; pick 0` = `pick d ; dip 1 { pick d }`.
    ///
    /// **Duplication is coassociative.** Making a third copy from the copy and
    /// making it from the original are the same thing, because they are the
    /// same value.
    ///
    /// Neither side is smaller, which is the point: the right-hand side puts a
    /// copy *in a frame*, and a framed computation is one [`Rule2::Interchange`]
    /// can carry. A bare `pick` cannot travel, so the copy a later step needs
    /// would otherwise be stranded where it was made.
    CopyAssoc { d: usize },

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

impl Rule2 {
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Rule2::Collapse { .. } => "collapse",
            Rule2::ElimDip0 { .. } => "elim_dip0",
            Rule2::Interchange { .. } => "interchange",
            Rule2::Fuse { .. } => "fuse",
            Rule2::Hoist { .. } => "hoist",
            Rule2::Distribute { .. } => "distribute",
            Rule2::FoldBranch { .. } => "fold_branch",
            Rule2::Eval { .. } => "eval",
            Rule2::Annihilate { .. } => "annihilate",
            Rule2::Counit { .. } => "counit",
            Rule2::CopyConst { .. } => "copy_const",
            Rule2::CopyAssoc { .. } => "copy_assoc",
            Rule2::CancelTuple { .. } => "cancel_tuple",
        }
    }

    /// Verifies every fact the arguments claim, against the library.
    ///
    /// The applier must run this before generating either side. [`Rule2::lhs`]
    /// and [`Rule2::rhs`] assume it has passed and will panic rather than
    /// invent a shape if it has not.
    pub(crate) fn check(&self, prog: &Program) -> Result<(), SideCondition> {
        match self {
            Rule2::Interchange { x, framed, n, m } => {
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
            Rule2::Annihilate { x, n, m } => {
                claimed_arity(prog, x, (*n as i64, *m as i64)).map(|_| ())
            }
            Rule2::Eval { op, inputs } => match eval_op(op, inputs) {
                Some(_) => Ok(()),
                None => Err(SideCondition::NotEvaluable {
                    op: format!("{}", op),
                    operands: inputs.len(),
                }),
            },
            // The rest are schematic in their arguments and hold for every
            // instantiation, so there is nothing to check.
            Rule2::Collapse { .. }
            | Rule2::ElimDip0 { .. }
            | Rule2::Fuse { .. }
            | Rule2::Hoist { .. }
            | Rule2::Distribute { .. }
            | Rule2::FoldBranch { .. }
            | Rule2::Counit { .. }
            | Rule2::CopyConst { .. }
            | Rule2::CopyAssoc { .. }
            | Rule2::CancelTuple { .. } => Ok(()),
        }
    }

    /// The left-hand side. Pure in the arguments; assumes [`Rule2::check`].
    pub(crate) fn lhs(&self) -> Vec<Node> {
        match self {
            Rule2::Collapse {
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

            Rule2::ElimDip0 { a, origins } => vec![Node::Dip {
                depth: 0,
                origins: origins.clone(),
                body: a.clone(),
            }],

            Rule2::Interchange { x, framed, .. } => vec![x.clone(), framed.clone()],

            Rule2::Fuse {
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

            Rule2::Hoist {
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

            Rule2::Distribute {
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

            Rule2::FoldBranch {
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

            Rule2::Eval { op, inputs } => {
                let mut out: Vec<Node> = inputs.iter().cloned().map(push).collect();
                out.push(Node::Op(op.clone()));
                out
            }

            Rule2::Annihilate { x, m, .. } => {
                let mut out = x.clone();
                out.extend(std::iter::repeat_n(Node::Op(Instruction::Drop), *m));
                out
            }

            Rule2::Counit { d } => {
                vec![Node::Op(Instruction::Pick(*d)), Node::Op(Instruction::Drop)]
            }

            Rule2::CopyConst { c } => vec![push(c.clone()), Node::Op(Instruction::Pick(0))],

            Rule2::CopyAssoc { d } => vec![
                Node::Op(Instruction::Pick(*d)),
                Node::Op(Instruction::Pick(0)),
            ],

            Rule2::CancelTuple { n } => vec![
                Node::Op(Instruction::Tuple(*n)),
                Node::Op(Instruction::Untuple(*n)),
            ],
        }
    }

    /// The right-hand side. Pure in the arguments; assumes [`Rule2::check`].
    pub(crate) fn rhs(&self) -> Vec<Node> {
        match self {
            Rule2::Collapse {
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

            Rule2::ElimDip0 { a, .. } => a.clone(),

            Rule2::Interchange { x, framed, n, m } => {
                let depth = frame_depth(framed).expect("check() accepted an unframed node");
                let shifted =
                    shifted_depth(depth, (*n, *m)).expect("check() accepted an unusable depth");
                vec![
                    with_frame_depth(framed, shifted).expect("check() accepted an unframed node"),
                    x.clone(),
                ]
            }

            Rule2::Fuse {
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

            Rule2::Hoist {
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

            Rule2::Distribute {
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

            Rule2::FoldBranch {
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

            Rule2::Eval { op, inputs } => eval_op(op, inputs)
                .expect("check() accepted an operator that cannot be folded")
                .into_iter()
                .map(push)
                .collect(),

            Rule2::Annihilate { n, .. } => {
                std::iter::repeat_n(Node::Op(Instruction::Drop), *n).collect()
            }

            Rule2::Counit { .. } => Vec::new(),

            Rule2::CopyConst { c } => vec![push(c.clone()), push(c.clone())],

            Rule2::CopyAssoc { d } => vec![
                Node::Op(Instruction::Pick(*d)),
                Node::Dip {
                    depth: 1,
                    origins: Vec::new(),
                    body: vec![Node::Op(Instruction::Pick(*d))],
                },
            ],

            Rule2::CancelTuple { .. } => vec![push(Value::Bool(true))],
        }
    }
}

fn push(v: Value) -> Node {
    Node::Op(Instruction::Push(v))
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
/// `None` means this is not an operator [`Rule2::Eval`] can fold, which
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
/// [`Rule2`] is a law of the calculus: schematic in its arguments and valid for
/// every instantiation of them. An [`StepKind::Unfold`] is not — that
/// `Call { k, S }` may be replaced by `S`'s body is the axiom the *library*
/// contributes by defining `S`, and it says nothing about any other sentence.
///
/// Keeping them apart is what stops library content from riding inside a
/// script. The applier reads the body from the library itself, so a step names
/// a sentence and never quotes it.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum StepKind {
    Rule(Rule2),
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

    /// `n` copies of the top `n` values, in the order they were read.
    ///
    /// Not part of any equation: it is the shape the **vacuous** derivation
    /// builds out of [`Rule2::Counit`], and what a generator emitting that
    /// derivation would need to recognize its own handiwork.
    pub(crate) fn copies(n: usize) -> Vec<Node> {
        let reach = n.saturating_sub(1);
        std::iter::repeat_n(Node::Op(Instruction::Pick(reach)), n).collect()
    }

    fn drops(n: usize) -> Vec<Node> {
        std::iter::repeat_n(op(Instruction::Drop), n).collect()
    }

    // -- the frame equations ------------------------------------------------

    #[test]
    fn collapse_adds_the_two_hidden_depths() {
        let r = Rule2::Collapse {
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
        let r = Rule2::Collapse {
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
        let r = Rule2::ElimDip0 {
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
        let r = Rule2::Fuse {
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
        let r = Rule2::Interchange {
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
        let r = Rule2::Interchange {
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
        let r = Rule2::Interchange {
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
        let r = Rule2::Interchange {
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
        let r = Rule2::Interchange {
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
        let r = Rule2::Interchange {
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

    fn hoist(k: usize, x: Vec<Node>, then_arm: Vec<Node>, else_arm: Vec<Node>) -> Rule2 {
        Rule2::Hoist {
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
        let r = Rule2::Distribute {
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
        let arms = |c: Value| Rule2::FoldBranch {
            c,
            then_arm: vec![op(Instruction::Add)],
            else_arm: vec![op(Instruction::Drop)],
            then_origin: "then".to_string(),
            else_origin: "else".to_string(),
        };
        assert_eq!(arms(Value::Bool(true)).rhs(), vec![op(Instruction::Add)]);
        assert_eq!(arms(Value::Bool(false)).rhs(), vec![op(Instruction::Drop)]);
        // Not a bool at all: the branch takes the else arm, and so must this.
        assert_eq!(arms(Value::Int(1)).rhs(), vec![op(Instruction::Drop)]);
    }

    // -- values -------------------------------------------------------------

    #[test]
    fn eval_agrees_with_the_interpreter_on_junk() {
        // Neither operand is `Bool(true)`, so `and` is false — not an error.
        let r = Rule2::Eval {
            op: Instruction::And,
            inputs: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(r.check(&prog()), Ok(()));
        assert_eq!(r.rhs(), vec![push(Value::Bool(false))]);
    }

    #[test]
    fn eval_of_a_fallible_comparison_produces_the_flag_too() {
        let r = Rule2::Eval {
            op: Instruction::Less,
            inputs: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            r.rhs(),
            vec![push(Value::Bool(true)), push(Value::Bool(true))]
        );
        // Unordered: not a comparison it can claim to have made.
        let r = Rule2::Eval {
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
        let r = Rule2::Eval {
            op: Instruction::TupleLength,
            inputs: vec![Value::Int(7)],
        };
        assert_eq!(r.rhs(), vec![push(Value::Int(7)), push(Value::Bool(false))]);
    }

    #[test]
    fn eval_refuses_an_operator_it_has_no_answer_for() {
        let r = Rule2::Eval {
            op: Instruction::Drop,
            inputs: vec![Value::Int(1)],
        };
        assert!(matches!(
            r.check(&prog()),
            Err(SideCondition::NotEvaluable { .. })
        ));
        // Right operator, wrong number of operands.
        let r = Rule2::Eval {
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
        let r = Rule2::Annihilate {
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
        let r = Rule2::Annihilate {
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
    fn counit_is_not_an_annihilation() {
        // `pick d` is (d+1 -> d+2), so the annihilation equation would ask for
        // d+2 drops. The counit law is the one that holds.
        let r = Rule2::Counit { d: 3 };
        assert_eq!(
            r.lhs(),
            vec![op(Instruction::Pick(3)), op(Instruction::Drop)]
        );
        assert_eq!(r.rhs(), Vec::new());
    }

    #[test]
    fn copy_assoc_puts_one_copy_in_a_frame() {
        let r = Rule2::CopyAssoc { d: 2 };
        assert_eq!(
            r.rhs(),
            vec![
                op(Instruction::Pick(2)),
                dip(1, vec![op(Instruction::Pick(2))])
            ]
        );
    }

    #[test]
    fn cancel_tuple_leaves_the_flag_behind() {
        let r = Rule2::CancelTuple { n: 3 };
        assert_eq!(r.rhs(), vec![push(Value::Bool(true))]);
    }

    // -- properties over the whole set --------------------------------------

    /// One instance of every equation, for the sweeps below.
    fn every_equation() -> Vec<Rule2> {
        vec![
            Rule2::Collapse {
                k: 2,
                j: 3,
                a: vec![op(Instruction::Add)],
                outer: vec!["o".to_string()],
                inner: vec!["i".to_string()],
            },
            Rule2::ElimDip0 {
                a: vec![op(Instruction::Add)],
                origins: vec!["o".to_string()],
            },
            Rule2::Interchange {
                x: op(Instruction::Add),
                framed: dip(2, vec![op(Instruction::Drop)]),
                n: 2,
                m: 2,
            },
            Rule2::Fuse {
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
            Rule2::Distribute {
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Not)],
                suffix: vec![op(Instruction::Drop)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule2::FoldBranch {
                c: Value::Bool(true),
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Add)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule2::Eval {
                op: Instruction::And,
                inputs: vec![Value::Bool(true), Value::Bool(false)],
            },
            Rule2::Annihilate {
                x: vec![op(Instruction::Add)],
                n: 2,
                m: 2,
            },
            Rule2::Counit { d: 3 },
            Rule2::CopyConst { c: Value::Int(7) },
            Rule2::CopyAssoc { d: 2 },
            Rule2::CancelTuple { n: 3 },
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
        assert_eq!(before, 13);
    }
}
