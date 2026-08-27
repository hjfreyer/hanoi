//! A goal is two graphs and the claim that they are the same program.
//!
//! The sides used to be terms; they are [`crate::diagram2`] graphs now, so
//! that a proof can *rewrite* them — the tactic language acts on a side in
//! place, and equality-as-stated is [isomorphism](crate::graph::isomorphic)
//! rather than one term twice. The terms are still where a goal comes from:
//! an identity lowers, aligns, and **builds**.
//!
//! The compiler holds an identity to equal **net** change rather than equal
//! arity — `pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`, and every
//! counit reads that way. That asymmetry still lives in exactly one place:
//! here, where the narrower side is padded with
//! [`under`](crate::term::Context::under) until the two arities agree,
//! before either side becomes a graph. Everything downstream is then
//! arity-exact, which is what lets two graphs share one boundary.

use bytecode::{IdentityIndex, Library, SentenceIndex};

use crate::diagram2;
use crate::diagram2::rules::{Step, replay};
use crate::graph::{self, Graph};
use crate::term::{Context, Error, TermIndex, lower};

/// Two graphs of one arity, claimed to be the same program.
#[derive(Debug, Clone, PartialEq)]
pub struct Goal {
    pub lhs: Graph,
    pub rhs: Graph,
}

impl Goal {
    /// The goal an `identity` declaration states.
    ///
    /// Lowers both sides and pads the narrower; the compiler already refused
    /// any identity whose sides differ in net change, so padding always
    /// brings the arities together.
    pub fn of_identity(
        ctx: &mut Context,
        library: &Library,
        idx: IdentityIndex,
    ) -> Result<Goal, Error> {
        let identity = &library.identities[idx];
        let lhs = lower(ctx, library, identity.lhs)?;
        let rhs = lower(ctx, library, identity.rhs)?;
        Ok(Goal::aligned(ctx, lhs, rhs))
    }

    /// Two terms padded to one arity, then built as graphs.
    pub fn aligned(ctx: &mut Context, lhs: TermIndex, rhs: TermIndex) -> Goal {
        let (la, ra) = (ctx.arity(lhs), ctx.arity(rhs));
        let (lhs, rhs) = if la.inputs < ra.inputs {
            (ctx.under(lhs, ra.inputs - la.inputs), rhs)
        } else {
            (lhs, ctx.under(rhs, la.inputs - ra.inputs))
        };
        debug_assert_eq!(
            ctx.arity(lhs),
            ctx.arity(rhs),
            "an identity's sides differ by more than padding, which check_identities refuses"
        );
        Goal {
            lhs: diagram2::build(ctx, lhs),
            rhs: diagram2::build(ctx, rhs),
        }
    }
}

/// Why a proof that spends steps on its right cannot be carried anywhere.
fn right_hand_run(steps: usize) -> String {
    format!(
        "it spends {} step(s) on the right, so it drives the two sides together rather than one \
         onto the other",
        steps
    )
}

/// How a goal was discharged — and **everything needed to check that it
/// was**. A proof is not the prover's word for it: each rewriting variant
/// carries the very [`Step`]s that landed, each definitional variant
/// carries what re-performs it, and [`Proof::check`] walks the tree
/// against the goal as stated, holding every step to
/// [`rules::apply`](crate::diagram2::rules::apply) again and every leaf to
/// [`isomorphic`](graph::isomorphic) again. Finding and checking are
/// different jobs; this is the artifact that keeps them apart.
///
/// [`summary`][Proof::summary] prints it one-line for the per-identity
/// report.
#[derive(Debug)]
pub enum Proof {
    /// The two sides are one graph — isomorphic as they stand.
    Trivial,
    /// A `lhs(…)`, `rhs(…)` or `both(…)` ran a graph tactic; the rewritten
    /// goal closed. The steps each side spent are the record.
    Rewrote {
        side: &'static str,
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        sub: Box<Proof>,
    },
    /// An `inline` opened calls — every one, or the one sentence `target`
    /// names — and the opened goal closed. Deterministic given the target,
    /// so the checker re-performs it rather than trusting a transcript.
    Inlined {
        target: Option<SentenceIndex>,
        name: Option<String>,
        sub: Box<Proof>,
    },
    /// A `symm` swapped the sides, and the swapped goal closed. It records
    /// nothing but itself: the claim either way is the same one.
    Swapped(Box<Proof>),
    /// A `via` cut the goal at the waypoint; each half closed
    /// independently, and the checker rebuilds both halves from the
    /// waypoint the same way the prover did.
    Cut {
        waypoint: TermIndex,
        left_sub: Box<Proof>,
        right_sub: Box<Proof>,
    },
    /// A `cases` expanded a boolean-valued wire — η, spent as the table's
    /// own Shannon law — on each side that held one, and the expanded goal
    /// closed. The per-side records hold the split(s) and, when the step
    /// carried per-case sub-strategies, every step those landed inside the
    /// arms, in order — all ordinary rewrites, replayed blind by the
    /// checker. `splits` and `arms` are presentation only: how many
    /// expansions fired, and how many rewrites each case's sub-strategy
    /// spent (both sides summed), when arms were written.
    Cases {
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        splits: usize,
        arms: Option<(usize, usize)>,
        sub: Box<Proof>,
    },
    /// A `diagram` drove both sides to fixpoint and they were one diagram.
    /// The two drives are the record, and the isomorphism is asked again.
    Diagram { lhs: Vec<Step>, rhs: Vec<Step> },
}

impl Proof {
    /// Re-checks the whole proof against the goal it claims to close.
    ///
    /// Nothing here trusts the prover: recorded steps re-apply through
    /// [`replay`] — every match re-verified port by port — definitional
    /// moves (`inline`, the cut's alignment, the swap) are re-performed
    /// from what the proof names, and every branch of the tree ends in an
    /// [`isomorphic`](graph::isomorphic) that is asked fresh. `Ok(())`
    /// means the claim closes by exactly what the proof says; an `Err`
    /// says where it does not, and a prover that produced one has a bug.
    pub fn check(&self, goal: Goal, ctx: &mut Context, library: &Library) -> Result<(), String> {
        let mut goal = goal;
        match self {
            Proof::Trivial => {
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    Ok(())
                } else {
                    Err("claimed trivial, and the sides are not one graph".to_string())
                }
            }
            Proof::Rewrote { lhs, rhs, sub, .. } | Proof::Cases { lhs, rhs, sub, .. } => {
                replay(&mut goal.lhs, lhs)
                    .map_err(|e| format!("a recorded left step does not re-apply: {}", e))?;
                replay(&mut goal.rhs, rhs)
                    .map_err(|e| format!("a recorded right step does not re-apply: {}", e))?;
                sub.check(goal, ctx, library)
            }
            Proof::Diagram { lhs, rhs } => {
                replay(&mut goal.lhs, lhs)
                    .map_err(|e| format!("a recorded left step does not re-apply: {}", e))?;
                replay(&mut goal.rhs, rhs)
                    .map_err(|e| format!("a recorded right step does not re-apply: {}", e))?;
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    Ok(())
                } else {
                    Err("the recorded drives do not land on one diagram".to_string())
                }
            }
            Proof::Inlined { target, sub, .. } => {
                diagram2::inline(&mut goal.lhs, ctx, library, *target)
                    .map_err(|e| format!("the recorded inline does not re-open: {}", e))?;
                diagram2::inline(&mut goal.rhs, ctx, library, *target)
                    .map_err(|e| format!("the recorded inline does not re-open: {}", e))?;
                sub.check(goal, ctx, library)
            }
            Proof::Swapped(sub) => {
                let swapped = Goal {
                    lhs: goal.rhs,
                    rhs: goal.lhs,
                };
                sub.check(swapped, ctx, library)
            }
            Proof::Cut {
                waypoint,
                left_sub,
                right_sub,
            } => {
                let (lhs, stone) = against(ctx, &goal.lhs, *waypoint);
                left_sub
                    .check(Goal { lhs, rhs: stone }, ctx, library)
                    .map_err(|e| format!("in the left half of the cut: {}", e))?;
                let (rhs, stone) = against(ctx, &goal.rhs, *waypoint);
                right_sub
                    .check(Goal { lhs: stone, rhs }, ctx, library)
                    .map_err(|e| format!("in the right half of the cut: {}", e))
            }
        }
    }

    /// The run this proof spends on the **left side alone**, or why it is
    /// not one.
    ///
    /// What [`transplant`](crate::diagram2::rules::transplant) needs to
    /// carry a proved identity into another goal: a flat list of ordinary
    /// rewrites taking the claim's left side to its right. A proof that
    /// closes by driving the left onto the right is already that list, with
    /// the tree flattened away.
    ///
    /// Not every proof is. Three shapes refuse, each for its own reason, and
    /// the message says which:
    ///
    /// - **A step on the right.** The run would be `A ⟶ M` and `B ⟶ M`
    ///   meeting in the middle, and turning that into `A ⟶ B` means
    ///   inverting the right-hand run and rebasing it through the
    ///   isomorphism the two met at. Nothing here does that yet.
    /// - **`inline` or `via`.** Neither is a rewrite. Opening a call changes
    ///   what is provable and a cut introduces a graph out of nowhere, so
    ///   there is no step list to carry — the honest fix is to state the
    ///   opened or cut form as its own identity.
    /// - **`symm`.** What follows it runs on the other side, so what it
    ///   proves is `B ⟶ A`.
    ///
    /// A lemma written to be reused is written left-only, and this is what
    /// says so when it was not.
    pub fn one_sided(&self) -> Result<Vec<Step>, String> {
        match self {
            Proof::Trivial => Ok(Vec::new()),
            Proof::Rewrote { lhs, rhs, sub, .. } | Proof::Cases { lhs, rhs, sub, .. } => {
                if !rhs.is_empty() {
                    return Err(right_hand_run(rhs.len()));
                }
                let mut run = lhs.clone();
                run.extend(sub.one_sided()?);
                Ok(run)
            }
            Proof::Diagram { lhs, rhs } => {
                if !rhs.is_empty() {
                    return Err(right_hand_run(rhs.len()));
                }
                Ok(lhs.clone())
            }
            Proof::Inlined { .. } => Err(
                "it opens a call, which is not a rewrite: state the opened form as its own \
                 identity and prove that"
                    .to_string(),
            ),
            Proof::Cut { .. } => Err(
                "it cuts at a waypoint, which is not a rewrite: state the waypoint as its own \
                 identity and prove that"
                    .to_string(),
            ),
            Proof::Swapped(_) => {
                Err("it swaps the sides, so what it drives is the right onto the left".to_string())
            }
        }
    }

    /// One line saying how the goal closed, for the per-identity report.
    pub fn summary(&self) -> String {
        match self {
            Proof::Trivial => "the two sides are one graph".to_string(),
            Proof::Rewrote {
                side,
                lhs,
                rhs,
                sub,
            } => format!(
                "{}: {} rewrite(s); {}",
                side,
                lhs.len() + rhs.len(),
                sub.summary()
            ),
            Proof::Inlined { name, sub, .. } => match name {
                None => format!("inline; {}", sub.summary()),
                Some(name) => format!("inline {}; {}", name, sub.summary()),
            },
            Proof::Swapped(sub) => format!("symm; {}", sub.summary()),
            Proof::Cut {
                left_sub,
                right_sub,
                ..
            } => format!(
                "cut (left: {}; right: {})",
                left_sub.summary(),
                right_sub.summary()
            ),
            Proof::Cases {
                splits, arms, sub, ..
            } => match arms {
                None => format!("cases: {} split(s); {}", splits, sub.summary()),
                Some((t, e)) => format!(
                    "cases: {} split(s) (true: {} rewrite(s); false: {} rewrite(s)); {}",
                    splits,
                    t,
                    e,
                    sub.summary()
                ),
            },
            Proof::Diagram { .. } => "the two sides are one diagram".to_string(),
        }
    }
}

/// A goal's side and a waypoint, brought to one arity: the narrower is
/// padded — the term with [`Context::under`] before it builds, the graph
/// with [`graph::under`] — and the waypoint comes back as a graph. Both
/// the prover's `via` and the checker's re-walk of a [`Proof::Cut`] build
/// their halves here, so the two cannot disagree about what a cut means.
pub(crate) fn against(ctx: &mut Context, side: &Graph, waypoint: TermIndex) -> (Graph, Graph) {
    let (ga, wa) = (side.arity(), ctx.arity(waypoint));
    if wa.inputs < ga.inputs {
        let padded = ctx.under(waypoint, ga.inputs - wa.inputs);
        (side.clone(), diagram2::build(ctx, padded))
    } else {
        (
            graph::under(side, wa.inputs - ga.inputs),
            diagram2::build(ctx, waypoint),
        )
    }
}

/// What is left when a goal did not close: what each side became, twice
/// over — as the graphs the tactics left, and as terms narrowed to where
/// the two differ.
///
/// Both, because the two answer different questions. The graphs are what
/// there is to *read*: they are what a step acted on, they carry the boxes
/// a next step would name, and a box's id is stable across a step so two
/// reports of one proof can be compared. The terms are what there is to
/// *write*: a `via` waypoint is a term, so the report hands back one in the
/// language the answer is written in.
///
/// This output is the deliverable of a failed run — it is what says what to
/// try next, so it is kept as data rather than printed on the spot.
#[derive(Debug)]
pub struct Residual {
    /// The two sides as they stand, which is what the report *shows*: a
    /// graph is what the tactics act on, and a box in one has a name that
    /// survives a step, so two of these compare. See
    /// [`render`](crate::diagram2::render).
    pub lhs_graph: Graph,
    pub rhs_graph: Graph,
    /// The same two sides read back as terms, narrowed to the difference.
    /// This is what a stuck goal is *answered* with: a `via` waypoint is
    /// written in the term language, so the report prints one to copy and
    /// edit rather than to translate.
    pub lhs: TermIndex,
    pub rhs: TermIndex,
    /// How the report walked from the goal to the difference: each step of
    /// stripping shared context or entering the one arm that differs.
    pub path: Vec<String>,
    /// Why the step gave up.
    pub stopped: String,
}

/// The answer for one goal.
#[derive(Debug)]
pub enum Outcome {
    Closed(Proof),
    Stuck(Residual),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What a lemma has to be for [`Proof::one_sided`] to answer, and what
    /// each of the three refusals says.
    #[test]
    fn only_a_run_on_one_side_can_be_carried() {
        // Nothing to do at all is a run of no steps.
        assert_eq!(Proof::Trivial.one_sided(), Ok(Vec::new()));

        // A `symm` puts what follows on the other side, so what it drives is
        // the right onto the left.
        let swapped = Proof::Swapped(Box::new(Proof::Trivial));
        assert!(swapped.one_sided().unwrap_err().contains("swaps the sides"));

        // Neither an `inline` nor a `via` is a rewrite, so neither leaves
        // steps to carry.
        let opened = Proof::Inlined {
            target: None,
            name: None,
            sub: Box::new(Proof::Trivial),
        };
        assert!(opened.one_sided().unwrap_err().contains("opens a call"));

        // And a drive that met in the middle is two runs, not one.
        let met = Proof::Diagram {
            lhs: Vec::new(),
            rhs: vec![impossible_step()],
        };
        let why = met.one_sided().unwrap_err();
        assert!(why.contains("1 step(s) on the right"), "{}", why);

        // The right side untouched is the shape a lemma is written in, and
        // the tree flattens to the steps the left spent, in order.
        let left_only = Proof::Rewrote {
            side: "lhs",
            lhs: vec![impossible_step()],
            rhs: Vec::new(),
            sub: Box::new(Proof::Diagram {
                lhs: vec![impossible_step()],
                rhs: Vec::new(),
            }),
        };
        assert_eq!(left_only.one_sided().map(|run| run.len()), Ok(2));
    }

    /// A step whose only job is to be counted — `one_sided` moves steps
    /// around and never reads inside one.
    fn impossible_step() -> Step {
        use crate::diagram2::rules::Rule;
        use crate::graph::{Direction, Match};
        Step {
            rule: Rule::SwapElim,
            dir: Direction::Forward,
            at: Match {
                nodes: Vec::new(),
                inputs: Vec::new(),
                outputs: Vec::new(),
                branches: Vec::new(),
            },
        }
    }
}
