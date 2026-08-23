//! A goal is two graphs and the claim that they are the same program.
//!
//! The sides used to be terms; they are [`crate::diagram2`] graphs now, so
//! that a proof can *rewrite* them — the tactic language acts on a side in
//! place, and equality-as-stated is [isomorphism](crate::diagram2::isomorphic)
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

use bytecode::{IdentityIndex, Library};

use crate::diagram2::{self, Graph};
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

/// How a goal was discharged: the shape of the strategy that closed it.
/// Printed one-line by [`summary`][Proof::summary].
#[derive(Debug)]
pub enum Proof {
    /// The two sides are one graph — isomorphic as they stand.
    Trivial,
    /// A `lhs(…)`, `rhs(…)` or `both(…)` ran a graph tactic; the rewritten
    /// goal closed. Records the side and how many rewrites landed.
    Rewrote {
        side: &'static str,
        steps: usize,
        sub: Box<Proof>,
    },
    /// An `inline` opened calls — every one, or the labelled sentence's,
    /// which the summary names — and the opened goal closed.
    Inlined {
        target: Option<String>,
        sub: Box<Proof>,
    },
    /// A `symm` swapped the sides, and the swapped goal closed. It records
    /// nothing but itself: the claim either way is the same one.
    Swapped(Box<Proof>),
    /// A `via` cut the goal at a waypoint; each half closed independently.
    Cut {
        left_sub: Box<Proof>,
        right_sub: Box<Proof>,
    },
    /// A `diagram` read both sides back and normalized them into one arena,
    /// and they were one diagram.
    Diagram,
}

impl Proof {
    /// One line saying how the goal closed, for the per-identity report.
    pub fn summary(&self) -> String {
        match self {
            Proof::Trivial => "the two sides are one graph".to_string(),
            Proof::Rewrote { side, steps, sub } => {
                format!("{}: {} rewrite(s); {}", side, steps, sub.summary())
            }
            Proof::Inlined { target, sub } => match target {
                None => format!("inline; {}", sub.summary()),
                Some(name) => format!("inline {}; {}", name, sub.summary()),
            },
            Proof::Swapped(sub) => format!("symm; {}", sub.summary()),
            Proof::Cut {
                left_sub,
                right_sub,
            } => format!(
                "cut (left: {}; right: {})",
                left_sub.summary(),
                right_sub.summary()
            ),
            Proof::Diagram => "the two sides are one diagram".to_string(),
        }
    }
}

/// What is left when a goal did not close: what each side became — for a
/// failed `diagram`, the two sides reified from their normal forms —
/// narrowed to where the two differ.
///
/// This output is the deliverable of a failed run — it is what says what to
/// try next, so it is kept as data rather than printed on the spot.
#[derive(Debug)]
pub struct Residual {
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
