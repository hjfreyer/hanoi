//! A goal is two terms and the claim that they are equal.
//!
//! The compiler holds an identity to equal **net** change rather than equal
//! arity — `pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`, and every
//! counit reads that way. In the term model that asymmetry lives in exactly
//! one place: here, where the narrower side is padded with
//! [`under`](crate::term::Term::under) until the two arities agree. Every rule
//! instance downstream is then arity-preserving, which is what lets the
//! e-graph's analysis assert arity on every merge.

use bytecode::{IdentityIndex, Library};

use crate::term::{Error, Term, lower};

/// Two terms of one arity, claimed equal.
#[derive(Debug, Clone)]
pub struct Goal {
    pub lhs: Term,
    pub rhs: Term,
}

impl Goal {
    /// The goal an `identity` declaration states.
    ///
    /// Lowers both sides and pads the narrower; the compiler already refused
    /// any identity whose sides differ in net change, so padding always
    /// brings the arities together.
    pub fn of_identity(library: &Library, idx: IdentityIndex) -> Result<Goal, Error> {
        let identity = &library.identities[idx];
        let lhs = lower(library, identity.lhs)?;
        let rhs = lower(library, identity.rhs)?;
        Ok(Goal::aligned(lhs, rhs))
    }

    /// Two terms padded to one arity.
    pub fn aligned(lhs: Term, rhs: Term) -> Goal {
        let (la, ra) = (lhs.arity(), rhs.arity());
        let (lhs, rhs) = if la.inputs < ra.inputs {
            (lhs.under(ra.inputs - la.inputs), rhs)
        } else {
            (lhs, rhs.under(la.inputs - ra.inputs))
        };
        debug_assert_eq!(
            lhs.arity(),
            rhs.arity(),
            "an identity's sides differ by more than padding, which check_identities refuses"
        );
        Goal { lhs, rhs }
    }
}

/// How a goal was discharged: the shape of the strategy that closed it.
/// Printed one-line by [`summary`][Proof::summary].
#[derive(Debug)]
pub enum Proof {
    /// The two sides are one term as written.
    Trivial,
    /// A `peel` stripped a shared prefix and suffix; the sub-proof answers
    /// for what was left.
    Peel {
        prefix: usize,
        suffix: usize,
        sub: Box<Proof>,
    },
    /// A `descend` forked the arms; `None` is an omitted arm whose sides
    /// were checked equal as written.
    Descend {
        then_sub: Option<Box<Proof>>,
        else_sub: Option<Box<Proof>>,
    },
    /// An `inline` unfolded calls — every one, or the labelled sentence's,
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
    /// A `diagram` normalized both sides into one arena and they were one
    /// diagram.
    Diagram,
}

impl Proof {
    /// One line saying how the goal closed, for the per-identity report.
    pub fn summary(&self) -> String {
        match self {
            Proof::Trivial => "the two sides are one term".to_string(),
            Proof::Peel {
                prefix,
                suffix,
                sub,
            } => format!("peel {}+{}; {}", prefix, suffix, sub.summary()),
            Proof::Descend { then_sub, else_sub } => {
                let arm = |sub: &Option<Box<Proof>>| match sub {
                    None => "as written".to_string(),
                    Some(p) => p.summary(),
                };
                format!("descend (then: {}; else: {})", arm(then_sub), arm(else_sub))
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
    pub lhs: Term,
    pub rhs: Term,
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
