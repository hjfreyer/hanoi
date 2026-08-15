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

/// How a goal was discharged. Printed with `--explain`; the leaves carry what
/// the e-graph found.
#[derive(Debug)]
pub enum Proof {
    /// The two sides are one term as written.
    Trivial,
    /// A shared prefix and suffix were stripped; the sub-proof answers for
    /// what was left.
    Peel {
        prefix: usize,
        suffix: usize,
        sub: Box<Proof>,
    },
    /// Both sides were branches; each pair of arms is its own claim. `None`
    /// means the arms were equal as written.
    Descend {
        then_sub: Option<Box<Proof>>,
        else_sub: Option<Box<Proof>>,
    },
    /// Every call was unfolded, and the opened goal closed.
    Inlined(Box<Proof>),
    /// Saturation united the two sides.
    Saturated {
        iterations: usize,
        classes: usize,
        explanation: Option<String>,
    },
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
            } => {
                format!("peel {}+{}; {}", prefix, suffix, sub.summary())
            }
            Proof::Descend { then_sub, else_sub } => {
                let arm = |sub: &Option<Box<Proof>>| match sub {
                    None => "as written".to_string(),
                    Some(p) => p.summary(),
                };
                format!("descend (then: {}; else: {})", arm(then_sub), arm(else_sub))
            }
            Proof::Inlined(sub) => format!("inline; {}", sub.summary()),
            Proof::Saturated {
                iterations,
                classes,
                ..
            } => format!("saturated ({} iters, {} classes)", iterations, classes),
        }
    }

    /// Every explanation the proof's leaves carry, outermost first.
    pub fn explanations(&self) -> Vec<&str> {
        match self {
            Proof::Trivial => vec![],
            Proof::Peel { sub, .. } | Proof::Inlined(sub) => sub.explanations(),
            Proof::Descend { then_sub, else_sub } => then_sub
                .iter()
                .chain(else_sub.iter())
                .flat_map(|p| p.explanations())
                .collect(),
            Proof::Saturated { explanation, .. } => explanation.as_deref().into_iter().collect(),
        }
    }
}

/// What is left when a goal did not close: the smallest spelling saturation
/// found for each side, and what the search did on the way.
///
/// This output is the deliverable of a failed run — it is what says what to
/// try next, so it is kept as data rather than printed on the spot.
#[derive(Debug)]
pub struct Residual {
    pub lhs: Term,
    pub rhs: Term,
    /// Rule firings, most active first.
    pub firings: Vec<(String, usize)>,
    /// Why saturation stopped.
    pub stopped: String,
}

/// The answer for one goal.
#[derive(Debug)]
pub enum Outcome {
    Closed(Proof),
    Stuck(Residual),
}
