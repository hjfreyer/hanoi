//! A goal is two graphs and the claim that they are the same program, and
//! the kernel's one judgement of a proof of it.
//!
//! The sides are [graphs](crate::kernel::graph), so that a proof can
//! *rewrite* them, and equality-as-stated is
//! [isomorphism](crate::kernel::graph::isomorphic) rather than one program
//! twice.
//!
//! The compiler holds an identity to equal **net** change rather than equal
//! arity — `pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`, and every
//! counit reads that way. That asymmetry lives in exactly one place: here,
//! where the narrower side is padded with [`graph::under`] until the two
//! arities agree. Everything downstream is then arity-exact, which is what
//! lets two graphs share one boundary.
//!
//! A proof, to the kernel, is a **run**: a flat list of [`Step`]s, and
//! [`certify`] is the whole of what is asked of one — replay it on the left
//! side, and ask whether it landed on the right. How the run was found —
//! the tree of goals a strategy carved, what met in the middle, what was
//! cited — is [`crate::proof`]'s account and the kernel never hears it.

use bytecode::{IdentityIndex, Library};

use crate::kernel::graph::{self, Graph};
use crate::kernel::lower::{Error, lower};
use crate::kernel::rules::{self, Rule, Step};

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
    pub fn of_identity(library: &Library, idx: IdentityIndex) -> Result<Goal, Error> {
        let identity = &library.identities[idx];
        let lhs = lower(library, identity.lhs)?;
        let rhs = lower(library, identity.rhs)?;
        Ok(Goal::aligned(lhs, rhs))
    }

    /// Two graphs padded to one arity.
    pub fn aligned(lhs: Graph, rhs: Graph) -> Goal {
        let (la, ra) = (lhs.arity(), rhs.arity());
        let (lhs, rhs) = if la.inputs < ra.inputs {
            (graph::under(&lhs, ra.inputs - la.inputs), rhs)
        } else {
            let k = la.inputs - ra.inputs;
            (lhs, graph::under(&rhs, k))
        };
        debug_assert_eq!(
            lhs.arity(),
            rhs.arity(),
            "an identity's sides differ by more than padding, which check_identities refuses"
        );
        Goal { lhs, rhs }
    }
}

/// Whether `run` takes the goal's left side onto its right.
///
/// This is the kernel's judgement, and all of it. Every step re-applies
/// through [`rules::apply`] — its match re-verified port by port, its two
/// sides rebuilt from its payload — against the left side as the steps
/// before it left it, and the graph that leaves is held to the right side
/// by [`isomorphic`](graph::isomorphic), asked fresh. `Ok(())` means the
/// claim closes by exactly these steps; an `Err` says where it does not,
/// and whoever produced the run has a bug.
///
/// One payload is held to something beyond its own shape. A
/// [`Rule::Open`] carries the body it opens a call to, and a body is what
/// the library says it is: each one is rebuilt from the sentence it names
/// and must be that program, or the step is refused before it is spent.
/// Nothing else in a run refers to anything outside the run.
pub fn certify(goal: &Goal, run: &[Step], library: &Library) -> Result<(), String> {
    let mut lhs = goal.lhs.clone();
    for (i, step) in run.iter().enumerate() {
        if let Rule::Open { target, body } = &step.rule {
            let sentence = lower(library, *target).map_err(|e| {
                format!(
                    "step {}: {} does not lower: {}",
                    i + 1,
                    library.names[*target],
                    e
                )
            })?;
            if *body != sentence {
                return Err(format!(
                    "step {}: opens {} to a body that is not its own",
                    i + 1,
                    library.names[*target]
                ));
            }
        }
        rules::apply(&mut lhs, step)
            .map_err(|e| format!("step {} does not apply: {}", i + 1, e))?;
    }
    if graph::isomorphic(&lhs, &goal.rhs) {
        Ok(())
    } else {
        Err("the run does not land on the right side".to_string())
    }
}
