//! The flag-driven driver.
//!
//! Stage 0 keeps the flags and their exact behaviour, but expresses them over
//! [`crate::rules`] and [`crate::tactic`] rather than five hand-written search
//! loops. Replacing this with a real tactic expression is the next step; the
//! shape below is what that expression has to reproduce.

use crate::ir::Node;
use crate::rules::{AnnihilateDrop, Collapse, Expand, FactorBranch, Fuse, Sink};
use crate::tactic::{children, each};

/// Which rewrites to apply. They compose, so each one's output is fed back to
/// the others until nothing more fires.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub(crate) struct Passes {
    pub(crate) dip_normalize: bool,
    pub(crate) factor_branches: bool,
    pub(crate) annihilate: bool,
}

impl Passes {
    pub(crate) fn any(&self) -> bool {
        self.dip_normalize || self.factor_branches || self.annihilate
    }

    pub(crate) fn names(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        if self.annihilate {
            out.push("drops annihilated");
        }
        if self.factor_branches {
            out.push("branch prefixes factored out");
        }
        if self.dip_normalize {
            out.push("dips moved left, fused, and split into unary dips");
        }
        out
    }
}

/// Applies the enabled rewrites, and everything they make possible, to a
/// fixpoint over the whole subtree.
///
/// Written out as a tactic this is
///
/// ```text
/// repeat( children(self)
///       ; try(each(annihilate_drop))
///       ; try(each(factor_branch))
///       ; try(each(collapse)); try(each(sink)); try(each(fuse)) )
/// ```
///
/// The rules are run as separate whole-sequence passes in a fixed order rather
/// than interleaved per position. That ordering is load-bearing for now:
/// `sink` and `fuse` are not known to be confluent, since a dip has an arity
/// and so may sink past another dip.
pub(crate) fn rewrite(nodes: &mut Vec<Node>, passes: Passes) -> bool {
    let mut ever_changed = false;
    loop {
        // Innermost first, so an inner rewrite is already settled by the time
        // an outer one asks for its arity.
        let mut changed = children(nodes, &mut |body| rewrite(body, passes));

        if passes.annihilate {
            changed |= each(&[&AnnihilateDrop], nodes);
        }
        if passes.factor_branches {
            changed |= each(&[&FactorBranch], nodes);
        }
        if passes.dip_normalize {
            changed |= each(&[&Collapse], nodes);
            changed |= each(&[&Sink], nodes);
            changed |= each(&[&Fuse], nodes);
        }

        if !changed {
            return ever_changed;
        }
        ever_changed = true;
    }
}

/// Rewrites every `dip k` with `k >= 2` into `k` nested `dip 1`s.
///
/// Deliberately outside [`rewrite`]'s fixpoint: `Expand` is `Collapse` run
/// backwards, and the two together do not terminate. Unary form is how the
/// result is presented, not how it is reasoned about.
pub(crate) fn expand_to_unary_dips(nodes: &mut Vec<Node>) {
    // Peeling one level at a time exposes another dip inside, so the descent
    // has to be repeated rather than done once.
    while children(nodes, &mut |body| {
        expand_to_unary_dips(body);
        false
    }) || each(&[&Expand], nodes)
    {}
}
