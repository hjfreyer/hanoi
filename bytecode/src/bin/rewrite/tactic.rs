//! Applying rules to a sequence.
//!
//! This is where the search lives, separated from the rules it drives. Stage 0
//! provides only what the flags need — `each`, and a fixpoint over children —
//! but the pieces are the ones a tactic combinator set is built from, and none
//! of the rules know which of them is in use.

use crate::ir::Node;
use crate::rules::Rule;

/// Applies the rules at every position of `nodes`, left to right, until no rule
/// matches anywhere. Returns whether anything fired.
///
/// **The scan discipline lives here and nowhere else.** After a rule splices at
/// window-start `w`, the scan resumes at `w - (width - 1)` rather than moving
/// on. That single rule reproduces all five of the cascades that used to be
/// written out by hand:
///
/// - a width-1 rule resumes at `w`, so it re-applies to its own output —
///   which is how a chain of nested dips collapses in one pass;
/// - a width-2 rule resumes one position earlier, so a dip that just moved
///   left is immediately reconsidered against its new predecessor, giving the
///   leftward cascade for free.
pub(crate) fn each(rules: &[&dyn Rule], nodes: &mut Vec<Node>) -> bool {
    let mut fired = false;
    let mut w = 0usize;

    while w < nodes.len() {
        let mut hit = false;
        for rule in rules {
            let width = rule.width();
            if w + width > nodes.len() {
                continue;
            }
            let Some(replacement) = rule.rewrite(&nodes[w..w + width]) else {
                continue;
            };
            debug_assert!(
                replacement[..] != nodes[w..w + width],
                "rule '{}' returned its input unchanged, which would not terminate",
                rule.name()
            );
            nodes.splice(w..w + width, replacement);
            w = w.saturating_sub(width - 1);
            fired = true;
            hit = true;
            break;
        }
        if !hit {
            w += 1;
        }
    }

    fired
}

/// Applies `f` to every child sequence of every node in `nodes`.
pub(crate) fn children(nodes: &mut [Node], f: &mut dyn FnMut(&mut Vec<Node>) -> bool) -> bool {
    let mut changed = false;
    for node in nodes.iter_mut() {
        changed |= match node {
            Node::Dip { body, .. } => f(body),
            Node::Branch {
                then_body,
                else_body,
                ..
            } => {
                // Both arms, and not short-circuiting: each is rewritten.
                let then_changed = f(then_body);
                let else_changed = f(else_body);
                then_changed || else_changed
            }
            Node::Op(_) | Node::Cut(_) => false,
        };
    }
    changed
}
