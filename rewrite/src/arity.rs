//! Stack arities over the tree.
//!
//! Mostly structural, but a [`Node::Call`] names a sentence rather than holding
//! its body, so these take a [`Program`] to look the target up. That is the
//! price of making inlining a rule; the gain is that a recursive call now has
//! an arity where the old `Cut` had none.

use bytecode::arity::op_arity;

use crate::ir::Node;
use crate::program::Program;

/// How many values a node takes off the stack and leaves on it, counted from
/// the top. `None` means the reckoning stops there: a panic runs nothing after
/// it, and a call whose target's arity is unknown tells us nothing about what
/// follows.
pub(crate) fn node_arity(prog: &Program, node: &Node) -> Option<(i64, i64)> {
    match node {
        Node::Op(inst) => op_arity(inst),
        Node::Call { depth, target } => {
            let (n, m) = prog.arity(*target)?;
            let d = *depth as i64;
            Some((d + n, d + m))
        }
        Node::Dip { depth, body, .. } => {
            let (n, m) = full_arity(prog, body)?;
            let d = *depth as i64;
            Some((d + n, d + m))
        }
        Node::Branch {
            then_body,
            else_body,
            ..
        } => branch_arity(prog, then_body, else_body),
    }
}

/// What a branch takes and leaves, from **both** arms.
///
/// The arity checker holds the two arms to the same *net* change and to
/// nothing else, so they may differ in what they require: `{ }` and
/// `{ drop ; push true }` are both net zero and need nought and one. Reading
/// the arity off whichever arm answered first therefore understated it, and
/// understating an arity is a soundness bug rather than an imprecision —
/// `annihilate` asks only for an arity, so a branch that claimed `(1 -> 0)`
/// when it was really `(2 -> 1)` was rewritten into a `drop` that does not
/// mean the same thing. `--check` could not catch it either, since the two
/// readings have the same net change, which is exactly what it compares.
///
/// So the branch requires what the hungrier arm requires, plus the condition,
/// and leaves what that implies. Both arms agree on the answer because they
/// agree on the net.
///
/// An arm whose own reckoning stops — one that reaches a `panic` — answers for
/// neither, and the other arm stands alone: an arm that does not return
/// constrains nothing about what the branch leaves. That is the only case in
/// which one arm decides, and it is unreachable under the tool's precondition,
/// where nothing can panic and nothing recurses. It is kept because the depth
/// gutter is printed for sentences the rewriter would refuse.
///
/// `None` when neither arm answers, or when the two disagree on net change.
/// Neither is reachable from code the arity checker accepted — but an arity
/// that is not known declines a rewrite, where a wrong one performs it.
fn branch_arity(prog: &Program, then_body: &[Node], else_body: &[Node]) -> Option<(i64, i64)> {
    match (full_arity(prog, then_body), full_arity(prog, else_body)) {
        (Some((tn, tm)), Some((en, em))) => {
            if tm - tn != em - en {
                return None;
            }
            let need = tn.max(en);
            Some((need + 1, need + (tm - tn)))
        }
        (Some((n, m)), None) | (None, Some((n, m))) => Some((n + 1, m)),
        (None, None) => None,
    }
}

/// [`seq_arity`] when the whole sequence is statically known, which is what a
/// node's own arity needs — a body that stops partway has no output count.
pub(crate) fn full_arity(prog: &Program, nodes: &[Node]) -> Option<(i64, i64)> {
    let (inputs, outputs) = seq_arity(prog, nodes);
    Some((inputs, outputs?))
}

pub(crate) fn seq_arity(prog: &Program, nodes: &[Node]) -> (i64, Option<i64>) {
    let mut inputs = 0i64;
    let mut size = 0i64;
    for node in nodes {
        let Some((n, m)) = node_arity(prog, node) else {
            return (inputs, None);
        };
        if size < n {
            inputs += n - size;
            size = n;
        }
        size = size - n + m;
    }
    (inputs, Some(size))
}
