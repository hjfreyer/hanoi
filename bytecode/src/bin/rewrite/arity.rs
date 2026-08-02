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
        } => {
            // The arity checker requires both arms to agree on net change, so
            // whichever arm is statically known answers for both. The extra
            // input is the condition.
            let (n, m) =
                full_arity(prog, then_body).or_else(|| full_arity(prog, else_body))?;
            Some((n + 1, m))
        }
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
