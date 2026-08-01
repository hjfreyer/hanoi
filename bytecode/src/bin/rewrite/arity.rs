//! Stack arities, computed structurally over the tree.

use bytecode::arity::op_arity;

use crate::ir::Node;


/// How many values a node takes off the stack and leaves on it, counted from
/// the top. `None` means the node ends or breaks the static reckoning: a panic
/// runs nothing after it, and a cut edge's body was never expanded.
pub(crate) fn node_arity(node: &Node) -> Option<(i64, i64)> {
    match node {
        Node::Op(inst) => op_arity(inst),
        Node::Dip { depth, body, .. } => {
            let (n, m) = full_arity(body)?;
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
            let (n, m) = full_arity(then_body).or_else(|| full_arity(else_body))?;
            Some((n + 1, m))
        }
        Node::Cut(_) => None,
    }
}

/// [`seq_arity`] when the whole sequence is statically known, which is what a
/// node's own arity needs — a body that stops partway has no output count.
pub(crate) fn full_arity(nodes: &[Node]) -> Option<(i64, i64)> {
    let (inputs, outputs) = seq_arity(nodes);
    Some((inputs, outputs?))
}

pub(crate) fn seq_arity(nodes: &[Node]) -> (i64, Option<i64>) {
    let mut inputs = 0i64;
    let mut size = 0i64;
    for node in nodes {
        let Some((n, m)) = node_arity(node) else {
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

