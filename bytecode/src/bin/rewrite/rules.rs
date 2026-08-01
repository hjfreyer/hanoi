//! The rewrite rules.
//!
//! Every rule is a **local splice on a window of at most two nodes**, expressed
//! as a pure function on a read-only slice. It either matches and returns the
//! replacement, or fails. It cannot mutate, cannot see the rest of the
//! sequence, and cannot see where in the tree it is being applied.
//!
//! That uniformity is the point. The search — scanning positions, cascading
//! after a hit, recursing into children, iterating to a fixpoint — belongs to
//! whatever drives the rules, and is written once in [`crate::tactic`] rather
//! than open-coded inside each of them.

use bytecode::Instruction;

use crate::arity::node_arity;
use crate::ir::{same_effect, Node};

/// A local rewrite.
///
/// Implementors must guarantee that firing strictly decreases some measure of
/// the term, since that is the only reason a fixpoint over them terminates.
/// Each states its own below.
pub(crate) trait Rule: Sync {
    fn name(&self) -> &'static str;

    /// How many adjacent nodes the rule matches on. The driver only ever hands
    /// `rewrite` a window of exactly this length.
    fn width(&self) -> usize;

    /// Rewrites the window, or fails. Must not return the window unchanged.
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>>;
}

// ---------------------------------------------------------------------------

/// `dip k { dip j { B } }` becomes `dip (k + j) { B }`.
///
/// Hiding k and then hiding j more of what is left is hiding k + j, so a dip
/// whose whole body is another dip is a nesting level that says nothing. This
/// is what lets an inner dip keep sinking after its wrapper has moved.
///
/// [`Expand`] runs this backwards, and the two are not in conflict: the
/// interchange rule tests a dip's *total* hidden depth, so a search meaning to
/// sink dips has to work on collapsed ones or it gives up reach it is entitled
/// to. Unary form is for presentation. Putting both in one fixpoint oscillates,
/// which is a thing the tactics language lets you write and the fuel budget
/// lets you diagnose.
///
/// Measure: node count.
pub(crate) struct Collapse;

impl Rule for Collapse {
    fn name(&self) -> &'static str {
        "collapse"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Dip {
            depth,
            origins,
            body,
        } = &window[0]
        else {
            return None;
        };
        let [Node::Dip {
            depth: inner_depth,
            origins: inner_origins,
            body: inner_body,
        }] = &body[..]
        else {
            return None;
        };

        let mut origins = origins.clone();
        origins.extend(inner_origins.iter().cloned());
        Some(vec![Node::Dip {
            depth: depth + inner_depth,
            origins,
            body: inner_body.clone(),
        }])
    }
}

/// `dip k { B }` becomes `dip 1 { dip (k-1) { B } }`, for `k >= 2`.
///
/// The inverse of [`Collapse`], peeling one level at a time; driven to a
/// fixpoint it writes a hidden region in unary, one level per hidden value,
/// which is the classic `dip` combinator. The origins ride inward so the
/// arrow ends up on the level that actually holds the body.
///
/// `dip 0` is left alone — it hides nothing and is a plain call.
///
/// Measure: none. This rule *increases* the node count and is the one rule
/// that must not share a fixpoint with its inverse.
pub(crate) struct Expand;

impl Rule for Expand {
    fn name(&self) -> &'static str {
        "expand"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Dip {
            depth,
            origins,
            body,
        } = &window[0]
        else {
            return None;
        };
        if *depth < 2 {
            return None;
        }
        Some(vec![Node::Dip {
            depth: 1,
            origins: Vec::new(),
            body: vec![Node::Dip {
                depth: depth - 1,
                origins: origins.clone(),
                body: body.clone(),
            }],
        }])
    }
}

/// `branch { X A } { X B }` becomes `dip 1 { X }; branch { A } { B }`.
///
/// X runs the same way whichever arm is taken, so it can run before the
/// condition is consumed — but only under a dip, because at that point the
/// condition is still sitting on top of the stack and X must not be handed it.
///
/// Takes the whole shared run at once. Arms are compared by
/// [`same_effect`][crate::ir::same_effect], not by `PartialEq`, so that two
/// identical blocks compiled to different sentences still count as shared.
///
/// Measure: nodes held inside branch arms.
pub(crate) struct FactorBranch;

impl Rule for FactorBranch {
    fn name(&self) -> &'static str {
        "factor_branch"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = &window[0]
        else {
            return None;
        };

        let shared = then_body
            .iter()
            .zip(else_body)
            .take_while(|(a, b)| same_effect(a, b))
            .count();
        if shared == 0 {
            return None;
        }

        Some(vec![
            Node::Dip {
                depth: 1,
                origins: Vec::new(),
                body: then_body[..shared].to_vec(),
            },
            Node::Branch {
                then_origin: then_origin.clone(),
                then_body: then_body[shared..].to_vec(),
                else_origin: else_origin.clone(),
                else_body: else_body[shared..].to_vec(),
            },
        ])
    }
}

/// `X ; dip k { S }` becomes `dip (k - m + n) { S } ; X`, where X has arity
/// `(n -> m)` and `k >= m`.
///
/// The dip's window has to sit entirely below everything X leaves behind —
/// that is `k >= m` — and the same window is `k - m + n` deep on the other side
/// of it. One rule covers every X: push (0→1), drop (1→0), arithmetic (2→1),
/// `pick d` (d+1→d+2), `roll d` (d+1→d+1), and a nested dip alike.
///
/// Measure: the summed positions of dips.
pub(crate) struct Sink;

impl Rule for Sink {
    fn name(&self) -> &'static str {
        "sink"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [prev, dip] = window else { return None };
        let Node::Dip {
            depth,
            origins,
            body,
        } = dip
        else {
            return None;
        };

        let (n, m) = node_arity(prev)?;
        let k = *depth as i64;
        if k < m {
            return None;
        }
        // The arity table keeps this non-negative, but do not trust it blindly.
        let shifted = usize::try_from(k - m + n).ok()?;

        Some(vec![
            Node::Dip {
                depth: shifted,
                origins: origins.clone(),
                body: body.clone(),
            },
            prev.clone(),
        ])
    }
}

/// `dip k { A }; dip k { B }` becomes `dip k { A B }`.
///
/// The second hides exactly what the first restored, so the region can just
/// stay hidden across both.
///
/// Measure: node count.
pub(crate) struct Fuse;

impl Rule for Fuse {
    fn name(&self) -> &'static str {
        "fuse"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [
            Node::Dip {
                depth: da,
                origins: oa,
                body: ba,
            },
            Node::Dip {
                depth: db,
                origins: ob,
                body: bb,
            },
        ] = window
        else {
            return None;
        };
        if da != db {
            return None;
        }

        let mut origins = oa.clone();
        origins.extend(ob.iter().cloned());
        let mut body = ba.clone();
        body.extend(bb.iter().cloned());

        Some(vec![Node::Dip {
            depth: *da,
            origins,
            body,
        }])
    }
}

/// Cancels a drop against the instruction that produced the value it drops.
///
/// Only instructions that cannot panic qualify. `add` also leaves one value on
/// top, but `add; drop` is not `drop; drop` — the add still rejects non-numeric
/// operands, and cancelling it would throw that check away. `equal` is total in
/// the VM but the Z3 model gives it a panic branch, so it is excluded too
/// rather than have this tool assert an equivalence the verifier would not.
///
/// Measure: node count.
pub(crate) struct AnnihilateDrop;

/// What cancelling a `drop` against the instruction before it leaves behind.
enum Annihilation {
    /// Both go: the predecessor produced exactly what was dropped.
    Both,
    /// Only the predecessor goes: it consumed a value to make the dropped one,
    /// so the drop stays and takes its input instead.
    Predecessor,
}

impl Rule for AnnihilateDrop {
    fn name(&self) -> &'static str {
        "annihilate_drop"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Op(prev), Node::Op(Instruction::Drop)] = window else {
            return None;
        };
        match annihilation(prev)? {
            Annihilation::Both => Some(Vec::new()),
            Annihilation::Predecessor => Some(vec![Node::Op(Instruction::Drop)]),
        }
    }
}

fn annihilation(inst: &Instruction) -> Option<Annihilation> {
    match inst {
        // Neither can fail once the arity checker has passed, and each leaves
        // exactly the value the drop removes.
        Instruction::Push(_) | Instruction::Pick(_) => Some(Annihilation::Both),
        // Total, but each consumes a value to produce the dropped one.
        Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
        | Instruction::IsSymbol
        | Instruction::IsTuple => Some(Annihilation::Predecessor),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::Value;

    fn op(i: Instruction) -> Node {
        Node::Op(i)
    }

    fn dip(depth: usize, body: Vec<Node>) -> Node {
        Node::Dip {
            depth,
            origins: Vec::new(),
            body,
        }
    }

    fn branch(then_body: Vec<Node>, else_body: Vec<Node>) -> Node {
        Node::Branch {
            then_origin: "then".to_string(),
            then_body,
            else_origin: "else".to_string(),
            else_body,
        }
    }

    #[test]
    fn collapse_merges_a_dip_whose_body_is_one_dip() {
        let w = [dip(2, vec![dip(3, vec![op(Instruction::Add)])])];
        assert_eq!(
            Collapse.rewrite(&w),
            Some(vec![dip(5, vec![op(Instruction::Add)])])
        );
    }

    #[test]
    fn collapse_declines_a_body_that_is_more_than_one_dip() {
        let w = [dip(2, vec![dip(1, vec![]), op(Instruction::Add)])];
        assert_eq!(Collapse.rewrite(&w), None);
    }

    #[test]
    fn expand_peels_exactly_one_level() {
        let w = [dip(3, vec![op(Instruction::Add)])];
        assert_eq!(
            Expand.rewrite(&w),
            Some(vec![dip(1, vec![dip(2, vec![op(Instruction::Add)])])])
        );
    }

    #[test]
    fn expand_leaves_a_plain_call_and_a_unary_dip_alone() {
        assert_eq!(Expand.rewrite(&[dip(0, vec![])]), None);
        assert_eq!(Expand.rewrite(&[dip(1, vec![])]), None);
    }

    #[test]
    fn sink_widens_past_an_operator_that_consumes_two() {
        // `add` is (2 -> 1): 1 >= 1 clears the window, and the same window is
        // 1 - 1 + 2 = 2 deep on the other side.
        let w = [op(Instruction::Add), dip(1, vec![])];
        assert_eq!(
            Sink.rewrite(&w),
            Some(vec![dip(2, vec![]), op(Instruction::Add)])
        );
    }

    #[test]
    fn sink_narrows_past_a_push() {
        // `push` is (0 -> 1), so the dip loses the value it was hiding.
        let w = [op(Instruction::Push(Value::Int(1))), dip(1, vec![])];
        assert_eq!(
            Sink.rewrite(&w),
            Some(vec![dip(0, vec![]), op(Instruction::Push(Value::Int(1)))])
        );
    }

    #[test]
    fn sink_declines_when_the_window_would_reach_what_prev_produced() {
        // `untuple 3` is (1 -> 3); a dip hiding only two would be rewriting a
        // slot the untuple just filled.
        assert_eq!(
            Sink.rewrite(&[op(Instruction::Untuple(3)), dip(2, vec![])]),
            None
        );
        // Hiding three clears it, and the window is 3 - 3 + 1 = 1 deep before.
        assert_eq!(
            Sink.rewrite(&[op(Instruction::Untuple(3)), dip(3, vec![])]),
            Some(vec![dip(1, vec![]), op(Instruction::Untuple(3))])
        );
    }

    #[test]
    fn sink_declines_past_a_panic() {
        // Nothing after a panic runs, so there is no interchange to make.
        assert_eq!(Sink.rewrite(&[op(Instruction::Panic), dip(9, vec![])]), None);
    }

    #[test]
    fn fuse_joins_dips_at_equal_depth_and_declines_otherwise() {
        let a = dip(2, vec![op(Instruction::Add)]);
        let b = dip(2, vec![op(Instruction::Drop)]);
        assert_eq!(
            Fuse.rewrite(&[a, b]),
            Some(vec![dip(
                2,
                vec![op(Instruction::Add), op(Instruction::Drop)]
            )])
        );
        assert_eq!(Fuse.rewrite(&[dip(1, vec![]), dip(2, vec![])]), None);
    }

    #[test]
    fn factor_branch_hoists_the_shared_prefix_under_a_dip() {
        let shared = op(Instruction::Push(Value::Int(7)));
        let w = [branch(
            vec![shared.clone(), op(Instruction::Push(Value::Int(1)))],
            vec![shared.clone(), op(Instruction::Push(Value::Int(2)))],
        )];
        assert_eq!(
            FactorBranch.rewrite(&w),
            Some(vec![
                dip(1, vec![shared]),
                branch(
                    vec![op(Instruction::Push(Value::Int(1)))],
                    vec![op(Instruction::Push(Value::Int(2)))],
                ),
            ])
        );
    }

    #[test]
    fn factor_branch_declines_when_the_arms_diverge_immediately() {
        let w = [branch(
            vec![op(Instruction::Push(Value::Int(1)))],
            vec![op(Instruction::Push(Value::Int(2)))],
        )];
        assert_eq!(FactorBranch.rewrite(&w), None);
    }

    #[test]
    fn annihilate_cancels_a_total_producer_against_its_drop() {
        assert_eq!(
            AnnihilateDrop.rewrite(&[
                op(Instruction::Push(Value::Int(1))),
                op(Instruction::Drop)
            ]),
            Some(vec![])
        );
        assert_eq!(
            AnnihilateDrop.rewrite(&[op(Instruction::Pick(3)), op(Instruction::Drop)]),
            Some(vec![])
        );
    }

    #[test]
    fn annihilate_leaves_the_drop_behind_for_a_type_test() {
        // `is_int` consumes a value to make the dropped one, so the drop still
        // has to happen — it just takes the input instead.
        assert_eq!(
            AnnihilateDrop.rewrite(&[op(Instruction::IsInt), op(Instruction::Drop)]),
            Some(vec![op(Instruction::Drop)])
        );
    }

    #[test]
    fn annihilate_declines_a_partial_producer() {
        // `add; drop` is not `drop; drop`: the add still rejects non-numeric
        // operands, and cancelling it would discard that check.
        assert_eq!(
            AnnihilateDrop.rewrite(&[op(Instruction::Add), op(Instruction::Drop)]),
            None
        );
        // `equal` is total in the VM, but the Z3 model gives it a panic branch,
        // so the tool does not assert an equivalence the verifier would not.
        assert_eq!(
            AnnihilateDrop.rewrite(&[op(Instruction::Equal), op(Instruction::Drop)]),
            None
        );
    }
}
