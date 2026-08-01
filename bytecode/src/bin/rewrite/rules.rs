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

use bytecode::{Instruction, Value};

use crate::arity::node_arity;
use crate::ir::{same_effect, Node};

/// A local rewrite.
///
/// Implementors must guarantee that firing strictly decreases some measure of
/// the term, since that is the only reason a fixpoint over them terminates.
/// Each states its own below.
pub(crate) trait Rule: Sync + std::fmt::Debug {
    fn name(&self) -> &'static str;

    /// How many adjacent nodes the rule matches on. The driver only ever hands
    /// `rewrite` a window of exactly this length.
    fn width(&self) -> usize;

    /// Rewrites the window, or fails. Must not return the window unchanged.
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>>;
}

/// Every rule, by name. Rules are a fixed instruction set in their own
/// namespace: a tactic expression can order and place them, but cannot alias
/// or define one.
pub(crate) const ALL_RULES: &[&dyn Rule] = &[
    &AnnihilateDrop,
    &Collapse,
    &Expand,
    &DistributeBranch,
    &FactorBranch,
    &FlattenCall,
    &FoldBranch,
    &Fuse,
    &NoOp,
    &PickDropToRoll,
    &Sink,
];

pub(crate) fn rule_by_name(name: &str) -> Option<&'static dyn Rule> {
    ALL_RULES.iter().copied().find(|r| r.name() == name)
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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
#[derive(Debug)]
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

/// `branch { A } { B } ; X` becomes `branch { A X } { B X }`.
///
/// X runs after whichever arm was taken, so moving it inside both is no change
/// at all. The point is to put X somewhere a rule can see it in context: a
/// simplification that only holds on one side of the branch cannot fire while
/// X sits outside.
///
/// The inverse of [`FactorBranch`] in spirit but not in fact — that one hoists
/// a shared *prefix* out of the front, this one pushes a *suffix* in at the
/// back, so the two do not undo each other. They meet only when both arms are
/// empty, and there they converge rather than oscillate.
///
/// Measure: nodes following a branch in the same sequence. Node count *grows*,
/// so this rule does not belong in a fixpoint that assumes otherwise.
#[derive(Debug)]
pub(crate) struct DistributeBranch;

impl Rule for DistributeBranch {
    fn name(&self) -> &'static str {
        "distribute_branch"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
            next,
        ] = window
        else {
            return None;
        };

        let mut then_body = then_body.clone();
        then_body.push(next.clone());
        let mut else_body = else_body.clone();
        else_body.push(next.clone());

        Some(vec![Node::Branch {
            then_origin: then_origin.clone(),
            then_body,
            else_origin: else_origin.clone(),
            else_body,
        }])
    }
}

/// `push true ; branch { A } { B }` becomes `A`, and `push false` takes `B`.
///
/// Only a literal `Bool` counts. The VM rejects a non-boolean condition, so
/// folding `push 1 ; branch …` would erase a panic rather than preserve one —
/// which is the same reason [`AnnihilateDrop`] will not touch `add`.
///
/// Measure: branch count. The node count can grow, since the chosen arm may be
/// longer than the two nodes it replaces, but a branch is gone for good.
#[derive(Debug)]
pub(crate) struct FoldBranch;

impl Rule for FoldBranch {
    fn name(&self) -> &'static str {
        "fold_branch"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [
            Node::Op(Instruction::Push(Value::Bool(cond))),
            Node::Branch {
                then_body,
                else_body,
                ..
            },
        ] = window
        else {
            return None;
        };
        Some(if *cond {
            then_body.clone()
        } else {
            else_body.clone()
        })
    }
}

/// `dip 0 { P }` becomes `P`, spliced into the enclosing sequence.
///
/// A plain call hides nothing, so its body runs on exactly the stack the call
/// site had; the frame is bookkeeping the listing shows but the semantics does
/// not need.
///
/// This is the rule that lets the others reach across a call. Rules only ever
/// see the sequence they are handed — that is the invariant which keeps them
/// unit-testable and position-independent — so a branch one frame down and an
/// instruction outside it are simply not in the same window. Flattening puts
/// them there:
///
/// ```text
/// jump S ; add        where S = branch { A } { B }
///   flatten_call  ->  branch { A } { B } ; add
///   distribute_branch -> branch { A add } { B add }
/// ```
///
/// It discards the call's origin, so the listing stops saying which sentence
/// the code came from. That is why it is not in `all`.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct FlattenCall;

impl Rule for FlattenCall {
    fn name(&self) -> &'static str {
        "flatten_call"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Dip {
            depth: 0,
            body,
            ..
        } = &window[0]
        else {
            return None;
        };
        // An empty body would make this the identity on the sequence; `noop`
        // owns that case, and returning it here would not terminate.
        if body.is_empty() {
            return None;
        }
        Some(body.clone())
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
    fn flatten_splices_a_plain_call_into_its_call_site() {
        let w = [dip(0, vec![op(Instruction::Add), op(Instruction::Drop)])];
        assert_eq!(
            FlattenCall.rewrite(&w),
            Some(vec![op(Instruction::Add), op(Instruction::Drop)])
        );
    }

    #[test]
    fn flatten_declines_a_dip_that_actually_hides_something() {
        // At depth 1 the body runs below a hidden value; splicing it in would
        // hand it that value instead.
        assert_eq!(
            FlattenCall.rewrite(&[dip(1, vec![op(Instruction::Add)])]),
            None
        );
    }

    #[test]
    fn flatten_leaves_the_empty_call_to_noop() {
        // Returning the empty body here would be the identity on the sequence,
        // and a rule that returns its input does not terminate.
        assert_eq!(FlattenCall.rewrite(&[dip(0, vec![])]), None);
        assert_eq!(NoOp.rewrite(&[dip(0, vec![])]), Some(vec![]));
    }

    #[test]
    fn distribute_pushes_the_next_node_into_both_arms() {
        let w = [
            branch(
                vec![op(Instruction::Push(Value::Int(1)))],
                vec![op(Instruction::Push(Value::Int(2)))],
            ),
            op(Instruction::Add),
        ];
        assert_eq!(
            DistributeBranch.rewrite(&w),
            Some(vec![branch(
                vec![op(Instruction::Push(Value::Int(1))), op(Instruction::Add)],
                vec![op(Instruction::Push(Value::Int(2))), op(Instruction::Add)],
            )])
        );
    }

    #[test]
    fn distribute_declines_with_nothing_to_push_in() {
        // Width 2, so a branch at the end of a sequence never matches.
        assert_eq!(
            DistributeBranch.rewrite(&[op(Instruction::Add), branch(vec![], vec![])]),
            None
        );
    }

    #[test]
    fn a_constant_condition_selects_its_arm() {
        let arms = || {
            branch(
                vec![op(Instruction::Push(Value::Int(10)))],
                vec![op(Instruction::Push(Value::Int(20)))],
            )
        };
        assert_eq!(
            FoldBranch.rewrite(&[op(Instruction::Push(Value::Bool(true))), arms()]),
            Some(vec![op(Instruction::Push(Value::Int(10)))])
        );
        assert_eq!(
            FoldBranch.rewrite(&[op(Instruction::Push(Value::Bool(false))), arms()]),
            Some(vec![op(Instruction::Push(Value::Int(20)))])
        );
    }

    #[test]
    fn folding_an_empty_arm_leaves_nothing() {
        assert_eq!(
            FoldBranch.rewrite(&[
                op(Instruction::Push(Value::Bool(true))),
                branch(vec![], vec![op(Instruction::Add)])
            ]),
            Some(vec![])
        );
    }

    #[test]
    fn only_a_literal_bool_folds_a_branch() {
        // The VM rejects a non-boolean condition, so folding `push 1; branch`
        // would erase a panic instead of preserving one.
        assert_eq!(
            FoldBranch.rewrite(&[
                op(Instruction::Push(Value::Int(1))),
                branch(vec![], vec![])
            ]),
            None
        );
        // And a condition that is computed rather than pushed is not constant.
        assert_eq!(
            FoldBranch.rewrite(&[op(Instruction::IsInt), branch(vec![], vec![])]),
            None
        );
    }

    #[test]
    fn pick_then_dropping_the_original_is_a_roll() {
        // After `pick 2` the original sits at depth 3, so dipping past three
        // and dropping leaves the copy on top with the original gone.
        let w = [
            op(Instruction::Pick(2)),
            dip(3, vec![op(Instruction::Drop)]),
        ];
        assert_eq!(
            PickDropToRoll.rewrite(&w),
            Some(vec![op(Instruction::Roll(2))])
        );
    }

    #[test]
    fn pick_drop_to_roll_needs_exactly_the_original_s_depth() {
        // One too shallow drops the copy instead; one too deep drops a
        // bystander. Neither is a roll.
        for depth in [2, 4] {
            assert_eq!(
                PickDropToRoll.rewrite(&[
                    op(Instruction::Pick(2)),
                    dip(depth, vec![op(Instruction::Drop)])
                ]),
                None,
                "depth {} should not match a pick 2",
                depth
            );
        }
        // And the body has to be a lone drop.
        assert_eq!(
            PickDropToRoll.rewrite(&[
                op(Instruction::Pick(0)),
                dip(1, vec![op(Instruction::Drop), op(Instruction::Drop)])
            ]),
            None
        );
    }

    #[test]
    fn pick_drop_to_roll_leaves_the_degenerate_case_to_noop() {
        // At d = 0 the answer is `roll 0`, which does nothing — but this rule
        // states one law and lets `noop` state the other.
        assert_eq!(
            PickDropToRoll.rewrite(&[
                op(Instruction::Pick(0)),
                dip(1, vec![op(Instruction::Drop)])
            ]),
            Some(vec![op(Instruction::Roll(0))])
        );
        assert_eq!(NoOp.rewrite(&[op(Instruction::Roll(0))]), Some(vec![]));
    }

    #[test]
    fn noop_removes_an_empty_dip_at_any_depth() {
        assert_eq!(NoOp.rewrite(&[dip(0, vec![])]), Some(vec![]));
        assert_eq!(NoOp.rewrite(&[dip(3, vec![])]), Some(vec![]));
    }

    #[test]
    fn noop_declines_anything_that_does_something() {
        assert_eq!(NoOp.rewrite(&[op(Instruction::Roll(1))]), None);
        assert_eq!(NoOp.rewrite(&[dip(1, vec![op(Instruction::Add)])]), None);
        assert_eq!(NoOp.rewrite(&[op(Instruction::Drop)]), None);
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

/// `pick d ; dip (d+1) { drop }` becomes `roll d`.
///
/// After `pick d` the original sits one deeper than the copy, so dipping past
/// `d + 1` and dropping removes the original and leaves the copy on top — which
/// is a roll. At `d = 0` the result is `roll 0`, which does nothing; [`NoOp`]
/// clears that up, rather than this rule special-casing it.
///
/// [`Sink`] cannot help here and should not: the dip deliberately reaches at
/// the value the pick just produced, which is precisely the interference the
/// interchange rule exists to forbid. `pick d` has arity `(d+1 -> d+2)`, so
/// `k >= m` is `d+1 >= d+2` and always false.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct PickDropToRoll;

impl Rule for PickDropToRoll {
    fn name(&self) -> &'static str {
        "pick_drop_to_roll"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Op(Instruction::Pick(d)), Node::Dip { depth, body, .. }] = window else {
            return None;
        };
        if *depth != d + 1 {
            return None;
        }
        let [Node::Op(Instruction::Drop)] = &body[..] else {
            return None;
        };
        Some(vec![Node::Op(Instruction::Roll(*d))])
    }
}

/// Removes a node that does nothing at all.
///
/// `roll 0` moves the top of the stack to the top. An empty `dip` hides a
/// region and hands it straight back. Neither is something a person writes;
/// they turn up after another rule has contracted a shuffle or emptied a body,
/// which is why this rule earns its place by composing rather than on its own.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct NoOp;

impl Rule for NoOp {
    fn name(&self) -> &'static str {
        "noop"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, window: &[Node]) -> Option<Vec<Node>> {
        match &window[0] {
            Node::Op(Instruction::Roll(0)) => Some(Vec::new()),
            Node::Dip { body, .. } if body.is_empty() => Some(Vec::new()),
            _ => None,
        }
    }
}
