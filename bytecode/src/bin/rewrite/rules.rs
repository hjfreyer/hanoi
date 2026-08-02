//! The rewrite rules.
//!
//! Every rule is a **local splice on a window of a fixed width**, expressed
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
use crate::ir::{expand_call, same_effect, Node};
use crate::program::Program;

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
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>>;
}

/// Every rule, by name. Rules are a fixed instruction set in their own
/// namespace: a tactic expression can order and place them, but cannot alias
/// or define one.
pub(crate) const ALL_RULES: &[&dyn Rule] = &[
    &AnnihilateDrop,
    &BoolIdentity,
    &CancelTuple,
    &Collapse,
    &DistributeBranch,
    &DupNatural,
    &Expand,
    &FactorBranch,
    &FlattenCall,
    &Float,
    &FoldBranch,
    &FoldConst,
    &FoldConstUnary,
    &Fuse,
    &Inline,
    &NoOp,
    &PickDropToRoll,
    &RebuildCopy,
    &RetainCondition,
    &Sink,
    &SpecializeEqual,
    &UnfactorBranch,
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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

/// How deep a node's hidden window is, if it has one.
///
/// A `Dip { depth: k }` and a `Call { depth: k }` mean the same thing — a block
/// running below `k` hidden values — and differ only in whether the block is
/// part of this tree. Every rule that reasons about the *frame* rather than the
/// body should therefore accept both, or it would silently demand that you
/// inline a callee just to move it, which is exactly the expansion the tool
/// exists to let you avoid.
///
/// `Call { depth: 0 }` is a plain jump and has no frame, so it reports `None`.
fn frame_depth(node: &Node) -> Option<usize> {
    match node {
        Node::Dip { depth, .. } => Some(*depth),
        Node::Call { depth, .. } if *depth > 0 => Some(*depth),
        _ => None,
    }
}

/// The same node with its frame set to `depth`.
fn with_frame_depth(node: &Node, depth: usize) -> Option<Node> {
    match node {
        Node::Dip { origins, body, .. } => Some(Node::Dip {
            depth,
            origins: origins.clone(),
            body: body.clone(),
        }),
        Node::Call { target, .. } => Some(Node::Call {
            depth,
            target: *target,
        }),
        _ => None,
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
/// The moved node may be an un-expanded `dip k → S` naming a real sentence as
/// readily as a spelled-out one: the side condition is about the frame, and the
/// callee's body has no say in it. Requiring the expanded form would make `sink`
/// demand an `inline` it does not need, which matters on a term where the whole
/// art is expanding as little as possible.
///
/// (A `dip N { ... }` written inline is spelled out by `build` and was never
/// affected by this — see `ir::build`. The case this covers is a `dip N` whose
/// target is a sentence somebody could also call by name.)
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
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [prev, dip] = window else { return None };
        let depth = frame_depth(dip)?;

        let (n, m) = node_arity(prog, prev)?;
        let k = depth as i64;
        if k < m {
            return None;
        }
        // The arity table keeps this non-negative, but do not trust it blindly.
        let shifted = usize::try_from(k - m + n).ok()?;

        Some(vec![with_frame_depth(dip, shifted)?, prev.clone()])
    }
}

/// `dip j { S } ; X` becomes `X ; dip (j - n + m) { S }`, where X has arity
/// `(n -> m)` and `j >= n`.
///
/// The exact inverse of [`Sink`], and the same interchange law read from the
/// other side. `sink` needs the dip's window to sit below everything `X` leaves
/// behind (`k >= m`); `float` needs it to sit below everything `X` *consumes*
/// (`j >= n`), so that `X`'s operands are entirely inside the hidden region and
/// `S` cannot disturb them. Swap `n` and `m` and each rule's arithmetic is the
/// other's.
///
/// `sink` is the normalizing direction and this one is not, which is why it has
/// no measure and why the two must never share a `repeat` — they are inverses in
/// the same way `collapse` and `expand` are. It exists for the case where a
/// total computation has to be delivered *to* somewhere rather than gathered up:
/// rebuilding a value with `tuple n` earns nothing until the rebuild reaches the
/// branch whose arm takes it apart again.
///
/// Measure: none. Termination is the caller's problem, which is what `once` and
/// `repeat_n` are for.
#[derive(Debug)]
pub(crate) struct Float;

impl Rule for Float {
    fn name(&self) -> &'static str {
        "float"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [dip, next] = window else { return None };
        let depth = frame_depth(dip)?;

        let (n, m) = node_arity(prog, next)?;
        let j = depth as i64;
        if j < n {
            return None;
        }
        let shifted = usize::try_from(j - n + m).ok()?;

        Some(vec![next.clone(), with_frame_depth(dip, shifted)?])
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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

/// Replaces a call with the block it names, spliced into the caller.
///
/// Nothing is expanded until you ask, and asking gets you the real thing: a
/// plain call hides nothing, so its body belongs in the caller's sequence
/// rather than in a frame of its own. Leaving a `dip 0` behind would put the
/// callee's code in a sequence of its own, where no rule could see it next to
/// the caller's — which made `inline` compose with almost nothing.
///
/// A `dip k` call for `k > 0` keeps its frame, because there the frame is the
/// point: the body runs below `k` hidden values.
///
/// The cost is provenance. A spliced body no longer says which sentence it
/// came from, which is why nothing inlines by default — the un-expanded
/// listing names every call on one line, and you flatten only what you mean to.
///
/// Declines a `#[recursive]` target. That is a single annotation lookup, not
/// an analysis: `check_arities` will not let a sentence call a recursive one
/// without being recursive itself, so the annotation has already propagated up
/// the call graph and its absence means the target cannot reach a cycle.
///
/// The tool also refuses to open a recursive sentence at all, which makes this
/// check unreachable in practice. It is here anyway because a rule should be
/// safe on its own terms — the alternative failure is a stack overflow rather
/// than something diagnosable, and rules are used directly by tests.
///
/// Measure: none in general. Inlining a diamond-shaped call graph duplicates
/// bodies. It terminates because the reachable call graph is finite and, by the
/// above, acyclic.
#[derive(Debug)]
pub(crate) struct Inline;

impl Rule for Inline {
    fn name(&self) -> &'static str {
        "inline"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Call { depth, target } = &window[0] else {
            return None;
        };
        if prog.is_recursive(*target) {
            return None;
        }
        Some(expand_call(prog, *depth, *target))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::{Library, Value};

    /// Most rules never consult the library; the ones that do get their own
    /// tests over a real one.
    fn prog() -> Program<'static> {
        // Leaked so the borrow is 'static and every test can just call `prog()`.
        Program::new(Box::leak(Box::new(Library::new())))
    }

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
            Collapse.rewrite(&prog(), &w),
            Some(vec![dip(5, vec![op(Instruction::Add)])])
        );
    }

    #[test]
    fn collapse_declines_a_body_that_is_more_than_one_dip() {
        let w = [dip(2, vec![dip(1, vec![]), op(Instruction::Add)])];
        assert_eq!(Collapse.rewrite(&prog(), &w), None);
    }

    #[test]
    fn expand_peels_exactly_one_level() {
        let w = [dip(3, vec![op(Instruction::Add)])];
        assert_eq!(
            Expand.rewrite(&prog(), &w),
            Some(vec![dip(1, vec![dip(2, vec![op(Instruction::Add)])])])
        );
    }

    #[test]
    fn expand_leaves_a_plain_call_and_a_unary_dip_alone() {
        assert_eq!(Expand.rewrite(&prog(), &[dip(0, vec![])]), None);
        assert_eq!(Expand.rewrite(&prog(), &[dip(1, vec![])]), None);
    }

    #[test]
    fn sink_widens_past_an_operator_that_consumes_two() {
        // `add` is (2 -> 1): 1 >= 1 clears the window, and the same window is
        // 1 - 1 + 2 = 2 deep on the other side.
        let w = [op(Instruction::Add), dip(1, vec![])];
        assert_eq!(
            Sink.rewrite(&prog(), &w),
            Some(vec![dip(2, vec![]), op(Instruction::Add)])
        );
    }

    #[test]
    fn sink_narrows_past_a_push() {
        // `push` is (0 -> 1), so the dip loses the value it was hiding.
        let w = [op(Instruction::Push(Value::Int(1))), dip(1, vec![])];
        assert_eq!(
            Sink.rewrite(&prog(), &w),
            Some(vec![dip(0, vec![]), op(Instruction::Push(Value::Int(1)))])
        );
    }

    #[test]
    fn sink_declines_when_the_window_would_reach_what_prev_produced() {
        // `untuple 3` is (1 -> 3); a dip hiding only two would be rewriting a
        // slot the untuple just filled.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Untuple(3)), dip(2, vec![])]),
            None
        );
        // Hiding three clears it, and the window is 3 - 3 + 1 = 1 deep before.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Untuple(3)), dip(3, vec![])]),
            Some(vec![dip(1, vec![]), op(Instruction::Untuple(3))])
        );
    }

    #[test]
    fn sink_declines_past_a_panic() {
        // Nothing after a panic runs, so there is no interchange to make.
        assert_eq!(Sink.rewrite(&prog(), &[op(Instruction::Panic), dip(9, vec![])]), None);
    }

    #[test]
    fn fuse_joins_dips_at_equal_depth_and_declines_otherwise() {
        let a = dip(2, vec![op(Instruction::Add)]);
        let b = dip(2, vec![op(Instruction::Drop)]);
        assert_eq!(
            Fuse.rewrite(&prog(), &[a, b]),
            Some(vec![dip(
                2,
                vec![op(Instruction::Add), op(Instruction::Drop)]
            )])
        );
        assert_eq!(Fuse.rewrite(&prog(), &[dip(1, vec![]), dip(2, vec![])]), None);
    }

    #[test]
    fn factor_branch_hoists_the_shared_prefix_under_a_dip() {
        let shared = op(Instruction::Push(Value::Int(7)));
        let w = [branch(
            vec![shared.clone(), op(Instruction::Push(Value::Int(1)))],
            vec![shared.clone(), op(Instruction::Push(Value::Int(2)))],
        )];
        assert_eq!(
            FactorBranch.rewrite(&prog(), &w),
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
        assert_eq!(FactorBranch.rewrite(&prog(), &w), None);
    }

    #[test]
    fn annihilate_cancels_a_total_producer_against_its_drop() {
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[
                op(Instruction::Push(Value::Int(1))),
                op(Instruction::Drop)
            ]),
            Some(vec![])
        );
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Pick(3)), op(Instruction::Drop)]),
            Some(vec![])
        );
    }

    #[test]
    fn annihilate_leaves_the_drop_behind_for_a_type_test() {
        // `is_int` consumes a value to make the dropped one, so the drop still
        // has to happen — it just takes the input instead.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::IsInt), op(Instruction::Drop)]),
            Some(vec![op(Instruction::Drop)])
        );
    }

    #[test]
    fn flatten_splices_a_plain_call_into_its_call_site() {
        let w = [dip(0, vec![op(Instruction::Add), op(Instruction::Drop)])];
        assert_eq!(
            FlattenCall.rewrite(&prog(), &w),
            Some(vec![op(Instruction::Add), op(Instruction::Drop)])
        );
    }

    #[test]
    fn flatten_declines_a_dip_that_actually_hides_something() {
        // At depth 1 the body runs below a hidden value; splicing it in would
        // hand it that value instead.
        assert_eq!(
            FlattenCall.rewrite(&prog(), &[dip(1, vec![op(Instruction::Add)])]),
            None
        );
    }

    #[test]
    fn flatten_leaves_the_empty_call_to_noop() {
        // Returning the empty body here would be the identity on the sequence,
        // and a rule that returns its input does not terminate.
        assert_eq!(FlattenCall.rewrite(&prog(), &[dip(0, vec![])]), None);
        assert_eq!(NoOp.rewrite(&prog(), &[dip(0, vec![])]), Some(vec![]));
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
            DistributeBranch.rewrite(&prog(), &w),
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
            DistributeBranch.rewrite(&prog(), &[op(Instruction::Add), branch(vec![], vec![])]),
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
            FoldBranch.rewrite(&prog(), &[op(Instruction::Push(Value::Bool(true))), arms()]),
            Some(vec![op(Instruction::Push(Value::Int(10)))])
        );
        assert_eq!(
            FoldBranch.rewrite(&prog(), &[op(Instruction::Push(Value::Bool(false))), arms()]),
            Some(vec![op(Instruction::Push(Value::Int(20)))])
        );
    }

    #[test]
    fn folding_an_empty_arm_leaves_nothing() {
        assert_eq!(
            FoldBranch.rewrite(&prog(), &[
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
            FoldBranch.rewrite(&prog(), &[
                op(Instruction::Push(Value::Int(1))),
                branch(vec![], vec![])
            ]),
            None
        );
        // And a condition that is computed rather than pushed is not constant.
        assert_eq!(
            FoldBranch.rewrite(&prog(), &[op(Instruction::IsInt), branch(vec![], vec![])]),
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
            PickDropToRoll.rewrite(&prog(), &w),
            Some(vec![op(Instruction::Roll(2))])
        );
    }

    #[test]
    fn pick_drop_to_roll_needs_exactly_the_original_s_depth() {
        // One too shallow drops the copy instead; one too deep drops a
        // bystander. Neither is a roll.
        for depth in [2, 4] {
            assert_eq!(
                PickDropToRoll.rewrite(&prog(), &[
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
            PickDropToRoll.rewrite(&prog(), &[
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
            PickDropToRoll.rewrite(&prog(), &[
                op(Instruction::Pick(0)),
                dip(1, vec![op(Instruction::Drop)])
            ]),
            Some(vec![op(Instruction::Roll(0))])
        );
        assert_eq!(NoOp.rewrite(&prog(), &[op(Instruction::Roll(0))]), Some(vec![]));
    }

    #[test]
    fn noop_removes_an_empty_dip_at_any_depth() {
        assert_eq!(NoOp.rewrite(&prog(), &[dip(0, vec![])]), Some(vec![]));
        assert_eq!(NoOp.rewrite(&prog(), &[dip(3, vec![])]), Some(vec![]));
    }

    #[test]
    fn noop_declines_anything_that_does_something() {
        assert_eq!(NoOp.rewrite(&prog(), &[op(Instruction::Roll(1))]), None);
        assert_eq!(NoOp.rewrite(&prog(), &[dip(1, vec![op(Instruction::Add)])]), None);
        assert_eq!(NoOp.rewrite(&prog(), &[op(Instruction::Drop)]), None);
    }

    #[test]
    fn annihilate_declines_a_partial_producer() {
        // `add; drop` is not `drop; drop`: the add still rejects non-numeric
        // operands, and cancelling it would discard that check.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Add), op(Instruction::Drop)]),
            None
        );
        // `equal` is total in the VM, but the Z3 model gives it a panic branch,
        // so the tool does not assert an equivalence the verifier would not.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Equal), op(Instruction::Drop)]),
            None
        );
    }

    // -----------------------------------------------------------------------
    // Value rules
    // -----------------------------------------------------------------------

    fn push(v: Value) -> Node {
        op(Instruction::Push(v))
    }

    /// Symbols compare by id, so distinct ids are distinct symbols.
    fn sym(id: usize) -> Value {
        Value::Symbol(bytecode::Symbol {
            id,
            name: format!("s{}", id),
        })
    }

    #[test]
    fn fold_const_decides_equal_on_any_pair() {
        // The case the whole symbol decision tree turns on. Two distinct
        // symbols are distinct structurally, so no extra disjointness fact is
        // needed anywhere.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[push(sym(1)), push(sym(2)), op(Instruction::Equal)]
            ),
            Some(vec![push(Value::Bool(false))])
        );
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[push(sym(1)), push(sym(1)), op(Instruction::Equal)]
            ),
            Some(vec![push(Value::Bool(true))])
        );
        // Different types compare too, and compare unequal.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    push(Value::Int(1)),
                    push(Value::Bool(true)),
                    op(Instruction::Equal)
                ]
            ),
            Some(vec![push(Value::Bool(false))])
        );
    }

    #[test]
    fn fold_const_declines_an_operator_that_would_panic() {
        // `push 1; push 2; and` is a panic, and `push false` is not one. The
        // literals make the operands known, which is exactly what makes it
        // knowable that this one must *not* fold.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[push(Value::Int(1)), push(Value::Int(2)), op(Instruction::And)]
            ),
            None
        );
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[push(sym(1)), push(sym(2)), op(Instruction::Less)]
            ),
            None
        );
        // Two booleans are fine.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    push(Value::Bool(true)),
                    push(Value::Bool(false)),
                    op(Instruction::And)
                ]
            ),
            Some(vec![push(Value::Bool(false))])
        );
    }

    #[test]
    fn fold_const_needs_both_operands_literal() {
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), push(sym(1)), op(Instruction::Equal)]
            ),
            None
        );
    }

    #[test]
    fn fold_const_unary_answers_the_is_family_but_not_a_rejecting_one() {
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(sym(1)), op(Instruction::IsSymbol)]),
            Some(vec![push(Value::Bool(true))])
        );
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(Value::Int(3)), op(Instruction::IsSymbol)]),
            Some(vec![push(Value::Bool(false))])
        );
        // `not` rejects a non-boolean, so it must not fold on one.
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(sym(1)), op(Instruction::Not)]),
            None
        );
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(Value::Bool(true)), op(Instruction::Not)]),
            Some(vec![push(Value::Bool(false))])
        );
    }

    #[test]
    fn bool_identity_drops_a_unit_and_only_when_the_operand_is_known_boolean() {
        // `is_symbol` answers with a Bool or panics, so `&& true` adds nothing.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    op(Instruction::IsSymbol),
                    push(Value::Bool(true)),
                    op(Instruction::And)
                ]
            ),
            Some(vec![op(Instruction::IsSymbol)])
        );
        // `pick 0` says nothing about the value, so the `and` is still the only
        // thing rejecting a non-boolean and has to stay.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    push(Value::Bool(true)),
                    op(Instruction::And)
                ]
            ),
            None
        );
        // A call is not enough either, even to a sentence that does return a
        // bool: that is a fact about the library, not about this node.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    Node::Call {
                        depth: 0,
                        target: bytecode::SentenceIndex::from(0)
                    },
                    push(Value::Bool(true)),
                    op(Instruction::And)
                ]
            ),
            None
        );
    }

    #[test]
    fn bool_identity_keeps_the_operand_in_the_absorbing_case() {
        // `a && false` is `false` only on the runs where `a` happened at all,
        // so the operand stays and a `drop` takes its place.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    op(Instruction::IsSymbol),
                    push(Value::Bool(false)),
                    op(Instruction::And)
                ]
            ),
            Some(vec![
                op(Instruction::IsSymbol),
                op(Instruction::Drop),
                push(Value::Bool(false))
            ])
        );
        // The dual: `a || true` is `true`.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    op(Instruction::IsTuple),
                    push(Value::Bool(true)),
                    op(Instruction::Or)
                ]
            ),
            Some(vec![
                op(Instruction::IsTuple),
                op(Instruction::Drop),
                push(Value::Bool(true))
            ])
        );
        // And `a || false` is `a`.
        assert_eq!(
            BoolIdentity.rewrite(
                &prog(),
                &[
                    op(Instruction::IsTuple),
                    push(Value::Bool(false)),
                    op(Instruction::Or)
                ]
            ),
            Some(vec![op(Instruction::IsTuple)])
        );
    }

    #[test]
    fn retain_condition_hands_each_arm_its_own_literal() {
        let w = [
            op(Instruction::Pick(0)),
            branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]),
        ];
        assert_eq!(
            RetainCondition.rewrite(&prog(), &w),
            Some(vec![branch(
                vec![push(Value::Bool(true)), op(Instruction::Add)],
                vec![push(Value::Bool(false)), op(Instruction::Drop)],
            )])
        );
    }

    #[test]
    fn retain_condition_needs_the_copy_to_be_of_the_condition() {
        // `pick 1` copies something else, so the value the arm would see is
        // not the one the branch tested.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[op(Instruction::Pick(1)), branch(vec![], vec![])]
            ),
            None
        );
        // And with no copy at all there is nothing left on the stack to name.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[op(Instruction::IsTuple), branch(vec![], vec![])]
            ),
            None
        );
    }

    #[test]
    fn retain_condition_composes_with_folding() {
        // The point of the rule. `pick 0; branch` puts a literal at the head of
        // each arm, and a `branch` nested at that head is then something
        // `fold_branch` can decide -- which is how a path condition reaches the
        // code that re-tests it.
        let inner = branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]);
        let w = [
            op(Instruction::Pick(0)),
            branch(vec![inner.clone()], vec![]),
        ];
        let Some(out) = RetainCondition.rewrite(&prog(), &w) else {
            panic!("expected retain_condition to fire")
        };
        let [Node::Branch { then_body, .. }] = &out[..] else {
            panic!("expected a branch")
        };
        assert_eq!(
            FoldBranch.rewrite(&prog(), &then_body[..2]),
            Some(vec![op(Instruction::Add)]),
            "the literal the arm now carries should decide the branch inside it"
        );
    }

    #[test]
    fn specialize_equal_gives_the_then_arm_the_literal() {
        let w = [
            op(Instruction::Pick(0)),
            push(sym(1)),
            op(Instruction::Equal),
            branch(vec![op(Instruction::IsSymbol)], vec![op(Instruction::Add)]),
        ];
        assert_eq!(
            SpecializeEqual.rewrite(&prog(), &w),
            Some(vec![
                op(Instruction::Pick(0)),
                push(sym(1)),
                op(Instruction::Equal),
                branch(
                    vec![op(Instruction::Drop), push(sym(1)), op(Instruction::IsSymbol)],
                    // The else arm learns only a disequality, which has no
                    // literal form.
                    vec![op(Instruction::Add)],
                ),
            ])
        );
    }

    #[test]
    fn specialize_equal_settles_instead_of_oscillating() {
        // Regression. The obvious guard -- "the arm already begins with
        // `drop; push c`" -- does not survive its neighbours: the `push c` is
        // live code, so `annihilate_drop` cancels it against a following drop
        // and the arm stops matching the guard, forever. Guarding on the
        // leading `drop` works because it is the arm's first node, which the
        // two-node rules have nothing to pair it with.
        let once = [
            op(Instruction::Pick(0)),
            push(sym(1)),
            op(Instruction::Equal),
            branch(
                vec![op(Instruction::Drop), push(sym(1)), op(Instruction::Drop)],
                vec![],
            ),
        ];
        assert_eq!(SpecializeEqual.rewrite(&prog(), &once), None);

        // An arm that opens by discarding the value has no use for a
        // refinement of it, which is the same condition read forwards.
        let discards = [
            op(Instruction::Pick(0)),
            push(sym(1)),
            op(Instruction::Equal),
            branch(vec![op(Instruction::Drop), op(Instruction::Add)], vec![]),
        ];
        assert_eq!(SpecializeEqual.rewrite(&prog(), &discards), None);
    }

    #[test]
    fn specialize_equal_declines_a_float_because_equal_is_not_identity() {
        // `0.0 == -0.0` holds while the two remain distinguishable, so
        // substituting the literal would not be invisible.
        let w = [
            op(Instruction::Pick(0)),
            push(Value::Float(0.0)),
            op(Instruction::Equal),
            branch(vec![op(Instruction::IsFloat)], vec![]),
        ];
        assert_eq!(SpecializeEqual.rewrite(&prog(), &w), None);

        // And through a tuple, since tuples compare elementwise.
        let nested = [
            op(Instruction::Pick(0)),
            push(Value::Tuple(vec![Value::Int(1), Value::Float(0.0)])),
            op(Instruction::Equal),
            branch(vec![op(Instruction::IsTuple)], vec![]),
        ];
        assert_eq!(SpecializeEqual.rewrite(&prog(), &nested), None);

        // A float-free tuple is fine.
        let ok = [
            op(Instruction::Pick(0)),
            push(Value::Tuple(vec![Value::Int(1), sym(2)])),
            op(Instruction::Equal),
            branch(vec![op(Instruction::IsTuple)], vec![]),
        ];
        assert!(SpecializeEqual.rewrite(&prog(), &ok).is_some());
    }

    #[test]
    fn specialize_equal_needs_the_copy() {
        // Without `pick 0` the value is consumed by the `equal`, so there is
        // nothing left in the arm to refine.
        let w = [
            op(Instruction::IsSymbol),
            push(sym(1)),
            op(Instruction::Equal),
            branch(vec![op(Instruction::Add)], vec![]),
        ];
        assert_eq!(SpecializeEqual.rewrite(&prog(), &w), None);
    }

    #[test]
    fn dup_natural_shares_a_computation_done_on_a_copy_and_the_original() {
        // The m = 1 case: one result, so one copy.
        let w = [
            op(Instruction::Pick(0)),
            op(Instruction::IsTuple),
            dip(1, vec![op(Instruction::IsTuple)]),
        ];
        assert_eq!(
            DupNatural.rewrite(&prog(), &w),
            Some(vec![op(Instruction::IsTuple), op(Instruction::Pick(0))])
        );

        // The case the crux turns on: the value came apart into three, so
        // three copies, each reaching past the ones already made.
        let w = [
            op(Instruction::Pick(0)),
            op(Instruction::Untuple(3)),
            dip(3, vec![op(Instruction::Untuple(3))]),
        ];
        assert_eq!(
            DupNatural.rewrite(&prog(), &w),
            Some(vec![
                op(Instruction::Untuple(3)),
                op(Instruction::Pick(2)),
                op(Instruction::Pick(2)),
                op(Instruction::Pick(2)),
            ])
        );
    }

    #[test]
    fn rebuild_copy_destructures_the_value_and_rebuilds_the_copy() {
        assert_eq!(
            RebuildCopy.rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Untuple(3))]
            ),
            Some(vec![
                op(Instruction::Untuple(3)),
                op(Instruction::Pick(2)),
                op(Instruction::Pick(2)),
                op(Instruction::Pick(2)),
                dip(3, vec![op(Instruction::Tuple(3))]),
            ])
        );
        // n = 1 is the degenerate but real case.
        assert_eq!(
            RebuildCopy.rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Untuple(1))]
            ),
            Some(vec![
                op(Instruction::Untuple(1)),
                op(Instruction::Pick(0)),
                dip(1, vec![op(Instruction::Tuple(1))]),
            ])
        );
        // A 0-tuple has no parts to share.
        assert_eq!(
            RebuildCopy.rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Untuple(0))]
            ),
            None
        );
        // The copy has to be of the value being taken apart.
        assert_eq!(
            RebuildCopy.rewrite(
                &prog(),
                &[op(Instruction::Pick(1)), op(Instruction::Untuple(3))]
            ),
            None
        );
    }

    #[test]
    fn rebuild_copy_settles() {
        // Its own output contains no `pick 0; untuple n`, so `each` terminates
        // rather than growing the term forever.
        let out = RebuildCopy
            .rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Untuple(2))],
            )
            .expect("should fire");
        for w in out.windows(2) {
            assert_eq!(RebuildCopy.rewrite(&prog(), w), None, "re-fired on {:?}", w);
        }
    }

    #[test]
    fn float_and_sink_are_inverse_on_everything_that_moves() {
        // The arithmetic is dual -- `sink` needs `k >= m` and shifts by
        // `-m + n`, `float` needs `j >= n` and shifts by `-n + m` -- so
        // round-tripping is the honest way to check both at once. One entry per
        // arity the instruction table can produce.
        let xs = [
            op(Instruction::Push(Value::Int(1))), // 0 -> 1
            op(Instruction::Drop),                // 1 -> 0
            op(Instruction::IsTuple),             // 1 -> 1
            op(Instruction::Add),                 // 2 -> 1
            op(Instruction::Pick(2)),             // 3 -> 4
            op(Instruction::Roll(2)),             // 3 -> 3
            op(Instruction::Untuple(3)),          // 1 -> 3
            op(Instruction::Tuple(3)),            // 3 -> 1
        ];
        for x in xs {
            let (n, m) = node_arity(&prog(), &x).expect("arity should be known");
            for k in 0..8usize {
                let sunk = Sink.rewrite(&prog(), &[x.clone(), dip(k, vec![op(Instruction::Add)])]);
                // `sink` fires exactly when the dip clears X's outputs.
                assert_eq!(sunk.is_some(), k as i64 >= m, "sink at k={} for {:?}", k, x);
                let Some(sunk) = sunk else { continue };

                // And `float` takes it straight back.
                assert_eq!(
                    Float.rewrite(&prog(), &sunk),
                    Some(vec![x.clone(), dip(k, vec![op(Instruction::Add)])]),
                    "float should invert sink at k={} for {:?} (arity {}->{})",
                    k,
                    x,
                    n,
                    m
                );
            }
        }
    }

    #[test]
    fn float_declines_when_x_reaches_under_the_hidden_window() {
        // `dip 1 { S }; add` cannot become `add; dip _ { S }`: the add's second
        // operand is below the hidden region, so `S` may well have produced it.
        assert_eq!(
            Float.rewrite(
                &prog(),
                &[dip(1, vec![op(Instruction::Push(Value::Int(1)))]), op(Instruction::Add)]
            ),
            None
        );
        // With the window deep enough, both operands are hidden and it moves.
        assert!(Float
            .rewrite(
                &prog(),
                &[dip(2, vec![op(Instruction::Push(Value::Int(1)))]), op(Instruction::Add)]
            )
            .is_some());
    }

    #[test]
    fn dup_natural_takes_either_orientation() {
        // `sink` decides which one you get. Written by hand it is
        // `pick 0; X; dip m { X }`, but once anything hoists the second
        // occurrence out of a branch, `sink` walks it left past the first and
        // it lands as `pick 0; dip 1 { X }; X`. Both compute X twice on the
        // same value and both collapse the same way.
        let hand_written = [
            op(Instruction::Pick(0)),
            op(Instruction::Untuple(3)),
            dip(3, vec![op(Instruction::Untuple(3))]),
        ];
        let after_sinking = [
            op(Instruction::Pick(0)),
            dip(1, vec![op(Instruction::Untuple(3))]),
            op(Instruction::Untuple(3)),
        ];
        let shared = Some(vec![
            op(Instruction::Untuple(3)),
            op(Instruction::Pick(2)),
            op(Instruction::Pick(2)),
            op(Instruction::Pick(2)),
        ]);
        assert_eq!(DupNatural.rewrite(&prog(), &hand_written), shared);
        assert_eq!(DupNatural.rewrite(&prog(), &after_sinking), shared);
    }

    #[test]
    fn dup_natural_needs_the_frame_to_match_what_the_first_copy_produced() {
        // `untuple 3` leaves three values, so the second occurrence has to sit
        // under exactly three. At any other depth the two are not looking at
        // the same thing.
        for depth in [1, 2, 4] {
            assert_eq!(
                DupNatural.rewrite(
                    &prog(),
                    &[
                        op(Instruction::Pick(0)),
                        op(Instruction::Untuple(3)),
                        dip(depth, vec![op(Instruction::Untuple(3))]),
                    ]
                ),
                None,
                "depth {} should not match",
                depth
            );
        }
        // And it has to be the same computation.
        assert_eq!(
            DupNatural.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    op(Instruction::Untuple(3)),
                    dip(3, vec![op(Instruction::Untuple(2))]),
                ]
            ),
            None
        );
    }

    #[test]
    fn dup_natural_declines_print() {
        // The one instruction where running twice and running once differ in
        // something other than the stack.
        assert_eq!(
            DupNatural.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    op(Instruction::Print),
                    dip(1, vec![op(Instruction::Print)]),
                ]
            ),
            None
        );
    }

    #[test]
    fn unfactor_branch_inverts_factor_branch() {
        let factored = [
            dip(1, vec![op(Instruction::IsTuple)]),
            branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]),
        ];
        let Some(unfactored) = UnfactorBranch.rewrite(&prog(), &factored) else {
            panic!("expected unfactor_branch to fire")
        };
        assert_eq!(
            unfactored,
            vec![branch(
                vec![op(Instruction::IsTuple), op(Instruction::Add)],
                vec![op(Instruction::IsTuple), op(Instruction::Drop)],
            )]
        );
        // Round trip: factor_branch takes it straight back.
        assert_eq!(
            FactorBranch.rewrite(&prog(), &unfactored),
            Some(factored.to_vec())
        );
    }

    #[test]
    fn cancel_tuple_goes_one_way_only() {
        assert_eq!(
            CancelTuple.rewrite(
                &prog(),
                &[op(Instruction::Tuple(2)), op(Instruction::Untuple(2))]
            ),
            Some(Vec::new())
        );
        // `untuple n; tuple n` is *not* a no-op: `untuple` is the instruction
        // that checks the shape, so removing the pair would accept values the
        // original rejected.
        assert_eq!(
            CancelTuple.rewrite(
                &prog(),
                &[op(Instruction::Untuple(2)), op(Instruction::Tuple(2))]
            ),
            None
        );
        // Mismatched widths are a panic, not a cancellation.
        assert_eq!(
            CancelTuple.rewrite(
                &prog(),
                &[op(Instruction::Tuple(2)), op(Instruction::Untuple(3))]
            ),
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
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
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        match &window[0] {
            Node::Op(Instruction::Roll(0)) => Some(Vec::new()),
            Node::Dip { body, .. } if body.is_empty() => Some(Vec::new()),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Values
//
// Everything above rearranges code without ever asking what a value *is*. The
// rules below are the ones that do, and they all answer to the same
// constraint: an instruction that rejects an operand is a check, and a rewrite
// that removes the check has changed the program even when it has not changed
// the result. `equal` is total and folds freely; `and` is not and does not.
// ---------------------------------------------------------------------------

/// The literal a node pushes, if it pushes one.
fn pushed(node: &Node) -> Option<&Value> {
    match node {
        Node::Op(Instruction::Push(v)) => Some(v),
        _ => None,
    }
}

/// Whether this node always leaves a `Bool` on top, or panics.
///
/// The point of the "or panics" is that a caller may then treat the value as a
/// boolean without having to keep `and`'s type check alive separately: on every
/// path where the check would have mattered, the node already failed.
///
/// Deliberately syntactic. A call to a sentence that happens to return a bool
/// does not count — that is a fact about the library rather than about this
/// node, and reading it here would make the rule's answer depend on which
/// sentence a name currently resolves to. Inline the callee and the operator
/// underneath becomes visible on its own.
fn yields_bool(node: &Node) -> bool {
    matches!(
        node,
        Node::Op(
            Instruction::IsInt
                | Instruction::IsBool
                | Instruction::IsFloat
                | Instruction::IsSymbol
                | Instruction::IsTuple
                | Instruction::Equal
                | Instruction::Greater
                | Instruction::Less
                | Instruction::And
                | Instruction::Or
                | Instruction::Not
                | Instruction::Push(Value::Bool(_))
        )
    )
}

/// `B ; push true ; and` becomes `B`, and the three other unit laws.
///
/// `a && true = a` is only a rewrite of *this program* when `a` is known to be
/// a boolean, because `and` rejects anything else and dropping it would erase
/// that rejection. `B` supplying the operand is what licenses it, which is why
/// the window is three wide: the two-node view `push true; and` cannot tell
/// whether the value underneath was ever checked.
///
/// The absorbing cases go to `B; drop; push c` rather than to `push c`, for the
/// same reason — `B` may panic, and `a && false` is only `false` on the runs
/// where `a` existed.
///
/// Measure: node count, counting the absorbing cases as level (2 nodes for 2)
/// and relying on the `drop` they expose to be cancelled by `annihilate_drop`.
#[derive(Debug)]
pub(crate) struct BoolIdentity;

impl Rule for BoolIdentity {
    fn name(&self) -> &'static str {
        "bool_identity"
    }
    fn width(&self) -> usize {
        3
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [b, lit, op] = window else { return None };
        if !yields_bool(b) {
            return None;
        }
        let Some(Value::Bool(k)) = pushed(lit) else {
            return None;
        };
        let unit = match (op, k) {
            // a && true = a, a || false = a
            (Node::Op(Instruction::And), true) | (Node::Op(Instruction::Or), false) => true,
            // a && false = false, a || true = true
            (Node::Op(Instruction::And), false) | (Node::Op(Instruction::Or), true) => false,
            _ => return None,
        };
        Some(if unit {
            vec![b.clone()]
        } else {
            vec![
                b.clone(),
                Node::Op(Instruction::Drop),
                Node::Op(Instruction::Push(Value::Bool(*k))),
            ]
        })
    }
}

/// Evaluates an operator whose operands are already literals.
///
/// Note carefully why this is allowed to fold `equal` when [`AnnihilateDrop`]
/// is not. The objection there is that an operand may itself be a panic, which
/// `equal` propagates and `drop; drop` would not — an operator's panic branch is
/// reachable whenever its operands are arbitrary. **A literal is never a
/// panic**, so with both operands pushed right here that branch cannot be
/// taken, and the fold is an equality in the Z3 encoding and in the VM alike.
/// The rule needs no view on which of the two is the real semantics.
///
/// That still leaves the operators that reject perfectly ordinary values:
/// `and`/`or` fold only on two booleans and the comparisons only on two
/// numbers, since `push 1; push 2; and` is a panic and `push false` is not.
/// `equal` rejects nothing, so it folds on any pair — which is what decides
/// `push idle; push thirsty; equal` and collapses a symbol decision tree.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct FoldConst;

impl Rule for FoldConst {
    fn name(&self) -> &'static str {
        "fold_const"
    }
    fn width(&self) -> usize {
        3
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [x, y, op] = window else { return None };
        let (a, b) = (pushed(x)?, pushed(y)?);
        let Node::Op(inst) = op else { return None };

        let out = match inst {
            // Rejects nothing: any two values compare.
            Instruction::Equal => Value::Bool(a == b),
            Instruction::And | Instruction::Or => match (a, b) {
                (Value::Bool(p), Value::Bool(q)) => Value::Bool(match inst {
                    Instruction::And => *p && *q,
                    _ => *p || *q,
                }),
                // Anything else is a panic, and a panic is not a value.
                _ => return None,
            },
            Instruction::Greater | Instruction::Less => match (a, b) {
                (Value::Int(p), Value::Int(q)) => Value::Bool(match inst {
                    Instruction::Greater => p > q,
                    _ => p < q,
                }),
                _ => return None,
            },
            _ => return None,
        };
        Some(vec![Node::Op(Instruction::Push(out))])
    }
}

/// Evaluates a one-operand operator applied to a literal.
///
/// Same licence as [`FoldConst`]: the operand is a literal, so it is not a
/// panic, so nothing the operator would propagate is in reach. The `is_*`
/// family additionally rejects nothing — it asks a question about the value it
/// is given rather than demanding a particular one — so it folds on any
/// literal, while `not` and `tuple_length` fold only on the shape they accept.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct FoldConstUnary;

impl Rule for FoldConstUnary {
    fn name(&self) -> &'static str {
        "fold_const_unary"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [x, op] = window else { return None };
        let a = pushed(x)?;
        let Node::Op(inst) = op else { return None };

        let out = match (inst, a) {
            (Instruction::IsInt, _) => Value::Bool(matches!(a, Value::Int(_))),
            (Instruction::IsBool, _) => Value::Bool(matches!(a, Value::Bool(_))),
            (Instruction::IsFloat, _) => Value::Bool(matches!(a, Value::Float(_))),
            (Instruction::IsSymbol, _) => Value::Bool(matches!(a, Value::Symbol(_))),
            (Instruction::IsTuple, _) => Value::Bool(matches!(a, Value::Tuple(_))),
            (Instruction::Not, Value::Bool(p)) => Value::Bool(!p),
            (Instruction::TupleLength, Value::Tuple(t)) => Value::Int(t.len() as i64),
            _ => return None,
        };
        Some(vec![Node::Op(Instruction::Push(out))])
    }
}

/// `pick 0 ; branch { A } { B }` becomes `branch { push true; A } { push false; B }`.
///
/// A branch may tell its arms what its condition was. The VM rejects a
/// non-boolean condition, so an arm that runs at all ran because the value was
/// exactly `true` or exactly `false` — and the copy `pick 0` left behind is
/// therefore a literal, which the arm can push for itself.
///
/// This is how a **path condition becomes a value**, and it is worth being
/// precise about why that matters. A predicate in this language is written
/// `pick 0; jump P::check; branch { ... }`: the check consumes a copy and the
/// arm gets a bare `true` that says nothing about what was established. Once
/// the arm holds the literal, every rule that folds literals can use it, and
/// the fact travels by the ordinary movement rules rather than by a traversal
/// that carries hypotheses around. Nothing here needs to know where in the tree
/// it is — the governing invariant is untouched, because the fact rides in the
/// sequence.
///
/// Measure: the number of branches immediately preceded by `pick 0`. Firing
/// removes one, and the arms it rewrites begin with a `push`, so no rule in
/// this set can hand one back.
#[derive(Debug)]
pub(crate) struct RetainCondition;

impl Rule for RetainCondition {
    fn name(&self) -> &'static str {
        "retain_condition"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Op(Instruction::Pick(0)), Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        }] = window
        else {
            return None;
        };

        let arm = |lit: bool, body: &Vec<Node>| {
            let mut out = vec![Node::Op(Instruction::Push(Value::Bool(lit)))];
            out.extend(body.iter().cloned());
            out
        };

        Some(vec![Node::Branch {
            then_origin: then_origin.clone(),
            then_body: arm(true, then_body),
            else_origin: else_origin.clone(),
            else_body: arm(false, else_body),
        }])
    }
}

/// Whether substituting this literal for a value `equal` accepted is invisible.
///
/// `equal` answers with Rust's `PartialEq` on `Value`, and on floats that is
/// not identity: `0.0 == -0.0` is true while the two are distinguishable, and
/// tuples inherit the problem through their elements. Symbols, ints and bools
/// have no such gap — comparing equal means indistinguishable — so the
/// refinement rule takes those and declines anything with a float in it.
fn float_free(v: &Value) -> bool {
    match v {
        Value::Float(_) => false,
        Value::Tuple(elems) => elems.iter().all(float_free),
        _ => true,
    }
}

/// `pick 0; push c; equal; branch { A } { B }` gives A the literal: its arm
/// becomes `drop; push c; A`.
///
/// The then-arm runs exactly when the copy `pick 0` left behind compares equal
/// to `c`, so inside that arm the value on top *is* `c` and may be replaced by
/// it. This is the refinement the `type` sugar's decision trees are built out
/// of — every union arm is `pick 0; push <symbol>; equal; branch` — and it is
/// what turns a test against an opaque value into a literal the folding rules
/// can act on.
///
/// The else arm learns a disequality, which has no literal form and is left
/// alone.
///
/// Note what this does *not* do. It refines the value the check is holding, not
/// the one the caller kept: where a predicate consumes a copy and the real code
/// later destructures the original, these are different stack slots and no
/// refinement relates them. Sharing the two is a separate problem.
///
/// Measure: the number of such branches whose then-arm does not begin with
/// `drop`. Firing takes one, because the arm it produces begins with exactly
/// that.
///
/// The guard has to be about `drop` rather than about the literal, and finding
/// out why is instructive. Guarding on "the arm already starts with `drop; push
/// c`" is the obvious statement of "already refined", and it oscillates: the
/// `push c` this rule introduces is live code that the other rules will act on,
/// so `annihilate_drop` cancels it against a following `drop` and
/// `fold_const_unary` rewrites it into a different literal — after which the
/// arm no longer matches the guard and the rule fires again, forever.
///
/// A guard survives its neighbours only if it names something they cannot
/// remove. The leading `drop` is the first node of the arm, so the two-node
/// rules have nothing to pair it with, and every path that consumes the
/// literal leaves it in place. It also says the right thing on its own terms:
/// an arm that opens by discarding the value has no use for a refinement of
/// it.
#[derive(Debug)]
pub(crate) struct SpecializeEqual;

impl Rule for SpecializeEqual {
    fn name(&self) -> &'static str {
        "specialize_equal"
    }
    fn width(&self) -> usize {
        4
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [pick, lit, eq, br] = window else {
            return None;
        };
        if !matches!(pick, Node::Op(Instruction::Pick(0)))
            || !matches!(eq, Node::Op(Instruction::Equal))
        {
            return None;
        }
        let c = pushed(lit)?;
        if !float_free(c) {
            return None;
        }
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = br
        else {
            return None;
        };

        if matches!(then_body.first(), Some(Node::Op(Instruction::Drop))) {
            // Either already refined, or an arm that discards the value
            // anyway. See the measure: this is what makes the rule settle.
            return None;
        }

        let mut body = vec![
            Node::Op(Instruction::Drop),
            Node::Op(Instruction::Push(c.clone())),
        ];
        body.extend(then_body.iter().cloned());
        Some(vec![
            pick.clone(),
            lit.clone(),
            eq.clone(),
            Node::Branch {
                then_origin: then_origin.clone(),
                then_body: body,
                else_origin: else_origin.clone(),
                else_body: else_body.clone(),
            },
        ])
    }
}

/// `pick 0 ; X ; dip m { X }` becomes `X ; (pick (m-1))^m`, for `X : 1 -> m`.
///
/// Duplication is natural: computing `X` on a copy and then on the original
/// gives the same thing as computing it once and copying all `m` results. The
/// left-hand side is what a caller looks like when it hands a value to a
/// predicate and then takes the value apart itself; the right-hand side is that
/// same program with the work shared.
///
/// At `m = 1` this is `pick 0; X; dip 1 { X }` becoming `X; pick 0`. At
/// `X = untuple 3` it is `pick 0; untuple 3; dip 3 { untuple 3 }` becoming
/// `untuple 3; pick 2; pick 2; pick 2` — three copies because the value came
/// apart into three. At `m = 0` there are no picks at all and `X; dip 0 { X }`
/// simply loses its first copy.
///
/// Panic behaviour is preserved rather than merely respected: `X` runs on the
/// copy first, so where the left side panics it does so on exactly the value
/// the right side hands to its single `X`. `print` is excluded, since it is the
/// one instruction for which running twice and running once differ in something
/// other than the stack.
///
/// Measure: node count, since `m` picks and one `X` replace two `X`s and a
/// `pick` only when `m <= 1`; for larger `m` the measure is the number of
/// duplicated computations, which is what the rule exists to reduce.
#[derive(Debug)]
pub(crate) struct DupNatural;

impl Rule for DupNatural {
    fn name(&self) -> &'static str {
        "dup_natural"
    }
    fn width(&self) -> usize {
        3
    }
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [pick, first, framed] = window else {
            return None;
        };
        if !matches!(pick, Node::Op(Instruction::Pick(0))) {
            return None;
        }
        // Running it twice has to mean what running it once means.
        if matches!(first, Node::Op(Instruction::Print)) {
            return None;
        }

        // Two orientations, because `sink` decides which one you get.
        //
        // Written by hand the shape is `pick 0; X; dip m { X }`: the copy is
        // consumed on top and the original is reached under the `m` results.
        // But once anything has hoisted the second occurrence out of a branch,
        // `sink` walks it left as far as the arithmetic allows — which is past
        // the first occurrence, landing on `pick 0; dip 1 { X }; X`, where the
        // *original* is consumed under the single copy and the copy on top.
        // Both compute `X` twice on the same value and both collapse the same
        // way, so the rule takes either rather than making a caller stop `sink`
        // at exactly the right moment.
        let (plain, framed) = match (first, framed) {
            (Node::Dip { depth: 1, body, .. }, second) => (second, &body[..]),
            (first, Node::Dip { depth, body, .. }) => {
                // The second occurrence has to sit exactly over what the first
                // one produced.
                let (_, m) = node_arity(prog, first)?;
                if m != *depth as i64 {
                    return None;
                }
                (first, &body[..])
            }
            _ => return None,
        };

        // Whichever way round, it has to be the same computation.
        let [inner] = framed else { return None };
        if !same_effect(plain, inner) || matches!(plain, Node::Op(Instruction::Print)) {
            return None;
        }
        let (n, m) = node_arity(prog, plain)?;
        if n != 1 {
            return None;
        }

        let mut out = vec![plain.clone()];
        // `m` copies, each reaching back past the ones already made.
        let reach = usize::try_from(m - 1).ok();
        if let Some(d) = reach {
            out.extend((0..m).map(|_| Node::Op(Instruction::Pick(d))));
        }
        Some(out)
    }
}

/// `pick 0 ; untuple n` becomes `untuple n ; (pick (n-1))^n ; dip n { tuple n }`.
///
/// Instead of keeping the value and taking a copy apart, take the value apart
/// and **rebuild** the copy. Both sides leave `[x, e(n-1) .. e0]` and both panic
/// on exactly the inputs where `x` is not an n-tuple, so the rewrite asks
/// nothing of `x` — but it changes what the surviving `x` *is*, from an opaque
/// value into a `tuple n` applied to parts that are now on the stack.
///
/// That is the whole point, and it is worth being clear that it is a proof
/// technique rather than a simplification. The problem it addresses is that a
/// predicate consumes a copy while the real work destructures the original, with
/// a branch in between that nothing can hoist across, because `untuple` is
/// partial and hoisting it would run it on the path that did not take the arm.
/// Knowing that path is safe needs a fact several branches out — but no fact is
/// needed if the value arrives at the branch *already built*: `tuple n` is
/// total, so [`UnfactorBranch`] may push it into both arms, and in the arm that
/// takes it apart again [`CancelTuple`] removes both. A window that sees
/// `tuple n; untuple n` needs to know nothing about where the value came from.
/// **The construction is the proof.**
///
/// The rebuild is framed as `dip n { tuple n }` rather than emitted with rolls
/// for two reasons: it rebuilds the lower copy where it already sits, and it
/// arrives in the form [`Float`] can move, which is what delivers it to the
/// branch.
///
/// This makes the term bigger and belongs in no normalizing pass. Aiming it is
/// a caller's job.
///
/// Measure: the number of `pick 0; untuple n` adjacencies, which this strictly
/// decreases — its own output contains none.
#[derive(Debug)]
pub(crate) struct RebuildCopy;

impl Rule for RebuildCopy {
    fn name(&self) -> &'static str {
        "rebuild_copy"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Op(Instruction::Pick(0)), Node::Op(Instruction::Untuple(n))] = window else {
            return None;
        };
        // A 0-tuple has no parts to share, so there would be nothing to gain.
        if *n == 0 {
            return None;
        }

        let mut out = vec![Node::Op(Instruction::Untuple(*n))];
        // Copy all `n` parts, each reaching back past the copies already made.
        out.extend((0..*n).map(|_| Node::Op(Instruction::Pick(*n - 1))));
        // Rebuild the lower copy in place, under the parts just copied.
        out.push(Node::Dip {
            depth: *n,
            origins: Vec::new(),
            body: vec![Node::Op(Instruction::Tuple(*n))],
        });
        Some(out)
    }
}

/// `dip 1 { X } ; branch { A } { B }` becomes `branch { X; A } { X; B }`.
///
/// The exact inverse of [`FactorBranch`], and sound for the reason that rule is:
/// the dip hides the condition, so `X` runs on the values below it either way,
/// and running it once before the split is running it once on whichever side
/// the split takes.
///
/// It duplicates on purpose, the way [`DistributeBranch`] does, and for the same
/// reason — a rule that only holds inside an arm cannot see anything outside
/// one. Note that the reverse direction, hoisting an `X` *out* of a single arm,
/// is **not** available and is not merely missing: it would run `X` on the path
/// that did not take that arm, and where `X` is partial — `untuple n` is — that
/// invents a panic the original did not have.
///
/// Never put this and `factor_branch` in one `repeat`; they are inverses in the
/// same way `collapse` and `expand` are.
///
/// Measure: none. It grows the term, and its termination is the caller's
/// problem, which is what `repeat_n` and `once` are for.
#[derive(Debug)]
pub(crate) struct UnfactorBranch;

impl Rule for UnfactorBranch {
    fn name(&self) -> &'static str {
        "unfactor_branch"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Dip { depth: 1, body, .. }, Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        }] = window
        else {
            return None;
        };
        if body.is_empty() {
            // `noop` removes an empty dip; pushing nothing into both arms would
            // report a change without making one.
            return None;
        }

        let prefixed = |arm: &Vec<Node>| {
            let mut out = body.clone();
            out.extend(arm.iter().cloned());
            out
        };
        Some(vec![Node::Branch {
            then_origin: then_origin.clone(),
            then_body: prefixed(then_body),
            else_origin: else_origin.clone(),
            else_body: prefixed(else_body),
        }])
    }
}

/// `tuple n ; untuple n` becomes nothing.
///
/// Building a tuple and immediately taking it apart returns the stack to
/// exactly where it started, and `untuple n` cannot reject what `tuple n` just
/// built. The converse — `untuple n; tuple n` — is *not* a no-op and is not
/// included: `untuple` is the instruction that checks the shape, so removing
/// the pair would accept values the original rejected.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct CancelTuple;

impl Rule for CancelTuple {
    fn name(&self) -> &'static str {
        "cancel_tuple"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [Node::Op(Instruction::Tuple(n)), Node::Op(Instruction::Untuple(m))] = window else {
            return None;
        };
        (n == m).then(Vec::new)
    }
}
