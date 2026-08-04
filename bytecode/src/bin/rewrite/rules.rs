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

use bytecode::arity::op_arity;
use bytecode::value::numeric_cmp;
use bytecode::{Instruction, Value};

use crate::arity::node_arity;
use crate::ir::{Node, expand_call, same_effect};
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
    &AnnihilateFlagged,
    &BoolIdentity,
    &CancelTuple,
    &Collapse,
    &CopyAssoc,
    &CopyConst,
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
    &SpeculateBranch,
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
        let [
            Node::Dip {
                depth: inner_depth,
                origins: inner_origins,
                body: inner_body,
            },
        ] = &body[..]
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

/// `X ; drop` becomes `drop^n`, where X has arity `(n -> 1)`.
///
/// Computing a value and throwing it away is throwing away the operands
/// instead. That used to be true only of a whitelist — `push` and `pick`
/// cancelled outright, the five `is_*` predicates left the drop behind, and
/// `add; drop` was deliberately *not* `drop; drop`, because the add still
/// rejected non-numeric operands and cancelling it would have discarded that
/// check. Now that every data operation is total there is no check to discard,
/// and one arity condition covers the lot (see `docs/totality.md`).
///
/// Two exceptions, and neither is about panics:
///
/// - `print` leaves one value on top like any other unary operator, but
///   running it and not running it differ in something other than the stack.
/// - `pick d` has arity `(d+1 -> d+2)`, so it is not of this shape at all. It
///   gets its own answer — no drops, since it consumed nothing — which is the
///   counit law of the comonoid [`CopyAssoc`] names.
///
/// `assert` and `assert_eq` fall out on their own: they leave nothing on top,
/// so there is no drop to pair them with, and the rule cannot reach the three
/// instructions that can still fail.
///
/// Measure: non-drop node count. The replacement is all drops, so firing takes
/// one node out of the count even when it puts several in.
#[derive(Debug)]
pub(crate) struct AnnihilateDrop;

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
        let drops = annihilation(prev)?;
        Some(vec![Node::Op(Instruction::Drop); drops])
    }
}

/// `X ; drop ; drop` becomes `drop^n`, where X has arity `(n -> 2)`.
///
/// [`AnnihilateDrop`] read one output; this one reads two, and exists because
/// a **fallible** instruction leaves its flag alongside its value. `add; drop`
/// is no longer an annihilation — it is the old `add`, with the flag thrown
/// away — so what cancels is `add; drop; drop`, which is three nodes and one
/// more than that rule's window.
///
/// It is not only about flags: `pick 0` has arity `(1 -> 2)` and belongs here
/// for the same arithmetic, copying a value only for both copies to go.
///
/// `untuple n` is covered only at `n = 1`, since a wider one leaves `n + 1`
/// values and this window reaches two. That is a bound on the rule rather than
/// a claim about the law.
///
/// Measure: non-`drop` node count, as for [`AnnihilateDrop`].
#[derive(Debug)]
pub(crate) struct AnnihilateFlagged;

impl Rule for AnnihilateFlagged {
    fn name(&self) -> &'static str {
        "annihilate_flagged"
    }
    fn width(&self) -> usize {
        3
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [
            Node::Op(prev),
            Node::Op(Instruction::Drop),
            Node::Op(Instruction::Drop),
        ] = window
        else {
            return None;
        };
        if matches!(prev, Instruction::Print) {
            return None;
        }
        let (n, 2) = op_arity(prev)? else {
            return None;
        };
        Some(vec![Node::Op(Instruction::Drop); usize::try_from(n).ok()?])
    }
}

/// How many drops replace `inst; drop`, or `None` if the pair does not cancel.
fn annihilation(inst: &Instruction) -> Option<usize> {
    match inst {
        // Copying a value and discarding the copy: neither happened.
        Instruction::Pick(_) => Some(0),
        // The one operator for which running twice is not running once.
        Instruction::Print => None,
        // Everything that leaves exactly one value takes its inputs with it.
        // `push` lands here too, at zero drops.
        _ => match op_arity(inst) {
            Some((n, 1)) => usize::try_from(n).ok(),
            _ => None,
        },
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

/// `push c ; branch { A } { B }` becomes the arm `c` selects.
///
/// **Any** literal folds, not only a `Bool`. A branch takes the then arm on
/// `Bool(true)` and the else arm on everything else, so `push 1; branch` is
/// decided just as firmly as `push false; branch` — it goes to the else arm.
/// This used to be restricted to booleans because the VM rejected any other
/// condition and folding would have erased a panic rather than preserved one;
/// with the condition total there is nothing left to erase.
///
/// A *computed* condition still declines, which is the real content of the
/// rule: it folds what is already decided, and a `pick` or an `is_int` is not.
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
            cond,
            Node::Branch {
                then_body,
                else_body,
                ..
            },
        ] = window
        else {
            return None;
        };
        Some(if pushed(cond)?.truthy() {
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
        let Node::Dip { depth: 0, body, .. } = &window[0] else {
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
        // `add` is (2 -> 2), the second output being its success flag: 2 >= 2
        // clears the window, and the same window is 2 - 2 + 2 = 2 deep on the
        // other side.
        let w = [op(Instruction::Add), dip(2, vec![])];
        assert_eq!(
            Sink.rewrite(&prog(), &w),
            Some(vec![dip(2, vec![]), op(Instruction::Add)])
        );
        // One shallower and the dip would be rewriting the flag.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Add), dip(1, vec![])]),
            None
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
        // `untuple 3` is (1 -> 4) -- three elements and a flag -- so a dip
        // hiding only three would be rewriting a slot the untuple just filled.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Untuple(3)), dip(3, vec![])]),
            None
        );
        // Hiding four clears it, and the window is 4 - 4 + 1 = 1 deep before.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Untuple(3)), dip(4, vec![])]),
            Some(vec![dip(1, vec![]), op(Instruction::Untuple(3))])
        );
    }

    #[test]
    fn sink_declines_past_a_panic() {
        // Nothing after a panic runs, so there is no interchange to make.
        assert_eq!(
            Sink.rewrite(&prog(), &[op(Instruction::Panic), dip(9, vec![])]),
            None
        );
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
        assert_eq!(
            Fuse.rewrite(&prog(), &[dip(1, vec![]), dip(2, vec![])]),
            None
        );
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
    fn annihilate_cancels_a_producer_against_its_drop() {
        assert_eq!(
            AnnihilateDrop.rewrite(
                &prog(),
                &[op(Instruction::Push(Value::Int(1))), op(Instruction::Drop)]
            ),
            Some(vec![])
        );
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Pick(3)), op(Instruction::Drop)]),
            Some(vec![])
        );
    }

    #[test]
    fn annihilate_leaves_one_drop_per_input_the_operator_consumed() {
        // `is_int` consumes a value to make the dropped one, so the drop still
        // has to happen — it just takes the input instead.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::IsInt), op(Instruction::Drop)]),
            Some(vec![op(Instruction::Drop)])
        );
        // A two-operand operator leaves two.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Equal), op(Instruction::Drop)]),
            Some(vec![op(Instruction::Drop), op(Instruction::Drop)])
        );
        // And `tuple n` leaves n, which is where the count stops being one or
        // two and the arity has to be looked up rather than remembered.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Tuple(3)), op(Instruction::Drop)]),
            Some(vec![
                op(Instruction::Drop),
                op(Instruction::Drop),
                op(Instruction::Drop)
            ])
        );
    }

    #[test]
    fn annihilate_declines_what_is_not_one_value_on_top() {
        // `untuple 3` leaves three, so the drop takes only one of them.
        assert_eq!(
            AnnihilateDrop.rewrite(
                &prog(),
                &[op(Instruction::Untuple(3)), op(Instruction::Drop)]
            ),
            None
        );
        // `roll 2` leaves the same three values it took, rearranged.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Roll(2)), op(Instruction::Drop)]),
            None
        );
        // `assert` leaves nothing on top, so the three instructions that can
        // still fail are out of this rule's reach on their own terms.
        for inst in [
            Instruction::Assert,
            Instruction::AssertEqual,
            Instruction::Panic,
        ] {
            assert_eq!(
                AnnihilateDrop.rewrite(&prog(), &[op(inst.clone()), op(Instruction::Drop)]),
                None,
                "{:?} should not cancel",
                inst
            );
        }
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
            FoldBranch.rewrite(
                &prog(),
                &[op(Instruction::Push(Value::Bool(false))), arms()]
            ),
            Some(vec![op(Instruction::Push(Value::Int(20)))])
        );
    }

    #[test]
    fn folding_an_empty_arm_leaves_nothing() {
        assert_eq!(
            FoldBranch.rewrite(
                &prog(),
                &[
                    op(Instruction::Push(Value::Bool(true))),
                    branch(vec![], vec![op(Instruction::Add)])
                ]
            ),
            Some(vec![])
        );
    }

    #[test]
    fn any_literal_folds_a_branch_and_only_true_takes_the_then_arm() {
        let arms = || {
            branch(
                vec![op(Instruction::Push(Value::Int(10)))],
                vec![op(Instruction::Push(Value::Int(20)))],
            )
        };
        // A non-boolean condition is decided rather than rejected: it goes to
        // the else arm, along with everything that is not `Bool(true)`.
        for v in [
            Value::Int(1),
            sym(1),
            Value::Tuple(Vec::new()),
            Value::Bool(false),
        ] {
            assert_eq!(
                FoldBranch.rewrite(&prog(), &[push(v.clone()), arms()]),
                Some(vec![op(Instruction::Push(Value::Int(20)))]),
                "{:?} should take the else arm",
                v
            );
        }
        // And a condition that is computed rather than pushed is not constant,
        // which is the part of the rule that was ever really about knowing.
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
                PickDropToRoll.rewrite(
                    &prog(),
                    &[
                        op(Instruction::Pick(2)),
                        dip(depth, vec![op(Instruction::Drop)])
                    ]
                ),
                None,
                "depth {} should not match a pick 2",
                depth
            );
        }
        // And the body has to be a lone drop.
        assert_eq!(
            PickDropToRoll.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    dip(1, vec![op(Instruction::Drop), op(Instruction::Drop)])
                ]
            ),
            None
        );
    }

    #[test]
    fn pick_drop_to_roll_leaves_the_degenerate_case_to_noop() {
        // At d = 0 the answer is `roll 0`, which does nothing — but this rule
        // states one law and lets `noop` state the other.
        assert_eq!(
            PickDropToRoll.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    dip(1, vec![op(Instruction::Drop)])
                ]
            ),
            Some(vec![op(Instruction::Roll(0))])
        );
        assert_eq!(
            NoOp.rewrite(&prog(), &[op(Instruction::Roll(0))]),
            Some(vec![])
        );
    }

    #[test]
    fn noop_removes_an_empty_dip_at_any_depth() {
        assert_eq!(NoOp.rewrite(&prog(), &[dip(0, vec![])]), Some(vec![]));
        assert_eq!(NoOp.rewrite(&prog(), &[dip(3, vec![])]), Some(vec![]));
    }

    #[test]
    fn noop_declines_anything_that_does_something() {
        assert_eq!(NoOp.rewrite(&prog(), &[op(Instruction::Roll(1))]), None);
        assert_eq!(
            NoOp.rewrite(&prog(), &[dip(1, vec![op(Instruction::Add)])]),
            None
        );
        assert_eq!(NoOp.rewrite(&prog(), &[op(Instruction::Drop)]), None);
    }

    #[test]
    fn annihilate_declines_print_and_anything_leaving_a_flag() {
        // `print` is the operator whose second run differs in something other
        // than the stack, and it is still the only *principled* exclusion.
        assert_eq!(
            AnnihilateDrop.rewrite(&prog(), &[op(Instruction::Print), op(Instruction::Drop)]),
            None
        );
        // The total operators cancel as before.
        for inst in [Instruction::Equal, Instruction::And, Instruction::Or] {
            assert_eq!(
                AnnihilateDrop.rewrite(&prog(), &[op(inst.clone()), op(Instruction::Drop)]),
                Some(vec![op(Instruction::Drop), op(Instruction::Drop)]),
                "{:?} should cancel into two drops",
                inst
            );
        }
        // A *fallible* one no longer matches, and this is a reach the flags
        // cost rather than a soundness argument. `add` leaves two values now,
        // so `add; drop` is the old `add` rather than an annihilation -- what
        // cancels is `add; drop; drop`, three nodes, and this rule sees two.
        // `AnnihilateFlagged` is the companion that takes that window.
        for inst in [
            Instruction::Add,
            Instruction::Divide,
            Instruction::SymbolCharAt,
            Instruction::TupleLength,
        ] {
            assert_eq!(
                AnnihilateDrop.rewrite(&prog(), &[op(inst.clone()), op(Instruction::Drop)]),
                None,
                "{:?} leaves a flag, so a lone drop only takes that",
                inst
            );
        }
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
    fn fold_const_evaluates_rather_than_declining() {
        // `push 1; push 2; and` used to be a panic and is now `false`: neither
        // operand is `Bool(true)`, and `and` coerces each separately.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    push(Value::Int(1)),
                    push(Value::Int(2)),
                    op(Instruction::And)
                ]
            ),
            Some(vec![push(Value::Bool(false))])
        );
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    push(Value::Int(1)),
                    push(Value::Bool(true)),
                    op(Instruction::Or)
                ]
            ),
            Some(vec![push(Value::Bool(true))])
        );
        // The comparisons are fallible now, so a fold produces the flag too.
        // A non-numeric pair is not less and not greater, and says so twice.
        for inst in [Instruction::Less, Instruction::Greater] {
            assert_eq!(
                FoldConst.rewrite(&prog(), &[push(sym(1)), push(sym(2)), op(inst.clone())]),
                Some(vec![push(Value::Bool(false)), push(Value::Bool(false))]),
                "{:?} on two symbols",
                inst
            );
        }
        // Two booleans still fold the obvious way.
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
        // And a mixed numeric pair compares, the way the VM does, reporting
        // that it really did compare.
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    push(Value::Int(1)),
                    push(Value::Float(1.5)),
                    op(Instruction::Less)
                ]
            ),
            Some(vec![push(Value::Bool(true)), push(Value::Bool(true))])
        );
    }

    #[test]
    fn fold_const_needs_both_operands_literal() {
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(0)),
                    push(sym(1)),
                    op(Instruction::Equal)
                ]
            ),
            None
        );
    }

    #[test]
    fn fold_const_unary_answers_on_every_literal() {
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(sym(1)), op(Instruction::IsSymbol)]),
            Some(vec![push(Value::Bool(true))])
        );
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(Value::Int(3)), op(Instruction::IsSymbol)]),
            Some(vec![push(Value::Bool(false))])
        );
        // The deliberate oddity, and the reason it is deliberate: a symbol is
        // not `true`, so it is falsy, so `not` answers `true`.
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(sym(1)), op(Instruction::Not)]),
            Some(vec![push(Value::Bool(true))])
        );
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(Value::Bool(true)), op(Instruction::Not)]),
            Some(vec![push(Value::Bool(false))])
        );
        // `tuple_length` is fallible, so folding it produces the flag too --
        // and on a non-tuple it hands the value back rather than inventing a
        // length, which is the "preserve the inputs" rule applied to a literal.
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[push(sym(1)), op(Instruction::TupleLength)]),
            Some(vec![push(sym(1)), push(Value::Bool(false))])
        );
        assert_eq!(
            FoldConstUnary.rewrite(
                &prog(),
                &[
                    push(Value::Tuple(vec![Value::Int(1), Value::Int(2)])),
                    op(Instruction::TupleLength)
                ]
            ),
            Some(vec![push(Value::Int(2)), push(Value::Bool(true))])
        );
        // A computed operand is still not a literal.
        assert_eq!(
            FoldConstUnary.rewrite(&prog(), &[op(Instruction::Pick(0)), op(Instruction::Not)]),
            None
        );
    }

    #[test]
    fn bool_identity_drops_a_unit_and_only_when_the_operand_is_known_boolean() {
        // `is_symbol` answers with a Bool, so `&& true` adds nothing.
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
        // `pick 0` says nothing about the value, so the `and` is still the
        // only thing coercing it and has to stay: on a junk operand it answers
        // `false`, which is not the operand.
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
        // `a && false` is `false` only on the runs where `a` happened at all
        // -- `a` may be an `assert` -- so the operand stays and a `drop` takes
        // its place.
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
            op(Instruction::IsTuple),
            op(Instruction::Pick(0)),
            branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]),
        ];
        assert_eq!(
            RetainCondition.rewrite(&prog(), &w),
            Some(vec![
                op(Instruction::IsTuple),
                branch(
                    vec![push(Value::Bool(true)), op(Instruction::Add)],
                    vec![push(Value::Bool(false)), op(Instruction::Drop)],
                )
            ])
        );
    }

    #[test]
    fn retain_condition_needs_the_copy_to_be_of_the_condition() {
        // `pick 1` copies something else, so the value the arm would see is
        // not the one the branch tested.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[
                    op(Instruction::IsTuple),
                    op(Instruction::Pick(1)),
                    branch(vec![], vec![])
                ]
            ),
            None
        );
        // And with no copy at all there is nothing left on the stack to name.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[
                    op(Instruction::IsTuple),
                    op(Instruction::IsTuple),
                    branch(vec![], vec![])
                ]
            ),
            None
        );
    }

    #[test]
    fn retain_condition_needs_the_condition_to_be_a_boolean() {
        // A branch decides on any value, taking the else arm on anything that
        // is not `Bool(true)`. `pick 0` says nothing about what the value is,
        // so the else arm cannot be told it held `false`.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(3)),
                    op(Instruction::Pick(0)),
                    branch(vec![], vec![])
                ]
            ),
            None
        );
        // A call to a sentence that does return a bool is not enough either:
        // that is a fact about the library, not about this node.
        assert_eq!(
            RetainCondition.rewrite(
                &prog(),
                &[
                    Node::Call {
                        depth: 0,
                        target: bytecode::SentenceIndex::from(0)
                    },
                    op(Instruction::Pick(0)),
                    branch(vec![], vec![])
                ]
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
            op(Instruction::IsTuple),
            op(Instruction::Pick(0)),
            branch(vec![inner.clone()], vec![]),
        ];
        let Some(out) = RetainCondition.rewrite(&prog(), &w) else {
            panic!("expected retain_condition to fire")
        };
        let [_, Node::Branch { then_body, .. }] = &out[..] else {
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
                    vec![
                        op(Instruction::Drop),
                        push(sym(1)),
                        op(Instruction::IsSymbol)
                    ],
                    // The else arm learns only a disequality, which has no
                    // literal form.
                    vec![op(Instruction::Add)],
                ),
            ])
        );
    }

    #[test]
    fn specialize_equal_refines_at_the_depth_the_test_looked() {
        // `pick d; push c; equal` leaves the original `d` deep once the branch
        // has popped the boolean, so the refinement dips to exactly there.
        assert_eq!(
            SpecializeEqual.rewrite(
                &prog(),
                &[
                    op(Instruction::Pick(2)),
                    push(sym(1)),
                    op(Instruction::Equal),
                    branch(vec![op(Instruction::IsSymbol)], vec![]),
                ]
            ),
            Some(vec![
                op(Instruction::Pick(2)),
                push(sym(1)),
                op(Instruction::Equal),
                branch(
                    vec![
                        dip(2, vec![op(Instruction::Drop), push(sym(1))]),
                        op(Instruction::IsSymbol),
                    ],
                    vec![],
                ),
            ])
        );
    }

    #[test]
    fn copy_const_turns_a_pick_back_into_a_literal() {
        // What makes a refinement pay: downstream code reads the refined slot
        // with `pick`, and a `pick` is opaque to every rule that folds
        // literals.
        assert_eq!(
            CopyConst.rewrite(&prog(), &[push(sym(1)), op(Instruction::Pick(0))]),
            Some(vec![push(sym(1)), push(sym(1))])
        );
        // Only the top copy: `pick 1` reads past the literal.
        assert_eq!(
            CopyConst.rewrite(&prog(), &[push(sym(1)), op(Instruction::Pick(1))]),
            None
        );
        // And it composes with folding, which is the whole point.
        let folded = CopyConst
            .rewrite(&prog(), &[push(sym(1)), op(Instruction::Pick(0))])
            .expect("should fire");
        assert_eq!(
            FoldConst.rewrite(
                &prog(),
                &[folded[1].clone(), push(sym(2)), op(Instruction::Equal)]
            ),
            Some(vec![push(Value::Bool(false))]),
            "the recovered literal should decide the comparison"
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
            dip(4, vec![op(Instruction::Untuple(3))]),
        ];
        assert_eq!(
            DupNatural.rewrite(&prog(), &w),
            Some(vec![
                op(Instruction::Untuple(3)),
                op(Instruction::Pick(3)),
                op(Instruction::Pick(3)),
                op(Instruction::Pick(3)),
                op(Instruction::Pick(3)),
            ])
        );
    }

    #[test]
    fn copy_assoc_frames_one_of_the_two_copies() {
        // Holds at every depth, not just 0: the second copy comes from the
        // original instead of from the copy, and they are the same value.
        for d in [0usize, 1, 2, 5] {
            assert_eq!(
                CopyAssoc.rewrite(
                    &prog(),
                    &[op(Instruction::Pick(d)), op(Instruction::Pick(0))]
                ),
                Some(vec![
                    op(Instruction::Pick(d)),
                    dip(1, vec![op(Instruction::Pick(d))]),
                ]),
                "at d = {}",
                d
            );
        }
    }

    #[test]
    fn copy_assoc_needs_the_second_pick_to_be_of_the_copy() {
        // `pick 1` reads past the copy the first pick made, so the two are not
        // copies of one value and the law does not apply.
        assert_eq!(
            CopyAssoc.rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Pick(1))]
            ),
            None
        );
    }

    #[test]
    fn copy_assoc_settles() {
        // Its output holds no `pick d; pick 0`, so `each` terminates.
        let out = CopyAssoc
            .rewrite(
                &prog(),
                &[op(Instruction::Pick(2)), op(Instruction::Pick(0))],
            )
            .expect("should fire");
        for w in out.windows(2) {
            assert_eq!(CopyAssoc.rewrite(&prog(), w), None, "re-fired on {:?}", w);
        }
    }

    #[test]
    fn copy_assoc_is_what_float_cannot_do() {
        // `float` declines this, and correctly: its `j >= n` is sufficient but
        // not necessary, and here the two windows overlap even though the
        // values do not differ. A general rule failing to see a special case is
        // the usual reason a specific law earns its own entry.
        assert_eq!(
            Float.rewrite(
                &prog(),
                &[
                    dip(0, vec![op(Instruction::Pick(0))]),
                    op(Instruction::Pick(0))
                ]
            ),
            None
        );
        // But once `copy_assoc` has framed it at depth 1, `float` carries it.
        assert_eq!(
            Float.rewrite(
                &prog(),
                &[
                    dip(1, vec![op(Instruction::Pick(0))]),
                    op(Instruction::IsTuple)
                ]
            ),
            Some(vec![
                op(Instruction::IsTuple),
                dip(1, vec![op(Instruction::Pick(0))]),
            ])
        );
    }

    #[test]
    fn rebuild_copy_destructures_the_value_and_rebuilds_the_copy() {
        // The guard is `untuple`'s own flag: the then arm rebuilds from parts
        // that really are the value's, and the else arm copies the value
        // `untuple` left in the deepest slot it filled.
        let want = vec![
            op(Instruction::Untuple(3)),
            branch(
                vec![
                    op(Instruction::Pick(2)),
                    op(Instruction::Pick(2)),
                    op(Instruction::Pick(2)),
                    dip(3, vec![op(Instruction::Tuple(3))]),
                    push(Value::Bool(true)),
                ],
                vec![
                    dip(2, vec![op(Instruction::Pick(0))]),
                    push(Value::Bool(false)),
                ],
            ),
        ];
        let Some(got) = RebuildCopy.rewrite(
            &prog(),
            &[op(Instruction::Pick(0)), op(Instruction::Untuple(3))],
        ) else {
            panic!("expected rebuild_copy to fire")
        };
        assert_eq!(shape_of(&got), shape_of(&want));

        // n = 1 is the degenerate but real case: no padding, so the else arm
        // copies in place.
        let want = vec![
            op(Instruction::Untuple(1)),
            branch(
                vec![
                    op(Instruction::Pick(0)),
                    dip(1, vec![op(Instruction::Tuple(1))]),
                    push(Value::Bool(true)),
                ],
                vec![
                    dip(0, vec![op(Instruction::Pick(0))]),
                    push(Value::Bool(false)),
                ],
            ),
        ];
        let Some(got) = RebuildCopy.rewrite(
            &prog(),
            &[op(Instruction::Pick(0)), op(Instruction::Untuple(1))],
        ) else {
            panic!("expected rebuild_copy to fire")
        };
        assert_eq!(shape_of(&got), shape_of(&want));

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
        // Its own output contains no `pick 0; untuple n` -- neither at the top
        // level nor in an arm, which is what the `push ()`s in the else arm buy
        // over restating the input there. So `each` terminates rather than
        // growing the term forever.
        let out = RebuildCopy
            .rewrite(
                &prog(),
                &[op(Instruction::Pick(0)), op(Instruction::Untuple(2))],
            )
            .expect("should fire");
        for nodes in sequences(&out) {
            for w in nodes.windows(2) {
                assert_eq!(RebuildCopy.rewrite(&prog(), w), None, "re-fired on {:?}", w);
            }
        }
    }

    /// Every sequence in a tree: the top level, plus each arm and dip body.
    fn sequences(nodes: &[Node]) -> Vec<Vec<Node>> {
        let mut out = vec![nodes.to_vec()];
        for node in nodes {
            match node {
                Node::Dip { body, .. } => out.extend(sequences(body)),
                Node::Branch {
                    then_body,
                    else_body,
                    ..
                } => {
                    out.extend(sequences(then_body));
                    out.extend(sequences(else_body));
                }
                _ => {}
            }
        }
        out
    }

    /// A tree rendered as text, so a mismatch reads as one.
    fn shape_of(nodes: &[Node]) -> String {
        nodes
            .iter()
            .map(|node| match node {
                Node::Op(i) => format!("{}", i),
                Node::Dip { depth, body, .. } => {
                    format!("dip {} {{ {} }}", depth, shape_of(body))
                }
                Node::Branch {
                    then_body,
                    else_body,
                    ..
                } => format!(
                    "branch {{ {} }} {{ {} }}",
                    shape_of(then_body),
                    shape_of(else_body)
                ),
                Node::Call { depth, target } => format!("call {} #{}", depth, usize::from(*target)),
            })
            .collect::<Vec<_>>()
            .join(" ")
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
                &[
                    dip(1, vec![op(Instruction::Push(Value::Int(1)))]),
                    op(Instruction::Add)
                ]
            ),
            None
        );
        // With the window deep enough, both operands are hidden and it moves.
        assert!(
            Float
                .rewrite(
                    &prog(),
                    &[
                        dip(2, vec![op(Instruction::Push(Value::Int(1)))]),
                        op(Instruction::Add)
                    ]
                )
                .is_some()
        );
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
            dip(4, vec![op(Instruction::Untuple(3))]),
        ];
        let after_sinking = [
            op(Instruction::Pick(0)),
            dip(1, vec![op(Instruction::Untuple(3))]),
            op(Instruction::Untuple(3)),
        ];
        let shared = Some(vec![
            op(Instruction::Untuple(3)),
            op(Instruction::Pick(3)),
            op(Instruction::Pick(3)),
            op(Instruction::Pick(3)),
            op(Instruction::Pick(3)),
        ]);
        assert_eq!(DupNatural.rewrite(&prog(), &hand_written), shared);
        assert_eq!(DupNatural.rewrite(&prog(), &after_sinking), shared);
    }

    #[test]
    fn dup_natural_needs_the_frame_to_match_what_the_first_copy_produced() {
        // `untuple 3` leaves four values -- three elements and a flag -- so
        // the second occurrence has to sit under exactly four. At any other
        // depth the two are not looking at the same thing.
        for depth in [1, 2, 3, 5] {
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
                    dip(4, vec![op(Instruction::Untuple(2))]),
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
    fn unfactor_branch_pushes_a_deeper_window_in_one_shallower() {
        // The case that matters in practice: `float` almost never leaves a
        // computation at exactly depth 1. The branch pops the condition, so
        // the same window is one shallower inside the arm.
        assert_eq!(
            UnfactorBranch.rewrite(
                &prog(),
                &[
                    dip(4, vec![op(Instruction::Tuple(3))]),
                    branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]),
                ]
            ),
            Some(vec![branch(
                vec![
                    dip(3, vec![op(Instruction::Tuple(3))]),
                    op(Instruction::Add)
                ],
                vec![
                    dip(3, vec![op(Instruction::Tuple(3))]),
                    op(Instruction::Drop)
                ],
            )])
        );
    }

    #[test]
    fn unfactor_branch_needs_the_window_to_contain_the_condition() {
        // At depth 0 the dip's block operates on the condition itself, so the
        // branch would be popping something the block could have produced.
        assert_eq!(
            UnfactorBranch.rewrite(
                &prog(),
                &[
                    dip(0, vec![op(Instruction::Tuple(3))]),
                    branch(vec![op(Instruction::Add)], vec![]),
                ]
            ),
            None
        );
    }

    #[test]
    fn speculate_branch_runs_one_arms_head_on_a_copy() {
        // `untuple 3` is (1 -> 3): copy the one operand, untuple the copy, and
        // let the then arm drop the original from under the three results
        // while the else arm drops the three results.
        let w = [branch(
            vec![op(Instruction::Untuple(3)), op(Instruction::Add)],
            vec![op(Instruction::Push(Value::Int(9)))],
        )];
        assert_eq!(
            SpeculateBranch.rewrite(&prog(), &w),
            Some(vec![
                dip(
                    1,
                    vec![op(Instruction::Pick(0)), op(Instruction::Untuple(3))]
                ),
                branch(
                    vec![dip(4, vec![op(Instruction::Drop)]), op(Instruction::Add)],
                    vec![
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Push(Value::Int(9))),
                    ],
                ),
            ])
        );
    }

    #[test]
    fn speculate_branch_reaches_the_else_arm_too() {
        // Same construction mirrored. The then arm opens with a call, whose
        // body this rule will not look into -- otherwise the rule would take
        // that arm, since it prefers the one it meets first.
        let call = Node::Call {
            depth: 0,
            target: bytecode::SentenceIndex::from(0),
        };
        let w = [branch(
            vec![call.clone()],
            vec![op(Instruction::Untuple(2))],
        )];
        assert_eq!(
            SpeculateBranch.rewrite(&prog(), &w),
            Some(vec![
                dip(
                    1,
                    vec![op(Instruction::Pick(0)), op(Instruction::Untuple(2))]
                ),
                branch(
                    vec![
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        call
                    ],
                    vec![dip(3, vec![op(Instruction::Drop)])],
                ),
            ])
        );
    }

    #[test]
    fn speculate_branch_lifts_a_whole_block_not_just_one_op() {
        // What lets a speculation climb out of nested branches: the rule's own
        // output is a dip, so if a dip could not be lifted the second branch
        // out would strand it. `dip 1 { untuple 2 }` is (2 -> 4).
        let w = [branch(
            vec![dip(1, vec![op(Instruction::Untuple(2))])],
            vec![op(Instruction::Push(Value::Int(9)))],
        )];
        assert_eq!(
            SpeculateBranch.rewrite(&prog(), &w),
            Some(vec![
                dip(
                    1,
                    vec![
                        op(Instruction::Pick(1)),
                        op(Instruction::Pick(1)),
                        dip(1, vec![op(Instruction::Untuple(2))]),
                    ]
                ),
                branch(
                    vec![dip(4, vec![op(Instruction::Drop), op(Instruction::Drop)])],
                    vec![
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Push(Value::Int(9))),
                    ],
                ),
            ])
        );
    }

    #[test]
    fn speculate_branch_looks_all_the_way_into_a_block() {
        // A dip qualifies only if its whole body does, however deep. One
        // `assert` anywhere inside is enough to disqualify it, since running
        // the block on the losing path would then fail where the original did
        // not.
        for body in [
            vec![op(Instruction::Assert)],
            vec![op(Instruction::Add), op(Instruction::Assert)],
            vec![dip(1, vec![op(Instruction::Panic)])],
            vec![op(Instruction::Print)],
            // A call is opaque, so a block containing one is too.
            vec![Node::Call {
                depth: 0,
                target: bytecode::SentenceIndex::from(0),
            }],
        ] {
            assert_eq!(
                SpeculateBranch.rewrite(&prog(), &[branch(vec![dip(1, body.clone())], vec![])]),
                None,
                "a block containing {:?} should not be speculated",
                body
            );
        }
    }

    #[test]
    fn speculate_branch_copies_every_operand_a_wider_x_reads() {
        // `add` is (2 -> 2), so both operands are copied and the then arm drops
        // two originals from under the result and its flag.
        let w = [branch(
            vec![op(Instruction::Add)],
            vec![op(Instruction::Push(Value::Int(9)))],
        )];
        assert_eq!(
            SpeculateBranch.rewrite(&prog(), &w),
            Some(vec![
                dip(
                    1,
                    vec![
                        op(Instruction::Pick(1)),
                        op(Instruction::Pick(1)),
                        op(Instruction::Add)
                    ]
                ),
                branch(
                    vec![dip(2, vec![op(Instruction::Drop), op(Instruction::Drop)])],
                    vec![
                        op(Instruction::Drop),
                        op(Instruction::Drop),
                        op(Instruction::Push(Value::Int(9)))
                    ],
                ),
            ])
        );
    }

    #[test]
    fn speculate_branch_declines_what_must_not_run_on_the_losing_path() {
        // Each of these would do something on the path that skipped the arm:
        // print an extra line, or fail where the original did not. The other
        // arm is left empty, since the rule takes whichever arm offers a head
        // and would otherwise fire on that one instead.
        for inst in [
            Instruction::Print,
            Instruction::Assert,
            Instruction::AssertEqual,
            Instruction::Panic,
            // Sound, but excluded to keep the measure honest.
            Instruction::Drop,
        ] {
            assert_eq!(
                SpeculateBranch.rewrite(&prog(), &[branch(vec![op(inst.clone())], vec![])]),
                None,
                "{:?} should not be speculated",
                inst
            );
        }
        // A call may hold one of those several frames down, and this rule does
        // not open callees to find out.
        assert_eq!(
            SpeculateBranch.rewrite(
                &prog(),
                &[branch(
                    vec![Node::Call {
                        depth: 0,
                        target: bytecode::SentenceIndex::from(0)
                    }],
                    vec![]
                )]
            ),
            None
        );
        // And an empty arm has no head to take.
        assert_eq!(
            SpeculateBranch.rewrite(&prog(), &[branch(vec![], vec![])]),
            None
        );
    }

    #[test]
    fn speculate_branch_leaves_a_shared_prefix_to_factor_branch() {
        // `factor_branch` does this case strictly better -- no copies and no
        // drops, because a prefix both arms run needs no speculation.
        let w = [branch(
            vec![op(Instruction::Untuple(3)), op(Instruction::Add)],
            vec![op(Instruction::Untuple(3)), op(Instruction::Drop)],
        )];
        assert_eq!(SpeculateBranch.rewrite(&prog(), &w), None);
        assert!(FactorBranch.rewrite(&prog(), &w).is_some());
    }

    #[test]
    fn speculate_branch_settles() {
        // The measure is non-`drop` Ops inside arms: firing takes one out and
        // puts back only drops and a dip, neither of which it will match.
        let start = branch(
            vec![op(Instruction::Untuple(3)), op(Instruction::Add)],
            vec![op(Instruction::IsInt)],
        );
        let mut nodes = vec![start];
        for round in 0..8 {
            let Some(next) = nodes
                .iter()
                .position(|n| matches!(n, Node::Branch { .. }))
                .and_then(|i| {
                    SpeculateBranch
                        .rewrite(&prog(), &nodes[i..i + 1])
                        .map(|out| (i, out))
                })
            else {
                assert!(round > 0, "expected at least one firing");
                return;
            };
            let (i, out) = next;
            nodes.splice(i..i + 1, out);
        }
        panic!("speculate_branch did not settle: {:?}", nodes);
    }

    #[test]
    fn cancel_tuple_goes_one_way_only() {
        assert_eq!(
            CancelTuple.rewrite(
                &prog(),
                &[op(Instruction::Tuple(2)), op(Instruction::Untuple(2))]
            ),
            // Not nothing: `untuple` cannot fail on what `tuple` just built, so
            // the pair leaves a literal `true` where its flag would be.
            Some(vec![push(Value::Bool(true))])
        );
        // `untuple n; tuple n` is *not* a no-op: it junk-normalizes, mapping
        // every non-n-tuple to `((), ...)`. A real function, and not the
        // identity, so the pair does not come out.
        assert_eq!(
            CancelTuple.rewrite(
                &prog(),
                &[op(Instruction::Untuple(2)), op(Instruction::Tuple(2))]
            ),
            None
        );
        // Mismatched widths junk-normalize rather than cancelling.
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
        let [
            Node::Op(Instruction::Pick(d)),
            Node::Dip { depth, body, .. },
        ] = window
        else {
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
// rules below are the ones that do, and since every data operation is total
// (see `docs/totality.md`) their job is arithmetic rather than negotiation:
// folding a window of literals is running it, and the obligation is to agree
// with the interpreter exactly — on junk as much as on anything else.
//
// What survives is a different constraint, and a sharper one. `truthy` is not
// injective: `and`, `or` and `branch` collapse every non-`true` value onto one
// answer, so a rule that hands a value *back* has to know it was a boolean to
// begin with. That is what `yields_bool` is for, and why `bool_identity` and
// `retain_condition` both take a three-node window.
// ---------------------------------------------------------------------------

/// The literal a node pushes, if it pushes one.
fn pushed(node: &Node) -> Option<&Value> {
    match node {
        Node::Op(Instruction::Push(v)) => Some(v),
        _ => None,
    }
}

/// Whether this node always leaves a `Bool` on top.
///
/// Every instruction listed is total and answers with a `Bool`, so a caller may
/// treat what it produced as a boolean rather than as a value that merely
/// happens to be falsy — which is the difference between `a && true = a` and
/// `a && true = false`, and between an else arm learning `false` and an else
/// arm being told a lie.
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
/// a boolean. `and` no longer rejects anything, but it does *coerce*: on a
/// junk `a` it answers `Bool(false)`, which is a different value from `a` even
/// though it is the same truth. `B` supplying the operand is what licenses the
/// rewrite, which is why the window is three wide — the two-node view
/// `push true; and` cannot tell what the value underneath is.
///
/// This is the shape of what totality did *not* buy. The absorbing cases still
/// go to `B; drop; push c` rather than to `push c`, because `B` may be a
/// `panic` or an `assert`, and `a && false` is only `false` on the runs where
/// `a` happened at all.
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
/// **Folding is evaluation.** Every operator here is a total function, so
/// running it on two known values and pushing the answer is the same program;
/// there is no operand it could have rejected and no check the fold could
/// throw away. What the rule needs is not a licence but an obligation — to
/// agree with the interpreter exactly, on junk as much as on anything else,
/// which is why `and`/`or` go through [`Value::truthy`] and the comparisons
/// through [`numeric_cmp`] rather than through a second reading of the same
/// rules. Both live in `bytecode::value` for that reason.
///
/// So `push 1; push 2; and` folds to `push false` (neither operand is
/// `Bool(true)`), and `push idle; push thirsty; less` folds to `push false`
/// (neither is a number). `equal` folds on any pair, which is what decides
/// `push idle; push thirsty; equal` and collapses a symbol decision tree.
///
/// The arithmetic operators are simply not listed. Adding them would be a
/// straightforward extension now, not a question about semantics.
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
            Instruction::Equal => vec![Value::Bool(a == b)],
            Instruction::And => vec![Value::Bool(a.truthy() && b.truthy())],
            Instruction::Or => vec![Value::Bool(a.truthy() || b.truthy())],
            // The comparisons are fallible, so folding one has to produce the
            // flag as well. Unordered covers both a non-numeric operand and a
            // NaN: neither is a comparison the instruction can claim to have
            // made, so both answer `false, false`.
            Instruction::Greater | Instruction::Less => {
                let want = match inst {
                    Instruction::Greater => std::cmp::Ordering::Greater,
                    _ => std::cmp::Ordering::Less,
                };
                match numeric_cmp(a, b) {
                    Some(ord) => vec![Value::Bool(ord == want), Value::Bool(true)],
                    None => vec![Value::Bool(false), Value::Bool(false)],
                }
            }
            _ => return None,
        };
        Some(
            out.into_iter()
                .map(|v| Node::Op(Instruction::Push(v)))
                .collect(),
        )
    }
}

/// Evaluates a one-operand operator applied to a literal.
///
/// Same story as [`FoldConst`]: these are total functions, so folding is
/// running them. Every case answers on every literal — `not` through
/// [`Value::truthy`], which makes `push sym; not` fold to `push true`, and
/// `tuple_length` to zero on anything that is not a tuple, which is what lets
/// [`RebuildCopy`]'s guard be decided when its subject is a literal.
///
/// `symbol_len` and `negate` are simply not listed, the same way the
/// arithmetic operators are absent from `fold_const`.
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

        let out = match inst {
            Instruction::IsInt => vec![Value::Bool(matches!(a, Value::Int(_)))],
            Instruction::IsBool => vec![Value::Bool(matches!(a, Value::Bool(_)))],
            Instruction::IsFloat => vec![Value::Bool(matches!(a, Value::Float(_)))],
            Instruction::IsSymbol => vec![Value::Bool(matches!(a, Value::Symbol(_)))],
            Instruction::IsTuple => vec![Value::Bool(matches!(a, Value::Tuple(_)))],
            Instruction::Not => vec![Value::Bool(!a.truthy())],
            // Fallible, and with one input and two slots it hands the value
            // back rather than inventing a length for it.
            Instruction::TupleLength => match a {
                Value::Tuple(t) => vec![Value::Int(t.len() as i64), Value::Bool(true)],
                other => vec![other.clone(), Value::Bool(false)],
            },
            _ => return None,
        };
        Some(
            out.into_iter()
                .map(|v| Node::Op(Instruction::Push(v)))
                .collect(),
        )
    }
}

/// `Y ; pick 0 ; branch { A } { B }` becomes
/// `Y ; branch { push true; A } { push false; B }`, where `Y` yields a `Bool`.
///
/// A branch may tell its arms what its condition was. `branch` takes the then
/// arm exactly when the condition is `Bool(true)`, so *if the condition is
/// known to be a boolean at all*, the copy `pick 0` left behind is `true` in
/// one arm and `false` in the other — a literal, which the arm can push for
/// itself.
///
/// The window is three wide because of that "if". A branch decides on any
/// value, taking the else arm on anything that is not literally `Bool(true)`
/// (see `docs/totality.md`), so an else arm may run holding a `42` or a
/// symbol, and telling it the value was `false` would be a lie. [`BoolIdentity`]
/// needs the same three-node view for the same reason and answers it with the
/// same [`yields_bool`] predicate: two nodes cannot tell you what the value
/// underneath is, and the node that produced it can.
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
        3
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [
            y,
            Node::Op(Instruction::Pick(0)),
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
        ] = window
        else {
            return None;
        };
        // Without this the else arm would be told `false` about a value that
        // merely failed to be `true`.
        if !yields_bool(y) {
            return None;
        }

        let arm = |lit: bool, body: &Vec<Node>| {
            let mut out = vec![Node::Op(Instruction::Push(Value::Bool(lit)))];
            out.extend(body.iter().cloned());
            out
        };

        Some(vec![
            y.clone(),
            Node::Branch {
                then_origin: then_origin.clone(),
                then_body: arm(true, then_body),
                else_origin: else_origin.clone(),
                else_body: arm(false, else_body),
            },
        ])
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
        let Node::Op(Instruction::Pick(d)) = pick else {
            return None;
        };
        if !matches!(eq, Node::Op(Instruction::Equal)) {
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

        // Replacing the value the test accepted, wherever the test found it.
        // `pick d; push c; equal` leaves the original `d` deep once the branch
        // has popped the boolean, so the refinement dips to exactly there.
        let refine = |rest: &[Node]| {
            let mut inner = vec![
                Node::Op(Instruction::Drop),
                Node::Op(Instruction::Push(c.clone())),
            ];
            let mut out = if *d == 0 {
                // No frame to keep, and splicing puts the literal where the
                // arm's own rules can reach it.
                std::mem::take(&mut inner)
            } else {
                vec![Node::Dip {
                    depth: *d,
                    origins: Vec::new(),
                    body: inner,
                }]
            };
            out.extend(rest.iter().cloned());
            out
        };

        // Already refined, or an arm that discards the value anyway. See the
        // measure: this is what makes the rule settle.
        let settled = match (*d, then_body.first()) {
            (0, Some(Node::Op(Instruction::Drop))) => true,
            (d, Some(Node::Dip { depth, body, .. })) if d > 0 && *depth == d => {
                matches!(body.first(), Some(Node::Op(Instruction::Drop)))
            }
            _ => false,
        };
        if settled {
            return None;
        }

        let body = refine(then_body);
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
/// `X` runs on the copy first, so where the left side fails — `X` may contain
/// an `assert` — it does so on exactly the value the right side hands to its
/// single `X`. `print` is excluded, since it is the one instruction for which
/// running twice and running once differ in something other than the stack.
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

        // The frame may also carry a `pick 0` of its own, which is what
        // [`SpeculateBranch`] leaves behind: speculating `X` out of one arm has
        // to copy `X`'s operand, because the arm that did *not* want `X` still
        // wants the value. So the law runs under a retained copy —
        //
        //   pick 0; dip 1 { pick 0; X }; X  ==  pick 0; X; (pick (m-1))^m
        //
        // — which is the same statement with `x` surviving on the left of both
        // sides. Without this the sharing stops one step short of closing,
        // since `sink` delivers the speculation in exactly this shape.
        let (retained, inner) = match framed {
            [inner] => (false, inner),
            [Node::Op(Instruction::Pick(0)), inner] => (true, inner),
            _ => return None,
        };
        if !same_effect(plain, inner) || matches!(plain, Node::Op(Instruction::Print)) {
            return None;
        }
        let (n, m) = node_arity(prog, plain)?;
        if n != 1 {
            return None;
        }

        let mut out = Vec::new();
        if retained {
            out.push(Node::Op(Instruction::Pick(0)));
        }
        out.push(plain.clone());
        // `m` copies, each reaching back past the ones already made.
        let reach = usize::try_from(m - 1).ok();
        if let Some(d) = reach {
            out.extend((0..m).map(|_| Node::Op(Instruction::Pick(d))));
        }
        Some(out)
    }
}

/// `pick d ; pick 0` becomes `pick d ; dip 1 { pick d }`.
///
/// **Duplication is coassociative.** Making a third copy from the copy and
/// making it from the original are the same thing, because they are the same
/// value; `Δ;(Δ⊗id) = Δ;(id⊗Δ)` in the notation where `pick` is the comonoid's
/// comultiplication. `annihilate_drop`'s treatment of `pick; drop` is the counit
/// law of the same comonoid, and `pick 0; roll 1` becoming `pick 0` — swapping
/// two copies of one value — would be its cocommutativity.
///
/// What makes it worth having is not simplification: both sides are three nodes
/// and neither is smaller. It is that the right-hand side puts one of the copies
/// **in a frame**, and a framed computation is one [`Float`] can carry. A bare
/// `pick` cannot travel at all, so the copy a downstream rule needs is stranded
/// wherever the source happened to make it.
///
/// `float` declines this move itself, and correctly: its side condition `j >= n`
/// is sufficient but not necessary, and two picks of the same slot commute even
/// though their windows overlap. That the general interchange rule cannot see a
/// special case is the usual reason a specific law earns its own entry.
///
/// Measure: the number of `pick d; pick 0` adjacencies, which this strictly
/// decreases — its own output contains none.
#[derive(Debug)]
pub(crate) struct CopyAssoc;

impl Rule for CopyAssoc {
    fn name(&self) -> &'static str {
        "copy_assoc"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [
            Node::Op(Instruction::Pick(d)),
            Node::Op(Instruction::Pick(0)),
        ] = window
        else {
            return None;
        };
        Some(vec![
            Node::Op(Instruction::Pick(*d)),
            Node::Dip {
                depth: 1,
                origins: Vec::new(),
                body: vec![Node::Op(Instruction::Pick(*d))],
            },
        ])
    }
}

/// `push c ; pick 0` becomes `push c ; push c`.
///
/// Copying a constant is pushing it again — the naturality of duplication over
/// a constant, `Δ ∘ c = c ⊗ c`, and the last member of the comonoid family
/// [`CopyAssoc`] names.
///
/// It is what makes a refinement pay. [`SpecializeEqual`] turns the value a test
/// accepted into a literal, but the code downstream reads that slot with `pick`,
/// and a `pick` is opaque to every rule that folds literals. Rewriting it back
/// into a `push` is what lets `fold_const` see two constants and decide the
/// comparison — which is how one branch of a decision tree rules out the others.
///
/// Measure: the number of `push c; pick 0` adjacencies, which this strictly
/// decreases — its own output contains none.
#[derive(Debug)]
pub(crate) struct CopyConst;

impl Rule for CopyConst {
    fn name(&self) -> &'static str {
        "copy_const"
    }
    fn width(&self) -> usize {
        2
    }
    fn rewrite(&self, _prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let [lit, Node::Op(Instruction::Pick(0))] = window else {
            return None;
        };
        let c = pushed(lit)?;
        Some(vec![
            Node::Op(Instruction::Push(c.clone())),
            Node::Op(Instruction::Push(c.clone())),
        ])
    }
}

/// `pick 0 ; untuple n` becomes, for `n >= 1`,
///
/// ```text
/// untuple n;
/// branch { (pick (n-1))^n; dip n { tuple n }; push true }
///        { dip (n-1) { pick 0 }; push false }
/// ```
///
/// Instead of keeping the value and taking a copy apart, take the value apart
/// and **rebuild** the copy. That changes what the surviving `x` *is*, from an
/// opaque value into a `tuple n` applied to parts that are now on the stack.
///
/// It is a proof technique rather than a simplification. The problem it
/// addresses is that a predicate consumes a copy while the real work
/// destructures the original, with a branch in between that nothing can hoist
/// across. Knowing the hoist is safe needs a fact several branches out — but no
/// fact is needed if the value arrives at the branch *already built*: `tuple n`
/// is total, so [`UnfactorBranch`] may push it into both arms, and in the arm
/// that takes it apart again [`CancelTuple`] removes both. A window that sees
/// `tuple n; untuple n` needs to know nothing about where the value came from.
/// **The construction is the proof.**
///
/// ## Why the branch, and why it is cheap
///
/// The rule used to be the bare equation `pick 0; untuple n` ==
/// `untuple n; (pick (n-1))^n; dip n { tuple n }`, justified by both sides
/// panicking on exactly the inputs where `x` is not an n-tuple. Once the
/// operators became total there was no panic left to agree about, and the two
/// sides visibly differed: the left keeps `x`, the right hands back
/// `untuple n; tuple n` of `x`, which on junk is not `x`. The rule was
/// *relying* on partiality to hide a normalization.
///
/// It briefly needed a `tuple_length; push n; equal` guard to recover. It does
/// not any more: **`untuple n` reports for itself**, so the condition is
/// already on the stack, and the else arm has something to say rather than
/// junk to invent — the value `untuple n` could not take apart is still sitting
/// in the deepest of the slots it filled. Both arms are exact, and neither
/// recomputes anything.
///
/// That is the whole argument for putting the flag on the stack: the guard a
/// rewrite needs is the one the instruction already computed.
///
/// The rebuild is framed as `dip n { tuple n }` rather than emitted with rolls
/// for two reasons: it rebuilds the lower copy where it already sits, and it
/// arrives in the form [`Float`] can move, which is what delivers it to the
/// branch.
///
/// This makes the term bigger and belongs in no normalizing pass. Aiming it is
/// a caller's job — and now more than before, since the payload sits inside an
/// arm and something has to bring the consumer in beside it. That something is
/// [`DistributeBranch`].
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
        let [
            Node::Op(Instruction::Pick(0)),
            Node::Op(Instruction::Untuple(n)),
        ] = window
        else {
            return None;
        };
        // A 0-tuple has no parts to share, so there would be nothing to gain —
        // and the guard below could not tell one from junk anyway.
        if *n == 0 {
            return None;
        }
        let n = *n;

        // Where it worked, the parts really are `x`'s and `tuple n` rebuilds
        // it. Copy all `n`, each pick reaching back past the copies already
        // made, then rebuild the lower copy in place underneath them.
        let mut rebuilt: Vec<Node> = (0..n).map(|_| Node::Op(Instruction::Pick(n - 1))).collect();
        rebuilt.push(Node::Dip {
            depth: n,
            origins: Vec::new(),
            body: vec![Node::Op(Instruction::Tuple(n))],
        });
        rebuilt.push(Node::Op(Instruction::Push(Value::Bool(true))));

        // Where it did not, there is nothing to rebuild: `untuple n` left `x`
        // itself in the deepest of the n slots, so the copy is a copy of that.
        let recovered = vec![
            Node::Dip {
                depth: n - 1,
                origins: Vec::new(),
                body: vec![Node::Op(Instruction::Pick(0))],
            },
            Node::Op(Instruction::Push(Value::Bool(false))),
        ];

        Some(vec![
            Node::Op(Instruction::Untuple(n)),
            Node::Branch {
                then_origin: "came apart".to_string(),
                then_body: rebuilt,
                else_origin: "did not".to_string(),
                else_body: recovered,
            },
        ])
    }
}

/// `dip k { X } ; branch { A } { B }` becomes
/// `branch { dip (k-1) { X }; A } { dip (k-1) { X }; B }`, for `k >= 1`.
///
/// At `k = 1` this is the exact inverse of [`FactorBranch`] — the dip hides
/// exactly the condition, so `X` runs on the values below it either way, and
/// the body splices straight into each arm.
///
/// Deeper windows work the same way and are the case that matters in practice.
/// A `dip k` hides the condition *and* `k - 1` values above whatever `X`
/// touches; the branch pops the condition, so inside the arm the same window is
/// one shallower. Restricting this to `k = 1` would mean a computation could
/// only be pushed into a branch it happened to sit immediately beneath, which
/// is almost never where `float` leaves one.
///
/// It duplicates on purpose, the way [`DistributeBranch`] does, and for the same
/// reason — a rule that only holds inside an arm cannot see anything outside
/// one. Note that the reverse direction, hoisting an `X` *out* of a single arm,
/// is **not** available and is not merely missing: it would run `X` on the path
/// that did not take that arm, and `untuple n` junk-normalizes what it is
/// given, so the other path would go on with a value the original left alone.
/// Totality changed the argument here without changing the conclusion — it used
/// to be that the hoist invented a panic.
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
        let [
            Node::Dip {
                depth,
                origins,
                body,
            },
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
        ] = window
        else {
            return None;
        };
        // The window has to contain the condition, or the branch would be
        // popping something the dip's block could have produced.
        if *depth < 1 {
            return None;
        }
        if body.is_empty() {
            // `noop` removes an empty dip; pushing nothing into both arms would
            // report a change without making one.
            return None;
        }

        let inner = depth - 1;
        let prefixed = |arm: &Vec<Node>| {
            let mut out = if inner == 0 {
                // No frame left to keep, and splicing is what lets the arm's
                // own rules reach what just landed.
                body.clone()
            } else {
                vec![Node::Dip {
                    depth: inner,
                    origins: origins.clone(),
                    body: body.clone(),
                }]
            };
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

/// Hoists an operator out of **one** branch arm, by running it speculatively
/// on a copy and letting each arm discard the half it did not want.
///
/// For `X : n -> m` at the head of the then arm:
///
/// ```text
/// branch { X; A } { B }
///   ==
/// dip 1 { (pick (n-1))^n; X };
/// branch { dip m { drop^n }; A } { drop^m; B }
/// ```
///
/// and symmetrically for the else arm. The `dip 1` is because the condition is
/// still on top and `X` must not be handed it; the `(pick (n-1))^n` copies `X`'s
/// operands in place, the same way [`RebuildCopy`] and [`DupNatural`] do.
///
/// **This is the direction that used to be impossible.** `factor_branch` hoists
/// a prefix only when *both* arms share it, and taking one from a single arm
/// would run it on the path that did not take that arm. While `untuple n` could
/// reject a value, that invented a panic; while its junk was untagged, it
/// junk-normalized a value the other path went on to use. Neither objection
/// survives here, because **the other path never gives up its own values** — the
/// speculation runs on a copy, and the losing arm drops the results and carries
/// on with what it always had. No inverse for `X` is needed, so this asks
/// nothing of `untuple n` that it asks of `add`.
///
/// What it does need is exactly what `docs/totality.md` established:
///
/// - `X` must be **total**, or the speculation invents a failure on the losing
///   path. Every data operation now is, which is what makes the rule possible
///   at all; `assert`, `assert_eq` and `panic` are excluded, and fall out of
///   [`op_arity`] or the match below.
/// - `X` must have **no effect but the stack**, which excludes `print`.
/// - `X` must have a **local arity**, which excludes `Dip`, `Branch` and `Call`
///   nodes. Their bodies may hold an `assert` several frames down, and a
///   window-local rule has no business guessing. `inline` and `flatten_call`
///   are how you make the operator underneath visible, as usual.
///
/// `drop` is excluded too, for the measure rather than for soundness: the rule
/// prepends drops to the arms, and hoisting those again would let it chase its
/// own tail. Hoisting a `drop` is pure loss anyway — there is nothing to its
/// left for it to cancel against that it could not have cancelled against
/// inside the arm.
///
/// It also declines when **both** arms open with the same effect, which is
/// [`FactorBranch`]'s case and which that rule does strictly better: no copies
/// and no drops, because a shared prefix needs no speculation.
///
/// The term gets bigger — n copies and n + m drops to move one node — so this
/// pays only when the hoisted `X` reaches something to its left that cancels
/// it. Aiming it is the search's job, as with `float` and `rebuild_copy`.
///
/// Measure: the number of non-`drop` `Op` nodes inside branch arms. Firing
/// removes exactly one and puts back only drops and a dip, so `each` settles
/// even though the node count grows.
#[derive(Debug)]
pub(crate) struct SpeculateBranch;

/// Whether `node` may be run on a path that would not have run it.
///
/// Total and effect-free, decided syntactically and recursively. A `Dip`
/// qualifies when its whole body does, which is what lets a speculation climb
/// out of nested branches: the rule's own output is a dip, and without this it
/// would strand itself at the next branch out.
///
/// A `Call` never qualifies. Its body may hold an `assert` several frames down,
/// and `inline` is how you make that visible — the same stance [`YieldsBool`]
/// takes towards a call that happens to return a boolean.
///
/// [`YieldsBool`]: yields_bool
fn speculable(node: &Node) -> bool {
    match node {
        Node::Op(inst) => match inst {
            // Running these on the losing path would print something the
            // original did not, or fail where the original did not.
            Instruction::Print | Instruction::Assert | Instruction::AssertEqual => false,
            // Sound to speculate, but excluded so that the rule cannot match
            // what it just emitted. See the measure.
            Instruction::Drop => false,
            // `Panic`, `Dip` and `Branch` have no local arity and stop here.
            _ => op_arity(inst).is_some(),
        },
        // An empty body is `noop`'s business, and hoisting it would report a
        // change without making one.
        Node::Dip { body, .. } => !body.is_empty() && body.iter().all(speculable),
        Node::Branch { .. } | Node::Call { .. } => false,
    }
}

impl Rule for SpeculateBranch {
    fn name(&self) -> &'static str {
        "speculate_branch"
    }
    fn width(&self) -> usize {
        1
    }
    fn rewrite(&self, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = &window[0]
        else {
            return None;
        };

        // A shared prefix is `factor_branch`'s, and it hoists one without
        // paying for any of this.
        if let (Some(a), Some(b)) = (then_body.first(), else_body.first()) {
            if same_effect(a, b) {
                return None;
            }
        }

        // Whichever arm offers a head that may run on the other path.
        fn head(arm: &[Node]) -> Option<&Node> {
            arm.first().filter(|n| speculable(n))
        }
        let (from_then, x) = match head(then_body) {
            Some(x) => (true, x.clone()),
            None => (false, head(else_body)?.clone()),
        };
        let (n, m) = node_arity(prog, &x)?;
        let (n, m) = (usize::try_from(n).ok()?, usize::try_from(m).ok()?);

        // Copy `X`'s operands in place, then run it on the copies. Each pick
        // reaches back past the copies already made, so the block lands in the
        // same order it was read.
        let mut speculated: Vec<Node> =
            (0..n).map(|_| Node::Op(Instruction::Pick(n - 1))).collect();
        speculated.push(x);

        // The arm that asked for `X` keeps its results and drops the originals,
        // which sit underneath them.
        let winner = |rest: &[Node]| {
            let mut out = Vec::new();
            if n > 0 {
                out.push(Node::Dip {
                    depth: m,
                    origins: Vec::new(),
                    body: vec![Node::Op(Instruction::Drop); n],
                });
            }
            out.extend(rest.iter().cloned());
            out
        };
        // The other arm drops the results and goes on with the values it always
        // had. This is the whole reason no inverse is needed.
        let loser = |rest: &[Node]| {
            let mut out = vec![Node::Op(Instruction::Drop); m];
            out.extend(rest.iter().cloned());
            out
        };

        let (then_body, else_body) = if from_then {
            (winner(&then_body[1..]), loser(else_body))
        } else {
            (loser(then_body), winner(&else_body[1..]))
        };

        Some(vec![
            Node::Dip {
                depth: 1,
                origins: Vec::new(),
                body: speculated,
            },
            Node::Branch {
                then_origin: then_origin.clone(),
                then_body,
                else_origin: else_origin.clone(),
                else_body,
            },
        ])
    }
}

/// `tuple n ; untuple n` becomes `push true`.
///
/// Building a tuple and immediately taking it apart returns the stack to
/// exactly where it started — and now says so. `untuple n` cannot fail on
/// something `tuple n` just built, so the flag it leaves is a literal `true`,
/// and that literal is the whole residue of the pair.
///
/// The converse — `untuple n; tuple n` — is still *not* a no-op and still not
/// included. It junk-normalizes, and it now also leaves the flag stranded.
///
/// Measure: node count. Two nodes become one.
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
        let [
            Node::Op(Instruction::Tuple(n)),
            Node::Op(Instruction::Untuple(m)),
        ] = window
        else {
            return None;
        };
        (n == m).then(|| vec![Node::Op(Instruction::Push(Value::Bool(true)))])
    }
}
