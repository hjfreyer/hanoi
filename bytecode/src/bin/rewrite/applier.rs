//! Applying a rewrite script, mechanically.
//!
//! This is the only code in the tool that changes a tree. A live run and a
//! replay go through it alike, which is what makes a script a faithful record
//! of a derivation rather than a log written alongside one.
//!
//! Applying a step is deliberately not a search. The equation regenerates the
//! side it expects to find, the window is compared against it, and anything
//! short of an exact match — by effect; provenance is not part of a term's
//! identity — is a failure rather than an invitation to look elsewhere. A
//! script that no longer fits its program says so at the step that stopped
//! fitting.
//!
//! Nothing here trusts the script. Side conditions are re-checked against the
//! library on every application (see [`Rule2::check`]), so a step whose
//! arguments claim an arity the library does not give is refused no matter how
//! it came to be written.

use crate::arity::seq_arity;
use crate::ir::{Node, Selector, child_seq, expand_call, same_effect_seq, sketch};
use crate::location::{Location, selector_name};
use crate::program::Program;
use crate::rule2::{Direction, SideCondition, Step, StepKind};

/// What a step did to the sequence it landed in.
///
/// The counts are what a driver needs to know where to carry on scanning; the
/// applier itself has no opinion about that.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SpliceInfo {
    pub(crate) removed: usize,
    pub(crate) inserted: usize,
}

/// Why a step could not be applied.
///
/// The context is the same for every cause — which step, which rule, which way
/// round, and where — so it is carried once here rather than repeated in each
/// variant.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ApplyError {
    pub(crate) step: usize,
    pub(crate) rule: &'static str,
    pub(crate) dir: Direction,
    pub(crate) loc: Location,
    pub(crate) cause: Cause,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Cause {
    /// The descent named a node that is not there.
    PathIndex {
        depth: usize,
        index: usize,
        len: usize,
    },
    /// The descent asked for a kind of child the node does not have — a `then`
    /// arm of a dip, say.
    PathKind {
        depth: usize,
        selector: Selector,
        found: String,
    },
    /// The window runs off the end of the sequence it starts in.
    WindowRange { at: usize, need: usize, len: usize },
    /// The window is there but is not what the equation says it should be.
    WindowMismatch { expected: String, found: String },
    /// The arguments do not satisfy the equation.
    SideCondition(SideCondition),
    /// `--check`: the replacement does not leave the stack as the window did.
    NetChanged {
        before: Option<i64>,
        after: Option<i64>,
    },
}

impl std::fmt::Display for ApplyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "step {} ({} {} {}): ",
            self.step,
            self.rule,
            self.dir.arrow(),
            self.loc
        )?;
        match &self.cause {
            Cause::PathIndex { depth, index, len } => write!(
                f,
                "the path turns at node {} on the way down (leg {}), but that \
                 sequence holds {}",
                index, depth, len
            ),
            Cause::PathKind {
                depth,
                selector,
                found,
            } => write!(
                f,
                "the path asks for the {} of `{}` (leg {}), which has no such part",
                selector_name(*selector),
                found,
                depth
            ),
            Cause::WindowRange { at, need, len } => write!(
                f,
                "the window wants {} node(s) from @{}, but the sequence holds {}",
                need, at, len
            ),
            Cause::WindowMismatch { expected, found } => write!(
                f,
                "the window does not match the equation.\n  expected: {}\n  found:    {}",
                expected, found
            ),
            Cause::SideCondition(sc) => write!(f, "{}", sc),
            Cause::NetChanged { before, after } => write!(
                f,
                "the replacement changes the net stack effect ({:?} -> {:?})",
                before, after
            ),
        }
    }
}

/// The two sides of a step's equation, source first.
///
/// Source is what must be found in the tree, destination what replaces it —
/// which way round that puts the equation is exactly what [`Direction`] says.
/// An [`StepKind::Unfold`] builds its sides from the library here, so no copy
/// of a sentence's body ever has to travel inside a script.
fn sides(prog: &Program, step: &Step) -> Result<(Vec<Node>, Vec<Node>), SideCondition> {
    let (lhs, rhs) = match &step.kind {
        StepKind::Rule(rule) => {
            rule.check(prog)?;
            (rule.lhs(), rule.rhs())
        }
        StepKind::Unfold { depth, target } => {
            if prog.is_recursive(*target) {
                return Err(SideCondition::RecursiveTarget { target: *target });
            }
            (
                vec![Node::Call {
                    depth: *depth,
                    target: *target,
                }],
                expand_call(prog, *depth, *target),
            )
        }
    };
    Ok(match step.dir {
        Direction::Forward => (lhs, rhs),
        Direction::Reverse => (rhs, lhs),
    })
}

/// Walks a descent to the sequence it names.
fn navigate<'t>(
    tree: &'t mut Vec<Node>,
    descent: &[(usize, Selector)],
) -> Result<&'t mut Vec<Node>, Cause> {
    let mut seq = tree;
    for (depth, (index, sel)) in descent.iter().enumerate() {
        let len = seq.len();
        let Some(node) = seq.get_mut(*index) else {
            return Err(Cause::PathIndex {
                depth,
                index: *index,
                len,
            });
        };
        let found = sketch(std::slice::from_ref(node));
        match child_seq(node, *sel) {
            Some(body) => seq = body,
            None => {
                return Err(Cause::PathKind {
                    depth,
                    selector: *sel,
                    found,
                });
            }
        }
    }
    Ok(seq)
}

/// Net stack effect, which every equation must preserve.
///
/// Deliberately not full arity: annihilating `pick 2; drop` legitimately drops
/// the demand for values that only the pick made, so what a sequence *requires*
/// may fall. What it leaves may not move.
fn net(prog: &Program, nodes: &[Node]) -> Option<i64> {
    let (inputs, outputs) = seq_arity(prog, nodes);
    outputs.map(|o| o - inputs)
}

/// Applies one step, or explains why it does not fit.
///
/// `idx` is the step's place in its script and appears in any error; a step
/// applied on its own can pass 0.
pub(crate) fn apply_step(
    prog: &Program,
    tree: &mut Vec<Node>,
    step: &Step,
    idx: usize,
    check: bool,
) -> Result<SpliceInfo, ApplyError> {
    let fail = |cause: Cause| ApplyError {
        step: idx,
        rule: step.kind.name(),
        dir: step.dir,
        loc: step.loc.clone(),
        cause,
    };

    let (src, dst) = sides(prog, step).map_err(|sc| fail(Cause::SideCondition(sc)))?;

    if check {
        // Learning an arity that was previously unknown stays permissible.
        // Under the global precondition it should not arise — every node has
        // an arity once recursion and panics are excluded — but tolerating it
        // costs nothing and keeps the applier usable on synthetic trees.
        let (before, after) = (net(prog, &src), net(prog, &dst));
        let broke = match (before, after) {
            (Some(a), Some(b)) => a != b,
            (Some(_), None) => true,
            (None, _) => false,
        };
        if broke {
            return Err(fail(Cause::NetChanged { before, after }));
        }
    }

    let seq = navigate(tree, &step.loc.descent).map_err(fail)?;

    let at = step.loc.at;
    let end = at + src.len();
    if end > seq.len() {
        return Err(fail(Cause::WindowRange {
            at,
            need: src.len(),
            len: seq.len(),
        }));
    }

    let window = &seq[at..end];
    if !same_effect_seq(window, &src) {
        return Err(fail(Cause::WindowMismatch {
            expected: sketch(&src),
            found: sketch(window),
        }));
    }

    let info = SpliceInfo {
        removed: src.len(),
        inserted: dst.len(),
    };
    seq.splice(at..end, dst);
    Ok(info)
}

/// What a step would replace, and with what — sketched, for a listing.
///
/// The same two sequences [`apply_step`] works from, so what this shows is what
/// would actually happen rather than a second account of it. `None` when the
/// arguments do not satisfy the equation, which for a recorded step means
/// something has changed underneath it.
pub(crate) fn preview(prog: &Program, step: &Step) -> Option<(String, String)> {
    let (src, dst) = sides(prog, step).ok()?;
    Some((sketch(&src), sketch(&dst)))
}

/// Applies a whole script, in order.
pub(crate) fn apply_script(
    prog: &Program,
    tree: &mut Vec<Node>,
    script: &[Step],
    check: bool,
) -> Result<(), ApplyError> {
    for (idx, step) in script.iter().enumerate() {
        apply_step(prog, tree, step, idx, check)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule2::Rule2;
    use bytecode::{Instruction, Library, Value, assemble};

    fn prog() -> Program<'static> {
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

    fn step(kind: Rule2, dir: Direction, loc: Location) -> Step {
        Step {
            kind: StepKind::Rule(kind),
            dir,
            loc,
        }
    }

    fn collapse(k: usize, j: usize, a: Vec<Node>) -> Rule2 {
        Rule2::Collapse {
            k,
            j,
            a,
            outer: Vec::new(),
            inner: Vec::new(),
        }
    }

    // -- the happy path -----------------------------------------------------

    #[test]
    fn a_step_rewrites_exactly_its_window() {
        let mut tree = vec![
            op(Instruction::Add),
            dip(2, vec![dip(3, vec![op(Instruction::Drop)])]),
            op(Instruction::Not),
        ];
        let s = step(
            collapse(2, 3, vec![op(Instruction::Drop)]),
            Direction::Forward,
            Location::root(1),
        );
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 1,
                inserted: 1
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Add),
                dip(5, vec![op(Instruction::Drop)]),
                op(Instruction::Not),
            ]
        );
    }

    #[test]
    fn a_descent_reaches_inside_a_branch_arm() {
        let mut tree = vec![branch(
            vec![op(Instruction::Not), dip(1, vec![dip(1, Vec::new())])],
            Vec::new(),
        )];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Then)],
                at: 1,
            },
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            tree,
            vec![branch(
                vec![op(Instruction::Not), dip(2, Vec::new())],
                Vec::new()
            )]
        );
    }

    #[test]
    fn a_window_may_be_wider_than_one_node_and_shrink() {
        // `counit` takes two nodes and leaves none.
        let mut tree = vec![
            op(Instruction::Not),
            op(Instruction::Pick(2)),
            op(Instruction::Drop),
            op(Instruction::Add),
        ];
        let s = step(
            Rule2::Counit { d: 2 },
            Direction::Forward,
            Location::root(1),
        );
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 2,
                inserted: 0
            }
        );
        assert_eq!(tree, vec![op(Instruction::Not), op(Instruction::Add)]);
    }

    // -- direction ----------------------------------------------------------

    #[test]
    fn reverse_finds_the_right_hand_side_and_leaves_the_left() {
        let mut tree = vec![dip(5, vec![op(Instruction::Drop)])];
        let s = step(
            collapse(2, 3, vec![op(Instruction::Drop)]),
            Direction::Reverse,
            Location::root(0),
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            tree,
            vec![dip(2, vec![dip(3, vec![op(Instruction::Drop)])])]
        );
    }

    #[test]
    fn forward_then_reverse_is_the_identity_for_every_equation() {
        // The strongest single statement about the lower layer: a step and its
        // opposite leave the tree exactly as they found it — origins included,
        // which is why the equations carry provenance in their arguments.
        let prog = prog();
        for rule in equations() {
            let mut tree = rule.lhs();
            let before = tree.clone();
            let fwd = step(rule.clone(), Direction::Forward, Location::root(0));
            apply_step(&prog, &mut tree, &fwd, 0, true)
                .unwrap_or_else(|e| panic!("{} forward: {}", rule.name(), e));
            assert_ne!(tree, before, "{} changed nothing", rule.name());

            let back = step(rule.clone(), Direction::Reverse, Location::root(0));
            apply_step(&prog, &mut tree, &back, 1, true)
                .unwrap_or_else(|e| panic!("{} reverse: {}", rule.name(), e));
            assert_eq!(tree, before, "{} does not round-trip", rule.name());
        }
    }

    fn equations() -> Vec<Rule2> {
        vec![
            collapse(2, 3, vec![op(Instruction::Add)]),
            Rule2::ElimDip0 {
                a: vec![op(Instruction::Add)],
                origins: vec!["o".to_string()],
            },
            Rule2::Interchange {
                x: op(Instruction::Add),
                framed: dip(2, vec![op(Instruction::Drop)]),
                n: 2,
                m: 2,
            },
            Rule2::Fuse {
                k: 1,
                a: vec![op(Instruction::Add)],
                b: vec![op(Instruction::Drop)],
                a_origins: vec!["a".to_string()],
                b_origins: vec!["b".to_string()],
            },
            Rule2::Hoist {
                k: 1,
                x: vec![op(Instruction::Add)],
                origins: Vec::new(),
                then_arm: vec![op(Instruction::Drop)],
                else_arm: vec![op(Instruction::Not)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule2::Distribute {
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Add)],
                suffix: vec![op(Instruction::Drop)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule2::FoldBranch {
                c: Value::Bool(true),
                then_arm: vec![op(Instruction::Add)],
                else_arm: vec![op(Instruction::Add)],
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule2::Eval {
                op: Instruction::And,
                inputs: vec![Value::Bool(true), Value::Bool(false)],
            },
            Rule2::Annihilate {
                x: op(Instruction::Add),
                n: 2,
                m: 2,
            },
            Rule2::Counit { d: 3 },
            Rule2::CopyConst { c: Value::Int(7) },
            Rule2::CopyAssoc { d: 2 },
            Rule2::CancelTuple { n: 3 },
        ]
    }

    // -- every way a step can fail ------------------------------------------

    #[test]
    fn a_descent_past_the_end_is_refused() {
        let mut tree = vec![op(Instruction::Add)];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(4, Selector::Body)],
                at: 0,
            },
        );
        assert!(matches!(
            apply_step(&prog(), &mut tree, &s, 3, false)
                .unwrap_err()
                .cause,
            Cause::PathIndex {
                depth: 0,
                index: 4,
                len: 1
            }
        ));
    }

    #[test]
    fn a_descent_into_a_part_the_node_does_not_have_is_refused() {
        // A dip has a body, not a then arm.
        let mut tree = vec![dip(1, vec![op(Instruction::Add)])];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Then)],
                at: 0,
            },
        );
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        assert!(matches!(
            err.cause,
            Cause::PathKind {
                selector: Selector::Then,
                ..
            }
        ));
        assert!(err.to_string().contains("no such part"));
    }

    #[test]
    fn a_window_running_off_the_end_is_refused() {
        let mut tree = vec![op(Instruction::Pick(0))];
        let s = step(
            Rule2::Counit { d: 0 },
            Direction::Forward,
            Location::root(0),
        );
        assert!(matches!(
            apply_step(&prog(), &mut tree, &s, 0, false)
                .unwrap_err()
                .cause,
            Cause::WindowRange {
                at: 0,
                need: 2,
                len: 1
            }
        ));
    }

    #[test]
    fn a_window_that_is_not_what_the_equation_says_is_refused() {
        let mut tree = vec![op(Instruction::Pick(0)), op(Instruction::Add)];
        let s = step(
            Rule2::Counit { d: 0 },
            Direction::Forward,
            Location::root(0),
        );
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        let Cause::WindowMismatch { expected, found } = &err.cause else {
            panic!("expected a mismatch, got {:?}", err.cause)
        };
        assert!(expected.contains("drop"), "{}", expected);
        assert!(found.contains("add"), "{}", found);
    }

    #[test]
    fn a_fabricated_arity_is_refused_even_though_the_window_fits() {
        // The window really does read `add ; dip 1 { }`. What the step claims
        // about `add` is what the library disagrees with, and that is enough.
        let mut tree = vec![op(Instruction::Add), dip(1, Vec::new())];
        let s = step(
            Rule2::Interchange {
                x: op(Instruction::Add),
                framed: dip(1, Vec::new()),
                n: 1,
                m: 1,
            },
            Direction::Forward,
            Location::root(0),
        );
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        assert!(matches!(
            err.cause,
            Cause::SideCondition(SideCondition::ClaimedArityMismatch { .. })
        ));
        // And the tree is untouched.
        assert_eq!(tree, vec![op(Instruction::Add), dip(1, Vec::new())]);
    }

    #[test]
    fn a_failed_step_leaves_the_tree_alone() {
        let before = vec![op(Instruction::Pick(0)), op(Instruction::Add)];
        let mut tree = before.clone();
        let s = step(
            Rule2::Counit { d: 0 },
            Direction::Forward,
            Location::root(0),
        );
        assert!(apply_step(&prog(), &mut tree, &s, 0, false).is_err());
        assert_eq!(tree, before);
    }

    #[test]
    fn an_equation_with_an_empty_side_is_placed_by_its_location_alone() {
        // `counit` backwards introduces a copy-and-discard where there was
        // nothing. An empty source window matches at every offset, so the
        // location is the *only* thing deciding where the work lands — which
        // is precisely what a script is for, and why introducing rules need
        // addressing to be exact.
        let mut tree = vec![op(Instruction::Not), op(Instruction::Add)];
        let s = step(
            Rule2::Counit { d: 0 },
            Direction::Reverse,
            Location::root(1),
        );
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 0,
                inserted: 2
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Not),
                op(Instruction::Pick(0)),
                op(Instruction::Drop),
                op(Instruction::Add),
            ]
        );
    }

    #[test]
    fn vacuous_is_derivable_from_annihilate_and_counit() {
        // Is `vacuous` an axiom, or a lemma? Run the derivation and find out.
        //
        //   ε
        //     counit(n-1) backwards, n times, each inside the last  -> pick^n drop^n
        //     annihilate backwards on the drops                     -> pick^n X drop^m
        //
        // If this reproduces `vacuous`'s left-hand side exactly then the
        // equation is a consequence of two others and does not earn a place
        // among the axioms.
        for (x, n, m) in [
            (op(Instruction::Add), 2usize, 2usize),
            (op(Instruction::Untuple(2)), 1, 3),
            (op(Instruction::Not), 1, 1),
        ] {
            let mut script: Vec<Step> = (0..n)
                .map(|i| {
                    step(
                        Rule2::Counit { d: n - 1 },
                        Direction::Reverse,
                        Location::root(i),
                    )
                })
                .collect();
            script.push(step(
                Rule2::Annihilate { x: x.clone(), n, m },
                Direction::Reverse,
                Location::root(n),
            ));

            let mut tree: Vec<Node> = Vec::new();
            apply_script(&prog(), &mut tree, &script, true)
                .unwrap_or_else(|e| panic!("deriving vacuous for {:?}: {}", x, e));

            let mut expected = crate::rule2::tests::copies(n);
            expected.push(x.clone());
            expected.extend(std::iter::repeat_n(op(Instruction::Drop), m));
            assert_eq!(
                tree, expected,
                "the derivation did not reproduce vacuous for {:?}",
                x
            );

            // And forwards, deleting the whole thing again: the derivation is
            // reversible step for step, which is what makes it a lemma rather
            // than a one-way trick.
            let back: Vec<Step> = script
                .iter()
                .rev()
                .map(|s| Step {
                    dir: s.dir.flipped(),
                    ..s.clone()
                })
                .collect();
            apply_script(&prog(), &mut tree, &back, true)
                .unwrap_or_else(|e| panic!("undoing vacuous for {:?}: {}", x, e));
            assert_eq!(tree, Vec::new(), "vacuous did not undo for {:?}", x);
        }
    }

    // -- provenance is not identity -----------------------------------------

    #[test]
    fn a_window_matches_by_effect_not_by_where_its_code_came_from() {
        // Phase 4 gives every inline block a fresh label, so two identical
        // blocks never share provenance. A step written against one has to fit
        // the other.
        let mut tree = vec![Node::Dip {
            depth: 0,
            origins: vec!["#12 somewhere".to_string()],
            body: vec![op(Instruction::Add)],
        }];
        let s = step(
            Rule2::ElimDip0 {
                a: vec![op(Instruction::Add)],
                origins: Vec::new(),
            },
            Direction::Forward,
            Location::root(0),
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![op(Instruction::Add)]);
    }

    // -- unfold -------------------------------------------------------------

    fn library() -> &'static Library {
        Box::leak(Box::new(
            assemble(
                r#"
                sentence pushy { push 7 }
                sentence pair { push 1 push 2 }
                #[recursive] sentence loops { jump loops }
                "#,
            )
            .unwrap(),
        ))
    }

    fn named(library: &Library, name: &str) -> bytecode::SentenceIndex {
        library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(i, _)| i)
            .unwrap_or_else(|| panic!("no sentence '{}'", name))
    }

    #[test]
    fn unfold_takes_its_body_from_the_library_not_from_the_script() {
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");

        let mut tree = vec![Node::Call {
            depth: 0,
            target: pushy,
        }];
        let s = Step {
            kind: StepKind::Unfold {
                depth: 0,
                target: pushy,
            },
            dir: Direction::Forward,
            loc: Location::root(0),
        };
        apply_step(&prog, &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![op(Instruction::Push(Value::Int(7)))]);

        // And backwards: recognizing the body and folding it into the call.
        let back = Step {
            dir: Direction::Reverse,
            ..s
        };
        apply_step(&prog, &mut tree, &back, 1, true).unwrap();
        assert_eq!(
            tree,
            vec![Node::Call {
                depth: 0,
                target: pushy
            }]
        );
    }

    #[test]
    fn unfold_produces_a_body_the_step_never_carried() {
        // One call node becomes two. The step names only the target, so those
        // nodes can have come from nowhere but the library — which is the whole
        // reason unfolding is not a [`Rule2`].
        let library = library();
        let prog = Program::new(library);
        let pair = named(library, "pair");
        let mut tree = vec![Node::Call {
            depth: 0,
            target: pair,
        }];
        let info = apply_step(
            &prog,
            &mut tree,
            &Step {
                kind: StepKind::Unfold {
                    depth: 0,
                    target: pair,
                },
                dir: Direction::Forward,
                loc: Location::root(0),
            },
            0,
            true,
        )
        .unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 1,
                inserted: 2
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Push(Value::Int(1))),
                op(Instruction::Push(Value::Int(2))),
            ]
        );
    }

    #[test]
    fn unfolding_a_deeper_call_keeps_its_frame() {
        // At depth 0 the body splices into the caller's own sequence; deeper,
        // the frame is what the instruction means and has to stay.
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");
        let mut tree = vec![Node::Call {
            depth: 2,
            target: pushy,
        }];
        apply_step(
            &prog,
            &mut tree,
            &Step {
                kind: StepKind::Unfold {
                    depth: 2,
                    target: pushy,
                },
                dir: Direction::Forward,
                loc: Location::root(0),
            },
            0,
            true,
        )
        .unwrap();
        let [Node::Dip { depth, body, .. }] = &tree[..] else {
            panic!("expected one dip, got {:?}", tree)
        };
        assert_eq!(*depth, 2);
        assert_eq!(body, &vec![op(Instruction::Push(Value::Int(7)))]);
    }

    #[test]
    fn unfold_refuses_a_recursive_target() {
        let library = library();
        let prog = Program::new(library);
        let loops = named(library, "loops");
        let mut tree = vec![Node::Call {
            depth: 0,
            target: loops,
        }];
        let s = Step {
            kind: StepKind::Unfold {
                depth: 0,
                target: loops,
            },
            dir: Direction::Forward,
            loc: Location::root(0),
        };
        assert!(matches!(
            apply_step(&prog, &mut tree, &s, 0, false)
                .unwrap_err()
                .cause,
            Cause::SideCondition(SideCondition::RecursiveTarget { .. })
        ));
    }

    #[test]
    fn folding_a_body_that_is_not_the_target_is_refused() {
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");
        let mut tree = vec![op(Instruction::Drop)];
        let s = Step {
            kind: StepKind::Unfold {
                depth: 0,
                target: pushy,
            },
            dir: Direction::Reverse,
            loc: Location::root(0),
        };
        assert!(matches!(
            apply_step(&prog, &mut tree, &s, 0, false)
                .unwrap_err()
                .cause,
            Cause::WindowMismatch { .. }
        ));
    }

    // -- scripts ------------------------------------------------------------

    #[test]
    fn a_script_runs_its_steps_in_order() {
        // Two collapses, the second only possible because the first ran.
        let mut tree = vec![dip(1, vec![dip(1, vec![dip(1, Vec::new())])])];
        let script = vec![
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location {
                    descent: vec![(0, Selector::Body)],
                    at: 0,
                },
            ),
            step(
                collapse(1, 2, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
        ];
        apply_script(&prog(), &mut tree, &script, true).unwrap();
        assert_eq!(tree, vec![dip(3, Vec::new())]);
    }

    #[test]
    fn a_script_reports_which_step_stopped_fitting() {
        let mut tree = vec![dip(1, vec![dip(1, Vec::new())])];
        let script = vec![
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
            // Now `dip 2 { }`, so this one cannot fire.
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
        ];
        let err = apply_script(&prog(), &mut tree, &script, true).unwrap_err();
        assert_eq!(err.step, 1);
        assert!(matches!(err.cause, Cause::WindowMismatch { .. }));
    }

    #[test]
    fn the_factoring_derivation_runs_as_a_script_of_three_laws() {
        // What `factor_branch` used to do in one motion: hoist the shared
        // prefix `add` out of both arms. Wrap it in a frame in each arm, then
        // read the hoist law backwards.
        let mut tree = vec![branch(
            vec![op(Instruction::Add), op(Instruction::Drop)],
            vec![op(Instruction::Add), op(Instruction::Not)],
        )];
        let wrap = |sel| {
            step(
                Rule2::ElimDip0 {
                    a: vec![op(Instruction::Add)],
                    origins: Vec::new(),
                },
                Direction::Reverse,
                Location {
                    descent: vec![(0, sel)],
                    at: 0,
                },
            )
        };
        let script = vec![
            wrap(Selector::Then),
            wrap(Selector::Else),
            step(
                Rule2::Hoist {
                    k: 0,
                    x: vec![op(Instruction::Add)],
                    origins: Vec::new(),
                    then_arm: vec![op(Instruction::Drop)],
                    else_arm: vec![op(Instruction::Not)],
                    then_origin: "then".to_string(),
                    else_origin: "else".to_string(),
                },
                Direction::Reverse,
                Location::root(0),
            ),
        ];
        apply_script(&prog(), &mut tree, &script, true).unwrap();
        assert_eq!(
            tree,
            vec![
                dip(1, vec![op(Instruction::Add)]),
                branch(vec![op(Instruction::Drop)], vec![op(Instruction::Not)]),
            ]
        );
    }
}
