//! Tests for the rewrite tool.

use std::collections::HashSet;

use bytecode::{assemble, Instruction, Library, SentenceIndex};
use std::fs;
use std::path::Path;

use crate::arity::{node_arity, seq_arity};
use crate::ir::{build, Node};
use crate::program::Program;
use crate::script::{Definitions, PRELUDE};
use crate::tactic::{apply, Env, Tactic};

/// The prelude tactics, by the name a test refers to them by.
const DIPS: &str = "dips";
const FACTOR: &str = "factoring";
const ANNIHILATE: &str = "annihilate";
const ALL: &str = "all";
const NOTHING: &str = "id";

/// Net stack change, which every rule must preserve exactly.
fn net(prog: &Program, nodes: &[Node]) -> Option<i64> {
    let (inputs, outputs) = seq_arity(prog, nodes);
    outputs.map(|o| o - inputs)
}

fn compile(src: &str) -> Tactic {
    let mut defs = Definitions::new();
    defs.load(PRELUDE)
        .unwrap_or_else(|e| panic!("{}", e.render(PRELUDE)));
    defs.compile(src)
        .unwrap_or_else(|e| panic!("{}", e.render(src)))
}

/// Runs a tactic, with `--check` on: every test therefore also asserts that
/// each rule preserved the net stack effect of the window it rewrote.
fn run(prog: &Program, nodes: Vec<Node>, src: &str) -> Vec<Node> {
    let env = Env::new(prog, 1_000_000, true);
    apply(&compile(src), &env, nodes)
        .unwrap_or_else(|e| panic!("{}", e))
        .into_nodes()
}

/// Assembles `code` and returns a program for it.
///
/// Leaked, so the borrow is `'static` and a test can hand it around without
/// threading a lifetime through every helper. Test libraries are small and the
/// process is short.
fn program_of(code: &str) -> &'static Program<'static> {
    let library: &'static Library = Box::leak(Box::new(assemble(code).unwrap()));
    Box::leak(Box::new(Program::new(library)))
}

/// The first sentence of `code`, inlined, then rewritten by `src`.
///
/// Inlining first because these tests are about rewriting rather than about
/// expansion — `build` itself no longer expands anything, so without this
/// every call would still be a `Call` node.
fn tree_of(code: &str, src: &str) -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(code);
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let body = run(prog, body, &format!("inline_all; {}", src));
    (prog, body)
}

fn tree(code: &str, src: &str) -> Vec<Node> {
    tree_of(code, src).1
}

/// The depth before each instruction of a sequence, entered at its inputs.
fn depths(prog: &Program, nodes: &[Node]) -> Vec<Option<i64>> {
    let mut depth = Some(seq_arity(prog, nodes).0);
    let mut out = Vec::new();
    for node in nodes {
        out.push(depth);
        depth = match (depth, node_arity(prog, node)) {
            (Some(d), Some((n, m))) => Some(d - n + m),
            _ => None,
        };
    }
    out
}

fn shape(nodes: &[Node]) -> Vec<String> {
    nodes
        .iter()
        .map(|node| match node {
            Node::Op(inst) => format!("{}", inst),
            Node::Dip { depth, body, .. } => {
                format!("dip {} {{ {} }}", depth, shape(body).join(" "))
            }
            Node::Branch { .. } => "branch".to_string(),
            Node::Call { depth, target } => format!("call {} #{}", depth, usize::from(*target)),
        })
        .collect()
}

#[test]
fn depth_counts_inputs_once() {
    // Regression: an earlier version read the arity checker's recorded
    // per-instruction size, which already includes the inputs found so far,
    // and added the total back on — reporting `is_tuple` one deeper than it
    // runs.
    let (prog, body) = tree_of(
        r#"
        #[arity(1, 1)]
        sentence probe {
            pick 0
            is_tuple
            and
        }
    "#,
        NOTHING,
    );
    assert_eq!(depths(prog, &body), vec![Some(1), Some(2), Some(2)]);
}

#[test]
fn dip_contributes_only_its_targets_net_change() {
    let (prog, body) = tree_of(
        r#"
        #[arity(3, 1)]
        sentence probe {
            dip 1 { add }
            drop 0
        }
    "#,
        NOTHING,
    );
    assert_eq!(depths(prog, &body), vec![Some(3), Some(2)]);
    // The dip itself takes three and leaves two: two consumed by the add,
    // plus the one it holds out of the way.
    assert_eq!(node_arity(prog, &body[0]), Some((3, 2)));
}

#[test]
fn depth_stops_being_known_after_a_panic() {
    let (prog, body) = tree_of(
        r#"
        #[arity(0, 0)]
        sentence probe {
            push 1
            panic
            push 2
        }
    "#,
        NOTHING,
    );
    assert_eq!(depths(prog, &body), vec![Some(0), Some(1), None]);
}

#[test]
fn factoring_looks_past_provenance() {
    // Both arms open with the same dipped block. They are separate inline
    // sentences, so they carry different labels — but the labels are for
    // the listing, not for deciding what the code does, and the prefix has
    // to factor anyway.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            branch { dip 1 { add } push 1 } { dip 1 { add } push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 1 { dip 1 { add } }", "branch"],
        "the shared dipped prefix should have been hoisted"
    );
}

#[test]
fn a_cycle_has_no_static_arity() {
    let (prog, body) = tree_of(
        r#"
        #[recursive]
        sentence loops {
            push 1
            jump loops
        }
    "#,
        NOTHING,
    );
    assert_eq!(seq_arity(prog, &body).1, None);
}

#[test]
fn dips_sink_past_pushes_and_arithmetic() {
    // The dip starts at the end hiding one value. Moving it past `add`
    // widens it to two operands, and past each push narrows it again, so it
    // arrives at the front hiding nothing at all.
    let (_prog, body) = tree_of(
        r#"
        #[arity(2, 2)]
        sentence probe {
            push 1
            push 2
            add
            dip 1 { add }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 0 { add }", "push 1", "push 2", "add"]
    );
}

#[test]
fn dips_fuse_when_they_meet_at_the_same_depth() {
    let (_prog, body) = tree_of(
        r#"
        #[arity(3, 3)]
        sentence probe {
            dip 1 { pick 0 drop 0 }
            dip 1 { pick 0 drop 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["dip 1 { pick 0 drop pick 0 drop }"]
    );
}

fn tree_unary(code: &str) -> Vec<Node> {
    tree(code, "dips; unary")
}

#[test]
fn a_deep_dip_becomes_a_nest_of_unary_dips() {
    // `untuple 3` leaves three values, so a dip hiding two cannot clear it
    // and stays put — which is what makes this a case where the expansion
    // has something to do.
    let body = tree_unary(
        r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#,
    );
    assert_eq!(
        shape(&body),
        vec!["untuple 3", "dip 1 { dip 1 { add } }"]
    );
}

#[test]
fn expansion_preserves_arity() {
    let code = r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#;
    let (prog, normalized) = tree_of(code, DIPS);
    let unary = tree_unary(code);
    assert_ne!(shape(&normalized), shape(&unary), "expected an expansion");
    assert_eq!(seq_arity(prog, &normalized), seq_arity(prog, &unary));
}

#[test]
fn nested_dips_collapse_and_then_keep_sinking() {
    // Hiding one and then one more is hiding two, and once that is a single
    // dip it sinks past both of the pushes it was reaching over.
    //
    // It stops at `push 2`: by then it has narrowed to `dip 0`, which is a
    // plain call taking its argument off the top — exactly the value that
    // push put there. That is the rule's `k >= m` biting, and it is the
    // point at which the dip has reached the values it actually operates on.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            push 1
            push 2
            push 8
            push 9
            dip 1 { dip 1 { add } }
        }
    "#,
        DIPS,
    );
    assert_eq!(
        shape(&body),
        vec!["push 1", "push 2", "dip 0 { add }", "push 8", "push 9"]
    );
}

#[test]
fn fusing_records_every_origin() {
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            push 1
            push 2
            push 8
            push 9
            dip 1 { dip 1 { add } }
        }
    "#,
        DIPS,
    );

    let origins = body
        .iter()
        .find_map(|node| match node {
            Node::Dip { origins, .. } => Some(origins),
            _ => None,
        })
        .expect("a dip should survive normalization");
    // Both of the sentences that were collapsed together are named, so the
    // listing still says where the merged block came from.
    assert_eq!(origins.len(), 2);
}

#[test]
fn a_dip_stops_at_a_pick_that_reaches_into_it() {
    // `pick 2` reads three deep, so a dip hiding only one value would be
    // rewriting the very slot the pick copies from. It has to stay put.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            pick 2
            dip 1 { pick 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(shape(&body), vec!["pick 2", "dip 1 { pick 0 }"]);
}

#[test]
fn a_dip_sinks_past_a_pick_it_clears() {
    // Same shape, but hiding four values puts the whole pick above the
    // window, so the move is sound.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            pick 2
            dip 4 { pick 0 }
        }
    "#,
        DIPS,
    );
    assert_eq!(shape(&body), vec!["dip 3 { pick 0 }", "pick 2"]);
}

#[test]
fn a_shared_branch_prefix_is_hoisted_under_a_dip() {
    // The `push 7` runs either way, so it can run before the condition is
    // consumed — under a dip, since the condition is still on top.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            branch { push 7 push 1 } { push 7 push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
}

#[test]
fn factoring_takes_the_whole_shared_run() {
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            branch { push 7 is_int push 1 } { push 7 is_int push 2 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 is_int }", "branch"]);
}

#[test]
fn factoring_stops_where_the_arms_diverge() {
    // Both arms also end with `push 5`, but only the prefix is hoistable:
    // what runs before the branch has to run before *both* arms, and the
    // trailing pushes are separated by instructions that differ.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            branch { push 7 push 1 push 5 } { push 7 push 2 push 5 }
        }
    "#,
        FACTOR,
    );
    assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
    let Node::Branch {
        then_body,
        else_body,
        ..
    } = &body[1]
    else {
        panic!("expected a branch")
    };
    assert_eq!(shape(then_body), vec!["push 1", "push 5"]);
    assert_eq!(shape(else_body), vec!["push 2", "push 5"]);
}

#[test]
fn a_push_and_a_drop_cancel() {
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            push 1
            push 2
            drop 0
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    // Cancelling the inner pair exposes the outer one.
    assert!(body.is_empty(), "expected nothing left, got {:?}", shape(&body));
}

#[test]
fn a_pick_and_a_drop_cancel() {
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            pick 1
            drop 0
            add
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["add"]);
}

#[test]
fn a_type_test_leaves_the_drop_behind() {
    // `is_int` consumes a value to make the one being dropped, so the drop
    // still has to happen — it just takes the input instead.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            is_int
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["drop"]);
}

#[test]
fn a_partial_instruction_is_not_annihilated() {
    // `add; drop` is not `drop; drop`: the add still rejects non-numeric
    // operands, and cancelling it would discard that check.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            add
            drop 0
        }
    "#,
        ANNIHILATE,
    );
    assert_eq!(shape(&body), vec!["add", "drop"]);
}

#[test]
fn passes_compose() {
    // Annihilating the push/drop pair leaves `push 7` shared by both arms,
    // which factoring then hoists — neither pass alone gets there.
    let code = r#"
        sentence probe {
            branch { push 7 push 9 drop 0 push 1 } { push 7 push 2 }
        }
    "#;
    assert_eq!(shape(&tree(code, FACTOR)), vec!["dip 1 { push 7 }", "branch"]);

    let both = tree(code, "factoring; annihilate");
    let Node::Branch { then_body, .. } = &both[1] else {
        panic!("expected a branch")
    };
    assert_eq!(shape(&both), vec!["dip 1 { push 7 }", "branch"]);
    assert_eq!(shape(then_body), vec!["push 1"]);
}

/// The rewrites must not change what a sentence does. Arity is the part of
/// that this tool can check for itself, and running it over every sentence
/// in the real corpus exercises far more instruction sequences than the
/// hand-written cases above.
///
/// Two different invariants are at play:
///
/// - Net change is preserved by every pass, exactly.
/// - The *input requirement* is preserved by the dip passes and by
///   factoring, but `--annihilate` may lower it: dropping `pick 2; drop`
///   also drops the demand for three values that only the `pick` made. The
///   rewritten code is defined on strictly more stacks than the original,
///   which is sound — so the bound is one-directional, not an equality.
#[test]
fn rewrites_preserve_arity_across_the_corpus() {
    // Tests run with the package root as the working directory.
    let main = Path::new("../tests/main.hana");
    let code = match fs::read_to_string(main) {
        Ok(code) => code,
        // Not a failure: the crate should still be testable on its own.
        Err(_) => return,
    };
    let library = bytecode::assemble_with_path(&code, main.parent()).unwrap();
    let prog = Program::new(&library);

    let mut checked = 0;
    for (s_idx, _) in library.names.iter_enumerated() {
        // Inline first: `build` expands nothing now, so an un-inlined tree
        // would exercise almost none of the rules.
        let plain = run(
            &prog,
            build(&library, s_idx, &mut HashSet::new()),
            "inline_all",
        );
        let name = || format!("#{} {}", usize::from(s_idx), library.names[s_idx]);

        // The dip tactics and factoring preserve arity outright.
        for tac in [DIPS, FACTOR] {
            let rewritten = run(&prog, plain.clone(), tac);
            assert_eq!(
                seq_arity(&prog, &plain),
                seq_arity(&prog, &rewritten),
                "`{}` changed the arity of {}",
                tac,
                name()
            );
        }

        // Everything together preserves net change, and never asks for
        // more inputs than the original did.
        let all = run(&prog, plain.clone(), ALL);
        assert_eq!(
            net(&prog, &plain),
            net(&prog, &all),
            "net change changed for {}",
            name()
        );
        assert!(
            seq_arity(&prog, &all).0 <= seq_arity(&prog, &plain).0,
            "rewriting raised the input requirement of {}",
            name()
        );

        // Running to a fixpoint has to mean something: a second pass must find
        // nothing left to do. The flags guaranteed this by construction; now
        // that the search is separable from the rules it is worth asserting,
        // since a non-confluent rule set would show up here first.
        let twice = run(&prog, all.clone(), ALL);
        assert_eq!(all, twice, "rewriting {} was not idempotent", name());

        let unary = run(&prog, all.clone(), "unary");
        assert_eq!(
            seq_arity(&prog, &all),
            seq_arity(&prog, &unary),
            "unary expansion changed the arity of {}",
            name()
        );
        assert!(
            unary_only(&unary),
            "{} kept a dip deeper than 1 after expansion",
            name()
        );
        checked += 1;
    }

    assert!(checked > 500, "expected the full corpus, saw {}", checked);
}

/// Whether every dip in the tree hides at most one value.
fn unary_only(nodes: &[Node]) -> bool {
    nodes.iter().all(|node| match node {
        Node::Dip { depth, body, .. } => *depth <= 1 && unary_only(body),
        Node::Branch {
            then_body,
            else_body,
            ..
        } => unary_only(then_body) && unary_only(else_body),
        Node::Op(_) | Node::Call { .. } => true,
    })
}

#[test]
fn normalization_preserves_arity() {
    // The rewrite is supposed to be meaning-preserving; arity is the part
    // of the meaning this tool can check for itself.
    let code = r#"
        sentence probe {
            push 1
            dip 2 { add }
            roll 1
            dip 1 { drop 0 }
            add
        }
    "#;
    let (prog, plain) = tree_of(code, NOTHING);
    let normalized = tree(code, DIPS);
    assert_ne!(shape(&plain), shape(&normalized), "expected some rewriting");
    assert_eq!(seq_arity(prog, &plain), seq_arity(prog, &normalized));
}


// ---------------------------------------------------------------------------
// The tactic algebra
//
// Three-valued outcomes are only useful if the combinators respect them, and
// these are the laws the evaluator relies on. `bu` being total in particular
// is why `repeat` keys on progress rather than on success.
// ---------------------------------------------------------------------------

use crate::tactic::{Outcome, TacticError};

fn sample() -> (&'static Program<'static>, Vec<Node>) {
    tree_of(
        r#"
        #[arity(2, 2)]
        sentence probe {
            push 1
            push 2
            add
            dip 1 { add }
        }
    "#,
        NOTHING,
    )
}

fn outcome(
    prog: &Program,
    src: &str,
    nodes: Vec<Node>,
) -> Result<Outcome, TacticError> {
    apply(&compile(src), &Env::new(prog, 1_000_000, true), nodes)
}

fn never_fails(src: &str) {
    let (prog, nodes) = sample();
    let got = outcome(prog, src, nodes).unwrap();
    assert!(
        !matches!(got, Outcome::Failed(_)),
        "`{}` reported Failed, but must be total",
        src
    );
}

#[test]
fn try_repeat_bu_and_children_are_total() {
    // Each wraps a tactic that fails on this input, and must absorb it.
    never_fails("try(each(annihilate_drop))");
    never_fails("repeat(each(annihilate_drop))");
    never_fails("bu(each(annihilate_drop))");
    never_fails("children(each(annihilate_drop))");
    never_fails("try(fail)");
    never_fails("repeat(fail)");
}

#[test]
fn a_failed_tactic_hands_back_exactly_what_it_got() {
    // The contract Seq and Choice rely on to avoid cloning.
    let (prog, before) = sample();
    let Outcome::Failed(after) = outcome(prog, "fail", before.clone()).unwrap() else {
        panic!("`fail` should fail")
    };
    assert_eq!(before, after);
}

#[test]
fn a_rule_that_matches_nowhere_is_a_no_op_not_a_failure() {
    // There is nothing to annihilate in this sample. Reporting that as failure
    // is what used to make a sequence discard everything before it.
    let (prog, before) = sample();
    let Outcome::Unchanged(after) = outcome(prog, "each(annihilate_drop)", before.clone()).unwrap()
    else {
        panic!("having found no work is not a failure")
    };
    assert_eq!(before, after);
}

// ---------------------------------------------------------------------------
// Selective descent: then, else, body
//
// `children` reaches every child of every node, which is fine for a
// normalizing pass and useless for a targeted one. These are the narrowed
// versions, and the point of them is that a script can open one branch arm
// while leaving the other alone.
// ---------------------------------------------------------------------------

/// A sentence whose two arms each contain a call, plus a call inside a dip.
fn arms() -> &'static str {
    r#"
        #[arity(1, 1)]
        sentence probe {
            pick 0
            is_tuple
            branch { jump left } { jump right }
        }
        #[arity(1, 1)]
        sentence left { push 1 add }
        #[arity(1, 1)]
        sentence right { push 2 add }
    "#
}

/// The `shape` of each branch arm of the first branch in `nodes`.
fn arm_shapes(nodes: &[Node]) -> (Vec<String>, Vec<String>) {
    nodes
        .iter()
        .find_map(|n| match n {
            Node::Branch {
                then_body,
                else_body,
                ..
            } => Some((shape(then_body), shape(else_body))),
            _ => None,
        })
        .expect("expected a branch")
}

/// Builds `arms()` without inlining anything, so the arms still hold calls.
fn unexpanded_arms() -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(arms());
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    (prog, body)
}

#[test]
fn then_and_else_each_reach_one_arm_and_leave_the_other() {
    let (prog, before) = unexpanded_arms();
    let (then_before, else_before) = arm_shapes(&before);

    let opened_then = run(prog, before.clone(), "then(each(inline))");
    let (t, e) = arm_shapes(&opened_then);
    assert_ne!(t, then_before, "`then` should have opened the then arm");
    assert_eq!(e, else_before, "`then` must not touch the else arm");

    let opened_else = run(prog, before, "else(each(inline))");
    let (t, e) = arm_shapes(&opened_else);
    assert_eq!(t, then_before, "`else` must not touch the then arm");
    assert_ne!(e, else_before, "`else` should have opened the else arm");
}

#[test]
fn the_three_selectors_partition_children() {
    // The claim documented in docs/tactics.md: `children(t)` is exactly
    // `then(t); else(t); body(t)`. It only holds because the three decline
    // each other's nodes, so the fixture needs a branch *and* a dip for the
    // test to have any force.
    // `dip 1 { ... }` is an inline block, so `build` spells it out and `body`
    // has a real body to find without anything being expanded first.
    let (prog, before) = tree_of(
        r#"
        #[arity(2, 1)]
        sentence probe {
            pick 0
            is_tuple
            branch { push 1 drop 0 } { push 2 drop 0 }
            dip 1 { jump inner }
            drop 0
        }
        #[arity(1, 1)]
        sentence inner { push 3 drop 0 }
    "#,
        NOTHING,
    );

    let via_children = run(prog, before.clone(), "children(each(annihilate_drop))");
    let via_parts = run(
        prog,
        before.clone(),
        "then(each(annihilate_drop)); else(each(annihilate_drop)); body(each(annihilate_drop))",
    );
    assert_ne!(
        shape(&before),
        shape(&via_children),
        "expected the fixture to have children worth descending into"
    );
    assert_eq!(shape(&via_children), shape(&via_parts));
    assert_eq!(arm_shapes(&via_children), arm_shapes(&via_parts));
}

#[test]
fn body_reaches_a_dip_and_not_a_branch_arm() {
    // `body` is the dip-shaped selector, so it must decline the branch arms
    // that `then`/`else` own — otherwise the three would not partition
    // `children` and a script could not say which it meant.
    let (prog, before) = unexpanded_arms();
    let after = run(prog, before.clone(), "body(each(inline))");
    assert_eq!(
        arm_shapes(&before),
        arm_shapes(&after),
        "`body` must not descend into branch arms"
    );

    let (prog, before) = tree_of(
        r#"
        #[arity(1, 1)]
        sentence probe {
            dip 1 { push 1 drop 0 }
        }
    "#,
        NOTHING,
    );
    let after = run(prog, before.clone(), "body(each(annihilate_drop))");
    assert_ne!(
        shape(&before),
        shape(&after),
        "`body` should have reached inside the dip"
    );
}

#[test]
fn an_inline_block_is_spelled_out_and_a_real_call_is_not() {
    // A block written inline has a SentenceIndex only because the compiler
    // needed somewhere to put it, so there is no call site to open and nothing
    // for the un-expanded listing to name. A `jump` to a real sentence is a
    // different thing and stays closed until asked.
    let prog = program_of(
        r#"
        #[arity(2, 2)]
        sentence probe {
            dip 1 { is_tuple }
            jump named
        }
        #[arity(1, 1)]
        sentence named { push 1 add }
    "#,
    );
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    assert_eq!(
        shape(&body),
        vec!["dip 1 { is_tuple }", "call 0 #1"],
        "the inline block should have a body; the named call should not"
    );
}

#[test]
fn a_recursive_inline_block_stays_a_call() {
    // The same guard branch arms already had: expanding a block that reaches
    // itself would not terminate, and a call is what it becomes at run time.
    let prog = program_of(
        r#"
        #[recursive]
        #[arity(1, 1)]
        sentence loops {
            pick 0
            is_tuple
            branch { dip 0 { jump loops } } { }
        }
    "#,
    );
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    // The point is only that building terminated and left a call behind.
    assert!(
        format!("{:?}", body).contains("Call"),
        "expected the recursive edge to stay a call, got {:?}",
        body
    );
}

#[test]
fn selective_descent_is_total() {
    // Same contract as `children`: a selector that picks out nothing is a
    // no-op, not a failure. `sample()` has no branch at all, so `then`/`else`
    // find nowhere to go.
    never_fails("then(each(annihilate_drop))");
    never_fails("else(each(annihilate_drop))");
    never_fails("body(each(annihilate_drop))");
    never_fails("then(fail)");
}

#[test]
fn selective_descent_breaks_the_staged_inlining_plateau() {
    // The motivating case. `once(inline)` works on one sequence, so staged
    // inlining stops dead once the only remaining calls are inside branch
    // arms — no amount of `repeat_n` gets further, because there is nothing
    // left to find at the level it is looking at.
    let (prog, before) = unexpanded_arms();

    let stalled = run(prog, before.clone(), "repeat_n(9, once(inline))");
    assert_eq!(
        arm_shapes(&before),
        arm_shapes(&stalled),
        "root-level staging cannot reach into arms; that is the plateau"
    );

    let past = run(prog, before.clone(), "repeat_n(9, once(inline)); then(once(inline))");
    assert_ne!(arm_shapes(&before), arm_shapes(&past), "`then` gets past it");
}

#[test]
fn dup_natural_shares_a_predicates_work_with_its_callers() {
    // End to end through the driver, on the idiom the sharing law exists for:
    // a value handed to a check and then taken apart again.
    let (prog, before) = tree_of(
        r#"
        #[arity(1, 6)]
        sentence probe {
            pick 0
            untuple 3
            dip 3 { untuple 3 }
        }
    "#,
        NOTHING,
    );
    let after = run(prog, before.clone(), "each(dup_natural)");
    assert_eq!(
        shape(&after),
        vec!["untuple 3", "pick 2", "pick 2", "pick 2"],
        "one untuple and three copies should replace two untuples"
    );
    // The driver ran with --check on, so the net effect is already known to
    // match; assert the full arity too, since this rule reshapes the stack
    // more than most.
    assert_eq!(seq_arity(prog, &before), seq_arity(prog, &after));
}

#[test]
fn the_sharing_law_cannot_reach_across_a_branch() {
    // Why the direct route does not work — and it still does not.
    //
    // This is the shape every predicate in the corpus actually has: the check
    // consumes a *copy* and the real work destructures the *original*, with a
    // branch in between. `dup_natural` relates the two occurrences only when
    // they are in one sequence, and no rule moves the inner `untuple` out of
    // the arm — hoisting it would run it on the path that did not take the
    // arm, and `untuple` is partial, so that invents a panic.
    //
    // The resolution is not to find such a rule but to stop needing one:
    // `rebuild_copy` makes the value arrive already built, and `tuple n` is
    // total where `untuple n` is not. See
    // `the_whole_derivation_runs_on_the_blocked_shape`.
    let (prog, before) = tree_of(
        r#"
        #[arity(1, 1)]
        sentence probe {
            pick 0
            is_tuple
            branch { untuple 3  drop 0  drop 0 } { drop 0  push true }
        }
    "#,
        NOTHING,
    );
    let after = run(
        prog,
        before.clone(),
        "repeat(bu(each(dup_natural); each(sink); each(collapse); each(flatten_call)))",
    );
    assert_eq!(
        shape(&before),
        shape(&after),
        "nothing in the current rule set relates the two occurrences"
    );
}

/// The rewriting half of the sharing problem, with the one missing fact
/// supplied by hand.
///
/// Both sentences have the shape `emit_does_pre_and_post` has: a check
/// destructures a *copy* and consumes the parts, and the real work
/// destructures the *original*, behind a branch on a condition — here
/// `is_symbol && is_symbol` — that has nothing to do with the tuple's shape.
///
/// They differ in one thing. In `given_the_fact` the else arm also untuples,
/// which is equivalent only because the value really is a 3-tuple at that
/// point. That is precisely the fact no window-local rule can establish, and
/// supplying it is enough: `factor_branch` hoists the shared `untuple`,
/// `sink` walks it back to the first one, and `dup_natural` merges the two.
const SHARING_PROBE: &str = r#"
    #[arity(1, 1)]
    sentence blocked {
        pick 0
        untuple 3
        is_symbol
        dip 1 { is_symbol }
        and
        dip 1 { is_symbol }
        and
        branch { untuple 3  is_symbol  dip 1 { drop 0 }  dip 1 { drop 0 } }
               { drop 0  push true }
    }
    #[arity(1, 1)]
    sentence given_the_fact {
        pick 0
        untuple 3
        is_symbol
        dip 1 { is_symbol }
        and
        dip 1 { is_symbol }
        and
        branch { untuple 3  is_symbol  dip 1 { drop 0 }  dip 1 { drop 0 } }
               { untuple 3  drop 0  drop 0  drop 0  push true }
    }
"#;

/// `factor_branch`, then `sink`, then `dup_natural`.
const SHARE: &str = "repeat(bu(each(factor_branch); each(sink); each(collapse); \
                     each(dup_natural); each(annihilate_drop, noop, pick_drop_to_roll)))";

fn untuples(nodes: &[Node]) -> usize {
    nodes
        .iter()
        .map(|n| match n {
            Node::Op(Instruction::Untuple(_)) => 1,
            Node::Dip { body, .. } => untuples(body),
            Node::Branch {
                then_body,
                else_body,
                ..
            } => untuples(then_body) + untuples(else_body),
            _ => 0,
        })
        .sum()
}

fn probe(name: &str) -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(SHARING_PROBE);
    let idx = prog
        .library()
        .names
        .iter()
        .position(|n| n == name)
        .map(SentenceIndex::from)
        .expect("sentence should exist");
    let body = build(prog.library(), idx, &mut HashSet::new());
    (prog, body)
}

#[test]
fn one_fact_is_all_that_separates_the_two_untuples() {
    let (prog, blocked) = probe("blocked");
    assert_eq!(untuples(&blocked), 2);
    assert_eq!(
        untuples(&run(prog, blocked, SHARE)),
        2,
        "without the fact, the else arm shares nothing and the two stay apart"
    );

    // Three to start with, the extra one being the fact stated by hand in the
    // else arm. `factor_branch` merges the two arms' copies into one hoisted
    // `dip 1 { untuple }`, `sink` walks that back to the check's, and
    // `dup_natural` merges those — leaving a single `untuple` for a value that
    // three separate occurrences used to take apart.
    let (prog, given) = probe("given_the_fact");
    assert_eq!(untuples(&given), 3);
    assert_eq!(
        untuples(&run(prog, given, SHARE)),
        1,
        "with the fact, the existing rules merge them -- nothing else is missing"
    );
}

#[test]
fn a_reconstruction_proves_the_shape_that_an_assertion_would_have_claimed() {
    // The way out of needing the fact at all.
    //
    // `one_fact_is_all_that_separates_the_two_untuples` shows the sharing
    // closes once something establishes that the value is a 3-tuple. Nothing
    // local can establish that — but nothing has to, because the fact is
    // already in the program and is merely being thrown away.
    //
    // Carry the *parts* forward instead of the value, and rebuild the value
    // where it is wanted. `tuple 3` is total, so the rebuild needs no
    // justification; `unfactor_branch` pushes it into both arms because it is
    // total; and in the arm that takes it apart again, `cancel_tuple` removes
    // both. The construction is the proof: a window sees `tuple 3; untuple 3`
    // and needs to know nothing about where the value came from.
    let (prog, before) = tree_of(
        r#"
        #[arity(1, 1)]
        sentence via_reconstruct {
            untuple 3
            pick 2  pick 2  pick 2
            is_symbol
            dip 1 { is_symbol }
            and
            dip 1 { is_symbol }
            and
            dip 1 { tuple 3 }
            branch { untuple 3  is_symbol  dip 1 { drop 0 }  dip 1 { drop 0 } }
                   { drop 0  push true }
        }
    "#,
        NOTHING,
    );
    assert_eq!(untuples(&before), 2);
    let after = run(
        prog,
        before,
        "repeat(bu(each(unfactor_branch); each(cancel_tuple); \
         each(annihilate_drop, noop, pick_drop_to_roll)))",
    );
    assert_eq!(
        untuples(&after),
        1,
        "the rebuild should cancel against the arm's untuple"
    );
}

#[test]
fn the_whole_derivation_runs_on_the_blocked_shape() {
    // End to end, from the shape `the_sharing_law_cannot_reach_across_a_branch`
    // shows is out of reach, with nothing hand-placed:
    //
    //   rebuild_copy     the value arrives built rather than carried
    //   float            delivers the rebuild down to the branch
    //   unfactor_branch  pushes it into both arms (sound: `tuple n` is total)
    //   cancel_tuple     annihilates it against the arm's `untuple`
    //
    // Every step is a local equivalence the rewriter checks for itself. No rule
    // is ever told that the value is a 3-tuple.
    let (prog, before) = probe("blocked");
    assert_eq!(untuples(&before), 2);
    let after = run(
        prog,
        before.clone(),
        "once(rebuild_copy); repeat(bu(each(float))); \
         repeat(bu(each(unfactor_branch); each(cancel_tuple); \
                   each(annihilate_drop, noop, pick_drop_to_roll)))",
    );
    assert_eq!(
        untuples(&after),
        1,
        "the two occurrences should have become one"
    );
    assert_eq!(
        seq_arity(prog, &before),
        seq_arity(prog, &after),
        "the whole derivation should preserve arity"
    );
}

#[test]
fn the_sharing_chain_runs_on_the_real_corpus_sentence() {
    // Not a probe: `barista::customer_impl::emit_does_pre_and_post` itself,
    // where the copy is made at the top of the caller and the `untuple` it
    // pairs with is two branches and several guards away.
    //
    //   copy_assoc       frames one copy so it can travel
    //   float            walks it past each guard instruction
    //   unfactor_branch  carries it through each branch
    //   rebuild_copy     fires once the copy finally sits on the untuple
    //   cancel_tuple     annihilates the rebuild against the later untuples
    // Tests run with the package root as the working directory. Not finding
    // the corpus is not a failure: the crate should still be testable alone.
    let main = Path::new("../tests/main.hana");
    let Ok(code) = fs::read_to_string(main) else {
        return;
    };
    let library: &'static Library =
        Box::leak(Box::new(bytecode::assemble_with_path(&code, main.parent()).unwrap()));
    let prog: &'static Program<'static> = Box::leak(Box::new(Program::new(library)));
    let idx = prog
        .library()
        .names
        .iter()
        .position(|n| n == "barista::customer_impl::emit_does_pre_and_post")
        .map(SentenceIndex::from)
        .expect("sentence should exist in the corpus");

    let opened = run(
        prog,
        build(prog.library(), idx, &mut HashSet::new()),
        "once(inline); children(once(inline)); then(then(once(inline))); distribute",
    );
    let before = untuples(&opened);
    assert!(
        before > 3,
        "expected several unshared untuples to start with, got {}",
        before
    );

    let after = run(
        prog,
        opened.clone(),
        "repeat(bu(each(copy_assoc); each(float); each(unfactor_branch); \
                   each(flatten_call); each(rebuild_copy); each(cancel_tuple)))",
    );
    assert!(
        untuples(&after) < before,
        "the chain should have shared some untuples: {} -> {}",
        before,
        untuples(&after)
    );
    assert_eq!(
        seq_arity(prog, &opened),
        seq_arity(prog, &after),
        "and preserved arity while doing it"
    );
}

#[test]
fn float_delivers_the_rebuild_to_the_branch_that_undoes_it() {
    // The same chain with nothing hand-placed. The rebuild sits where the
    // rewrite would leave it — straight after the picks — and `float` has to
    // carry it down past the checks before `unfactor_branch` can push it into
    // the arms and `cancel_tuple` can finish.
    //
    // This is the whole answer to how an untrusted oracle talks to the
    // rewriter: every step is a local equivalence the rewriter verifies. The
    // oracle only chose *where*.
    let (prog, before) = tree_of(
        r#"
        #[arity(1, 1)]
        sentence needs_float {
            untuple 3
            pick 2  pick 2  pick 2
            dip 3 { tuple 3 }
            is_symbol
            dip 1 { is_symbol }
            and
            dip 1 { is_symbol }
            and
            branch { untuple 3  is_symbol  dip 1 { drop 0 }  dip 1 { drop 0 } }
                   { drop 0  push true }
        }
    "#,
        NOTHING,
    );
    assert_eq!(untuples(&before), 2);
    let after = run(
        prog,
        before.clone(),
        "repeat(bu(each(float))); \
         repeat(bu(each(unfactor_branch); each(cancel_tuple); \
                   each(annihilate_drop, noop, pick_drop_to_roll)))",
    );
    assert_eq!(untuples(&after), 1);
    assert_eq!(
        seq_arity(prog, &before),
        seq_arity(prog, &after),
        "the whole derivation should preserve arity"
    );
}

#[test]
fn a_later_step_finding_nothing_does_not_discard_an_earlier_one() {
    // Regression. `each(sink)` rewrites; `each(annihilate_drop)` then matches
    // nowhere. The sequence has to keep the sinking — it used to roll the
    // whole thing back, silently, while --trace still reported `sink` firing.
    let (prog, before) = sample();
    let sunk = run(prog, before.clone(), "each(sink)");
    assert_ne!(shape(&before), shape(&sunk), "expected sinking to do something");
    assert_eq!(
        shape(&run(prog, before, "each(sink); each(annihilate_drop)")),
        shape(&sunk),
        "the second step found nothing, which must not undo the first"
    );
}

#[test]
fn a_failing_step_rolls_the_whole_sequence_back() {
    // `each(sink)` succeeds and rewrites; `fail` then aborts. The sequence has
    // to report the *original*, not the half-rewritten intermediate.
    let (prog, before) = sample();
    let Outcome::Failed(after) = outcome(prog, "each(sink); fail", before.clone()).unwrap() else {
        panic!("the sequence should fail")
    };
    assert_eq!(before, after, "a failed sequence must not leak its progress");
}

#[test]
fn choice_takes_the_first_branch_that_applies() {
    let (prog, before) = sample();
    // The first fails, so the second decides the result.
    let first = outcome(prog, "each(annihilate_drop) | each(sink)", before.clone())
        .unwrap()
        .into_nodes();
    let alone = run(prog, before, "each(sink)");
    assert_eq!(first, alone);
}

#[test]
fn choice_falls_through_a_branch_that_did_nothing() {
    // Regression: `|` used to fall through only on *failure*. Every prelude
    // tactic is a `repeat`, which is total and reports Unchanged rather than
    // Failed when it had no work — so a choice over them always stopped at the
    // first branch and the second was dead. `annihilate` never fires on this
    // corpus, so `annihilate | factoring` has to reach `factoring`.
    let (prog, body) = tree_of(
        r#"
        sentence probe {
            branch { push 7 push 1 } { push 7 push 2 }
        }
    "#,
        NOTHING,
    );
    assert_eq!(
        run(prog, body.clone(), "annihilate | factoring"),
        run(prog, body, FACTOR),
        "the choice should have fallen through to factoring"
    );
}

#[test]
fn fail_is_the_identity_of_choice_and_id_of_sequence() {
    let (prog, before) = sample();
    assert_eq!(
        outcome(prog, "fail | each(sink)", before.clone()).unwrap().into_nodes(),
        run(prog, before.clone(), "each(sink)")
    );
    assert_eq!(
        outcome(prog, "each(sink); id", before.clone()).unwrap().into_nodes(),
        run(prog, before, "each(sink)")
    );
}

#[test]
fn repeat_n_stops_early_when_there_is_nothing_left() {
    // Ten rounds of a tactic that settles after one must equal one round.
    let (prog, before) = sample();
    assert_eq!(
        run(prog, before.clone(), "repeat_n(10, bu(each(collapse)))"),
        run(prog, before, "repeat_n(1, bu(each(collapse)))")
    );
}

#[test]
fn inverse_rules_in_one_repeat_run_out_of_fuel_legibly() {
    // `collapse` and `expand` undo each other. The language lets you write
    // that; the budget is what makes it diagnosable rather than a hang.
    let (prog, body) = tree_of(
        r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#,
        NOTHING,
    );
    let err = apply(
        &compile("repeat(bu(each(collapse, expand)))"),
        &Env::new(prog, 50, false),
        body,
    )
    .expect_err("an inverse pair should exhaust the budget");

    let TacticError::OutOfFuel { recent, .. } = err else {
        panic!("expected OutOfFuel, got {:?}", err)
    };
    let trace = recent.join(" ");
    assert!(
        trace.contains("collapse@") && trace.contains("expand@"),
        "the trace should show the oscillation: {}",
        trace
    );
}

#[test]
fn duplicating_a_value_then_discarding_the_original_vanishes() {
    // `pick 0` copies the top; `drop 1` removes the value beneath it, which is
    // the original. The pair is the identity, and it takes two rules to see
    // that: one contracts it to `roll 0`, the other removes the no-op.
    //
    // `sink` cannot help and should not — the dip reaches at the value the
    // pick just produced, which is exactly the interference it forbids.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            pick 0
            drop 1
        }
    "#,
        "cleanup",
    );
    assert!(body.is_empty(), "expected nothing left, got {:?}", shape(&body));
}

#[test]
fn a_deeper_copy_and_discard_becomes_a_roll() {
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            pick 2
            drop 3
        }
    "#,
        "cleanup",
    );
    assert_eq!(shape(&body), vec!["roll 2"]);
}

#[test]
fn distributing_a_suffix_into_both_arms_preserves_arity() {
    let code = r#"
        sentence probe {
            branch { push 1 } { push 2 }
            add
        }
    "#;
    let (prog, plain) = tree_of(code, NOTHING);
    let spread = tree(code, "distribute");
    assert_eq!(shape(&spread), vec!["branch"], "the add should have moved in");
    assert_eq!(
        seq_arity(prog, &plain),
        seq_arity(prog, &spread),
        "distributing must not change what the sentence takes or leaves"
    );
}

#[test]
fn distribution_absorbs_every_following_node_and_then_stops() {
    // The measure is "nodes after a branch", so it runs out rather than
    // running forever, even though node count grows.
    let (_prog, body) = tree_of(
        r#"
        sentence probe {
            branch { push 1 } { push 2 }
            add
            add
        }
    "#,
        "distribute",
    );
    assert_eq!(shape(&body), vec!["branch"]);
}

#[test]
fn a_constant_condition_folds_to_the_arm_it_selects() {
    let then_arm = tree(
        r#"
        sentence probe {
            push true
            branch { push 10 } { push 20 }
        }
    "#,
        "cleanup",
    );
    assert_eq!(shape(&then_arm), vec!["push 10"]);

    let else_arm = tree(
        r#"
        sentence probe {
            push false
            branch { push 10 } { push 20 }
        }
    "#,
        "cleanup",
    );
    assert_eq!(shape(&else_arm), vec!["push 20"]);
}

#[test]
fn distributing_then_folding_reaches_what_neither_does_alone() {
    // The constant sits *inside* an arm, so `fold_branch` cannot see the inner
    // branch until the outer `push true` has been pushed in beside it. This is
    // the composition the two rules exist for, and it is why `distribute` is a
    // tactic you reach for rather than something `all` does behind your back.
    let code = r#"
        sentence probe {
            branch { push true } { push false }
            branch { push 10 } { push 20 }
        }
    "#;
    assert_eq!(
        shape(&tree(code, "cleanup")),
        vec!["branch", "branch"],
        "folding alone cannot see past the outer branch"
    );

    let both = tree(code, "distribute; cleanup");
    assert_eq!(shape(&both), vec!["branch"], "expected one branch to fold away");
    let Node::Branch {
        then_body,
        else_body,
        ..
    } = &both[0]
    else {
        panic!("expected a branch")
    };
    assert_eq!(shape(then_body), vec!["push 10"]);
    assert_eq!(shape(else_body), vec!["push 20"]);
}

#[test]
fn inlining_puts_the_callee_in_reach_of_the_callers_rules() {
    // Rules only ever see one sequence. An unexpanded call is opaque, so there
    // is nothing for distribution to move into; splicing on inline is what puts
    // the callee's branch and the caller's `add` in the same sequence. Leaving
    // a `dip 0` frame behind would have kept them apart.
    let code = r#"
        sentence chooser {
            branch { push 1 } { push 2 }
        }
        sentence caller {
            jump chooser
            add
        }
    "#;
    let prog = program_of(code);
    let caller = prog
        .library()
        .exports
        .get("caller")
        .copied()
        .unwrap_or(SentenceIndex::from(1));
    let body = build(prog.library(), caller, &mut HashSet::new());

    assert_eq!(
        shape(&run(prog, body.clone(), "distribute")),
        vec!["call 0 #0", "add"],
        "an unexpanded call is opaque, so distribution has nothing to enter"
    );
    assert_eq!(
        shape(&run(prog, body, "inline_all; distribute")),
        vec!["branch"],
        "once the callee is spliced in, the add moves into both arms"
    );
}

#[test]
fn flattening_preserves_arity() {
    let code = r#"
        sentence helper {
            push 1
            add
        }
        sentence probe {
            jump helper
            jump helper
        }
    "#;
    let prog = program_of(code);
    let library = prog.library();
    let probe = library
        .exports
        .get("probe")
        .copied()
        .unwrap_or(SentenceIndex::from(1));
    let body = run(
        prog,
        build(library, probe, &mut HashSet::new()),
        "inline_all",
    );
    let flat = run(prog, body.clone(), "flatten");

    assert_eq!(shape(&flat), vec!["push 1", "add", "push 1", "add"]);
    assert_eq!(seq_arity(prog, &body), seq_arity(prog, &flat));
}

// ---------------------------------------------------------------------------
// Inlining as a rule
// ---------------------------------------------------------------------------

/// Builds a named sentence without inlining, so a test can watch it happen.
fn raw(code: &str, name: &str) -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(code);
    let idx = prog
        .library()
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == name)
        .map(|(i, _)| i)
        .unwrap_or_else(|| panic!("no sentence named {}", name));
    (prog, build(prog.library(), idx, &mut HashSet::new()))
}

const CALLS: &str = r#"
    sentence inner { add }
    sentence middle { jump inner jump inner }
    sentence outer { jump middle }
"#;

#[test]
fn build_no_longer_expands_anything() {
    let (_prog, body) = raw(CALLS, "outer");
    assert_eq!(shape(&body), vec!["call 0 #1"]);
}

#[test]
fn inlining_a_call_splices_it_into_the_caller() {
    // No frame left behind: the callee's code lands in the caller's sequence,
    // which is the only place other rules can act on it.
    let (prog, body) = raw(CALLS, "outer");
    assert_eq!(
        shape(&run(prog, body, "once(inline)")),
        vec!["call 0 #0", "call 0 #0"]
    );
}

#[test]
fn inlining_is_bounded_one_call_at_a_time() {
    // Splicing rescans where it landed, so `each(inline)` expands a whole
    // sequence transitively. `once` is what takes a single call, and
    // `repeat_n` counts them.
    let (prog, body) = raw(CALLS, "outer");
    assert_eq!(
        shape(&run(prog, body.clone(), "repeat_n(2, once(inline))")),
        vec!["add", "call 0 #0"]
    );
    assert_eq!(
        shape(&run(prog, body, "repeat_n(3, once(inline))")),
        vec!["add", "add"]
    );
}

#[test]
fn each_inline_expands_a_sequence_all_the_way_down() {
    let (prog, body) = raw(CALLS, "outer");
    assert_eq!(shape(&run(prog, body.clone(), "each(inline)")), vec!["add", "add"]);
    assert_eq!(shape(&run(prog, body, "inline_all")), vec!["add", "add"]);
}

const LOOPS: &str = r#"
    #[recursive]
    #[arity(1, 1)]
    sentence countdown {
        pick 0
        push 0
        equal
        branch { } { push 1 subtract jump countdown }
    }
    #[recursive]
    sentence entry { push 5 jump countdown }
"#;

#[test]
fn the_recursive_annotation_is_all_it_takes_to_spot_recursion() {
    // No graph analysis: `check_arities` refuses to let a sentence call a
    // recursive one without being recursive itself, so the annotation has
    // already propagated up the call graph by the time the tool sees it.
    // `program::invariant` checks that against the whole corpus.
    let prog = program_of(LOOPS);
    for name in ["countdown", "entry"] {
        let idx = prog
            .library()
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(i, _)| i)
            .unwrap();
        assert!(prog.is_recursive(idx), "{} should be refused", name);
    }
}

#[test]
fn a_call_to_a_recursive_sentence_still_reports_its_arity() {
    // Reachable only from a recursive root, which the tool refuses — but the
    // arity is what deleting `Cut` bought, so it is worth pinning that a
    // `Call` carries one rather than poisoning everything after it.
    let (prog, body) = raw(LOOPS, "entry");
    assert_eq!(depths(prog, &body), vec![Some(0), Some(1)]);
    assert_eq!(seq_arity(prog, &body), (0, Some(1)));
}

#[test]
fn an_unannotated_recursive_call_is_still_unknown() {
    // Honest rather than wrong: without an #[arity] there is nothing to report.
    let (prog, body) = raw(
        r#"
        #[recursive]
        sentence loops { jump loops }
        #[recursive]
        sentence entry { push 1 jump loops }
    "#,
        "entry",
    );
    assert_eq!(depths(prog, &body), vec![Some(0), Some(1)]);
    assert_eq!(seq_arity(prog, &body).1, None);
}
