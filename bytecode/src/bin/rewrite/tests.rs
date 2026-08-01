//! Tests for the rewrite tool.

use std::collections::HashSet;

use bytecode::{assemble, SentenceIndex};
use std::fs;
use std::path::Path;

use crate::arity::{node_arity, seq_arity};
use crate::ir::{build, Node};
use crate::script::{Definitions, PRELUDE};
use crate::tactic::{apply, Env, Tactic};

/// The prelude tactics, by the name a test refers to them by.
const DIPS: &str = "dips";
const FACTOR: &str = "factoring";
const ANNIHILATE: &str = "annihilate";
const ALL: &str = "all";
const NOTHING: &str = "id";

/// Net stack change, which every rule must preserve exactly.
fn net(nodes: &[Node]) -> Option<i64> {
    let (inputs, outputs) = seq_arity(nodes);
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
fn run(nodes: Vec<Node>, src: &str) -> Vec<Node> {
    let env = Env::new(1_000_000, true);
    apply(&compile(src), &env, nodes)
        .unwrap_or_else(|e| panic!("{}", e))
        .into_nodes()
}

fn tree(code: &str, src: &str) -> Vec<Node> {
    let library = assemble(code).unwrap();
    let body = build(&library, SentenceIndex::from(0), &mut HashSet::new());
    run(body, src)
}

/// The depth before each instruction of a sequence, entered at its inputs.
fn depths(nodes: &[Node]) -> Vec<Option<i64>> {
    let mut depth = Some(seq_arity(nodes).0);
    let mut out = Vec::new();
    for node in nodes {
        out.push(depth);
        depth = match (depth, node_arity(node)) {
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
            Node::Cut(_) => "cut".to_string(),
        })
        .collect()
}

#[test]
fn depth_counts_inputs_once() {
    // Regression: an earlier version read the arity checker's recorded
    // per-instruction size, which already includes the inputs found so far,
    // and added the total back on — reporting `is_tuple` one deeper than it
    // runs.
    let body = tree(
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
    assert_eq!(depths(&body), vec![Some(1), Some(2), Some(2)]);
}

#[test]
fn dip_contributes_only_its_targets_net_change() {
    let body = tree(
        r#"
        #[arity(3, 1)]
        sentence probe {
            dip 1 { add }
            drop 0
        }
    "#,
        NOTHING,
    );
    assert_eq!(depths(&body), vec![Some(3), Some(2)]);
    // The dip itself takes three and leaves two: two consumed by the add,
    // plus the one it holds out of the way.
    assert_eq!(node_arity(&body[0]), Some((3, 2)));
}

#[test]
fn depth_stops_being_known_after_a_panic() {
    let body = tree(
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
    assert_eq!(depths(&body), vec![Some(0), Some(1), None]);
}

#[test]
fn factoring_looks_past_provenance() {
    // Both arms open with the same dipped block. They are separate inline
    // sentences, so they carry different labels — but the labels are for
    // the listing, not for deciding what the code does, and the prefix has
    // to factor anyway.
    let body = tree(
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
    let body = tree(
        r#"
        #[recursive]
        sentence loops {
            push 1
            jump loops
        }
    "#,
        NOTHING,
    );
    assert_eq!(seq_arity(&body).1, None);
}

#[test]
fn dips_sink_past_pushes_and_arithmetic() {
    // The dip starts at the end hiding one value. Moving it past `add`
    // widens it to two operands, and past each push narrows it again, so it
    // arrives at the front hiding nothing at all.
    let body = tree(
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
    let body = tree(
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
fn expansion_leaves_plain_calls_alone() {
    // `dip 0` hides nothing, so there is no unary nest to write it as.
    let body = tree_unary(
        r#"
        sentence probe {
            push 1
            push 2
            dip 0 { add }
        }
    "#,
    );
    assert_eq!(shape(&body), vec!["push 1", "push 2", "dip 0 { add }"]);
}

#[test]
fn expansion_preserves_arity() {
    let code = r#"
        sentence probe {
            untuple 3
            dip 2 { add }
        }
    "#;
    let normalized = tree(code, DIPS);
    let unary = tree_unary(code);
    assert_ne!(shape(&normalized), shape(&unary), "expected an expansion");
    assert_eq!(seq_arity(&normalized), seq_arity(&unary));
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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
    let body = tree(
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

    let mut checked = 0;
    for (s_idx, _) in library.names.iter_enumerated() {
        let plain = build(&library, s_idx, &mut HashSet::new());
        let name = || format!("#{} {}", usize::from(s_idx), library.names[s_idx]);

        // The dip tactics and factoring preserve arity outright.
        for tac in [DIPS, FACTOR] {
            let rewritten = run(plain.clone(), tac);
            assert_eq!(
                seq_arity(&plain),
                seq_arity(&rewritten),
                "`{}` changed the arity of {}",
                tac,
                name()
            );
        }

        // Everything together preserves net change, and never asks for
        // more inputs than the original did.
        let all = run(plain.clone(), ALL);
        assert_eq!(net(&plain), net(&all), "net change changed for {}", name());
        assert!(
            seq_arity(&all).0 <= seq_arity(&plain).0,
            "rewriting raised the input requirement of {}",
            name()
        );

        // Running to a fixpoint has to mean something: a second pass must find
        // nothing left to do. The flags guaranteed this by construction; now
        // that the search is separable from the rules it is worth asserting,
        // since a non-confluent rule set would show up here first.
        let twice = run(all.clone(), ALL);
        assert_eq!(all, twice, "rewriting {} was not idempotent", name());

        let unary = run(all.clone(), "unary");
        assert_eq!(
            seq_arity(&all),
            seq_arity(&unary),
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
        Node::Op(_) | Node::Cut(_) => true,
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
    let plain = tree(code, NOTHING);
    let normalized = tree(code, DIPS);
    assert_ne!(shape(&plain), shape(&normalized), "expected some rewriting");
    assert_eq!(seq_arity(&plain), seq_arity(&normalized));
}


// ---------------------------------------------------------------------------
// The tactic algebra
//
// Three-valued outcomes are only useful if the combinators respect them, and
// these are the laws the evaluator relies on. `bu` being total in particular
// is why `repeat` keys on progress rather than on success.
// ---------------------------------------------------------------------------

use crate::tactic::{Outcome, TacticError};

fn sample() -> Vec<Node> {
    tree(
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

fn outcome(src: &str, nodes: Vec<Node>) -> Result<Outcome, TacticError> {
    apply(&compile(src), &Env::new(1_000_000, true), nodes)
}

fn never_fails(src: &str) {
    let got = outcome(src, sample()).unwrap();
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
    let before = sample();
    let Outcome::Failed(after) = outcome("fail", before.clone()).unwrap() else {
        panic!("`fail` should fail")
    };
    assert_eq!(before, after);

    let Outcome::Failed(after) = outcome("each(annihilate_drop)", before.clone()).unwrap() else {
        panic!("nothing to annihilate here, so it should fail")
    };
    assert_eq!(before, after);
}

#[test]
fn a_failing_step_rolls_the_whole_sequence_back() {
    // `each(sink)` succeeds and rewrites; `fail` then aborts. The sequence has
    // to report the *original*, not the half-rewritten intermediate.
    let before = sample();
    let Outcome::Failed(after) = outcome("each(sink); fail", before.clone()).unwrap() else {
        panic!("the sequence should fail")
    };
    assert_eq!(before, after, "a failed sequence must not leak its progress");
}

#[test]
fn choice_takes_the_first_branch_that_applies() {
    let before = sample();
    // The first fails, so the second decides the result.
    let first = outcome("each(annihilate_drop) | each(sink)", before.clone())
        .unwrap()
        .into_nodes();
    let alone = run(before, "each(sink)");
    assert_eq!(first, alone);
}

#[test]
fn choice_falls_through_a_branch_that_did_nothing() {
    // Regression: `|` used to fall through only on *failure*. Every prelude
    // tactic is a `repeat`, which is total and reports Unchanged rather than
    // Failed when it had no work — so a choice over them always stopped at the
    // first branch and the second was dead. `annihilate` never fires on this
    // corpus, so `annihilate | factoring` has to reach `factoring`.
    let body = tree(
        r#"
        sentence probe {
            branch { push 7 push 1 } { push 7 push 2 }
        }
    "#,
        NOTHING,
    );
    assert_eq!(
        run(body.clone(), "annihilate | factoring"),
        run(body, FACTOR),
        "the choice should have fallen through to factoring"
    );
}

#[test]
fn fail_is_the_identity_of_choice_and_id_of_sequence() {
    let before = sample();
    assert_eq!(
        outcome("fail | each(sink)", before.clone()).unwrap().into_nodes(),
        run(before.clone(), "each(sink)")
    );
    assert_eq!(
        outcome("each(sink); id", before.clone()).unwrap().into_nodes(),
        run(before, "each(sink)")
    );
}

#[test]
fn repeat_n_stops_early_when_there_is_nothing_left() {
    // Ten rounds of a tactic that settles after one must equal one round.
    let before = sample();
    assert_eq!(
        run(before.clone(), "repeat_n(10, bu(each(collapse)))"),
        run(before, "repeat_n(1, bu(each(collapse)))")
    );
}

#[test]
fn inverse_rules_in_one_repeat_run_out_of_fuel_legibly() {
    // `collapse` and `expand` undo each other. The language lets you write
    // that; the budget is what makes it diagnosable rather than a hang.
    let body = tree(
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
        &Env::new(50, false),
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
    let body = tree(
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
    let body = tree(
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
    let plain = tree(code, NOTHING);
    let spread = tree(code, "distribute");
    assert_eq!(shape(&spread), vec!["branch"], "the add should have moved in");
    assert_eq!(
        seq_arity(&plain),
        seq_arity(&spread),
        "distributing must not change what the sentence takes or leaves"
    );
}

#[test]
fn distribution_absorbs_every_following_node_and_then_stops() {
    // The measure is "nodes after a branch", so it runs out rather than
    // running forever, even though node count grows.
    let body = tree(
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
fn a_branch_one_frame_down_is_out_of_reach_until_the_frame_is_gone() {
    // `jump chooser` compiles to Dip(0, ..), so the branch sits in the call's
    // body while the `add` sits outside it. Rules only ever see one sequence,
    // so no window holds both — distribution cannot fire, and should not be
    // given the context that would let it.
    let code = r#"
        sentence chooser {
            branch { push 1 } { push 2 }
        }
        sentence caller {
            jump chooser
            add
        }
    "#;
    let library = assemble(code).unwrap();
    let caller = library.exports.get("caller").copied().unwrap_or(SentenceIndex::from(1));
    let body = build(&library, caller, &mut HashSet::new());

    assert_eq!(
        shape(&run(body.clone(), "distribute")),
        vec!["dip 0 { branch }", "add"],
        "distribution should not reach through a call frame"
    );

    // Flattening the frame puts them in one sequence, and then it does.
    assert_eq!(
        shape(&run(body, "flatten; distribute")),
        vec!["branch"],
        "with the frame gone the add should have moved into both arms"
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
    let library = assemble(code).unwrap();
    let probe = library.exports.get("probe").copied().unwrap_or(SentenceIndex::from(1));
    let body = build(&library, probe, &mut HashSet::new());
    let flat = run(body.clone(), "flatten");

    assert_eq!(shape(&flat), vec!["push 1", "add", "push 1", "add"]);
    assert_eq!(seq_arity(&body), seq_arity(&flat));
}
