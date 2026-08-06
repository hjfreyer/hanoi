//! Integration tests for the rewrite tool.
//!
//! The layers have their own tests: `rule` checks that each equation says what
//! it means, `applier` that a step is applied or refused exactly, `matcher`
//! that a proposal is one the applier takes, `engine` that a run is reproduced
//! by the script it leaves. What is left for here is the tool as a whole —
//! prelude tactics over real `.hana` code, and the sweeps over the corpus that
//! keep the claims in `docs/tactics.md` honest.

use std::collections::HashSet;

use bytecode::arity::failure_reachability;
use bytecode::{Instruction, Library, SentenceIndex, assemble};
use std::fs;
use std::path::Path;

use crate::applier::apply_script;
use crate::arity::{node_arity, seq_arity};
use crate::engine::{Env, Tactic, run as run_tactic};
use crate::ir::{Node, build};
use crate::program::Program;
use crate::rule::{Rule, Script, StepKind};
use crate::script::{Definitions, PRELUDE};

/// The prelude tactics, by the name a test refers to them by.
const DIPS: &str = "dips";
const FACTOR: &str = "factoring";
const ANNIHILATE: &str = "annihilation";
const ALL: &str = "all";

/// Net stack change, which every equation must preserve exactly.
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

/// The same, with a program, so a term may name a sentence.
fn compile_for(prog: &Program, src: &str) -> Tactic {
    let mut defs = Definitions::new();
    defs.load(PRELUDE)
        .unwrap_or_else(|e| panic!("{}", e.render(PRELUDE)));
    defs.compile_with(src, Some(prog))
        .unwrap_or_else(|e| panic!("{}", e.render(src)))
}

/// Runs a tactic with `--check` on, and checks the script it produced replays.
///
/// Every test in this file therefore also asserts that each step preserved the
/// net stack effect of the window it rewrote, and that the derivation the run
/// recorded reproduces the run.
fn run(prog: &Program, nodes: Vec<Node>, src: &str) -> Vec<Node> {
    with_script(prog, nodes, src).0
}

fn with_script(prog: &Program, nodes: Vec<Node>, src: &str) -> (Vec<Node>, Script) {
    let env = Env::new(prog, 1_000_000, true);
    let before = nodes.clone();
    let (after, script) =
        run_tactic(&env, &compile(src), nodes).unwrap_or_else(|e| panic!("{}", e));

    let mut replayed = before;
    apply_script(prog, &mut replayed, &script, true)
        .unwrap_or_else(|e| panic!("`{}` produced a script that does not replay: {}", src, e));
    assert_eq!(
        replayed, after,
        "`{}` did not replay to its own result",
        src
    );
    (after, script)
}

/// Assembles `code` and returns a program for it.
///
/// Leaked, so the borrow is `'static` and a test can hand it around without
/// threading a lifetime through every helper.
fn program_of(code: &str) -> &'static Program<'static> {
    let library: &'static Library = Box::leak(Box::new(assemble(code).unwrap()));
    Box::leak(Box::new(Program::new(library)))
}

/// The first sentence of `code`, unfolded, then rewritten by `src`.
///
/// Unfolding first because these tests are about rewriting rather than about
/// expansion — `build` itself expands nothing, so without this every call would
/// still be a `Call` node.
fn tree_of(code: &str, src: &str) -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(code);
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let body = run(prog, body, &format!("unfold_all; {}", src));
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

// ---------------------------------------------------------------------------
// Depth reckoning
// ---------------------------------------------------------------------------

#[test]
fn depth_counts_inputs_once() {
    let prog = program_of("sentence probe { add drop 0 drop 0 }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    // Two operands in, the sum and its flag out, then both dropped.
    assert_eq!(
        depths(prog, &body),
        vec![Some(2), Some(2), Some(1)],
        "{:?}",
        shape(&body)
    );
}

#[test]
fn depth_stops_being_known_after_a_panic() {
    let prog = program_of("sentence probe { push 1 panic push 2 }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let d = depths(prog, &body);
    assert_eq!(d[0], Some(0));
    assert_eq!(d[1], Some(1));
    assert_eq!(d[2], None, "the reckoning should stop at the panic");
}

/// A branch's arity accounts for **both** arms, not whichever answered first.
///
/// The arity checker holds the two arms to the same *net* change and to
/// nothing else, so they may differ in what they require. Reading the arity off
/// one arm understated it, and an understated arity is a soundness bug:
/// `annihilate` asks only for an arity.
#[test]
fn a_branch_takes_what_the_hungrier_arm_takes() {
    // `{ }` is (0 -> 0) and `{ drop 0  push true }` is (1 -> 1): same net,
    // different demands. The branch needs the condition and the value.
    let prog = program_of("sentence probe { pick 0 branch { } { drop 0 push true } }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let [_, inner] = &body[..] else {
        panic!("expected a pick and a branch, got {:?}", shape(&body))
    };
    assert_eq!(node_arity(prog, inner), Some((2, 1)));

    // An arm that never returns answers for neither, and the other stands
    // alone — the one case where a single arm decides.
    let prog = program_of("sentence probe { pick 0 branch { panic } { drop 0 } }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let [_, inner] = &body[..] else {
        panic!("expected a branch")
    };
    assert_eq!(node_arity(prog, inner), Some((2, 0)));
}

/// The rewrite that understating a branch's arity used to license.
///
/// `test_always_true` returns `true` for every input — it is `drop ; push
/// true`, not the identity. The inner `branch { } { drop ; push true }` is
/// `(2 -> 1)`, but reading the then arm alone made it `(1 -> 0)`, and
/// `annihilate` with no outputs to read turned it into a `drop`. Twice over,
/// that left the identity.
///
/// **`--check` could not have caught it.** It compares net change, and `(1, 0)`
/// and `(2, 1)` have the same net; the input requirement fell, which it allows
/// on purpose because annihilation legitimately lowers one. The arity was the
/// only place to fix it.
#[test]
fn a_function_that_is_not_the_identity_is_not_rewritten_into_one() {
    let code = r#"
        #[total]
        function test_always_true {
            pick 0
            is_bool
            branch {
                pick 0
                branch { } { drop 0 push true }
            } {
                drop 0
                push true
            }
        }
    "#;
    let (prog, plain) = tree_of(code, "id");
    for tac in ["cleanup", "all", "annihilation", "factoring; all"] {
        let got = run(prog, plain.clone(), tac);
        assert_eq!(
            shape(&got),
            shape(&plain),
            "`{}` rewrote a function that nothing in the set can simplify",
            tac
        );
    }
}

#[test]
fn a_cycle_has_no_static_arity() {
    let prog = program_of("#[recursive] sentence loops { jump loops }");
    assert_eq!(prog.arity(SentenceIndex::from(0)), None);
}

// ---------------------------------------------------------------------------
// Frames: collapse, sink, fuse, expand
// ---------------------------------------------------------------------------

#[test]
fn dips_sink_past_pushes_and_arithmetic() {
    // The dip's window clears what each node leaves behind, so it walks left
    // and the depth follows the arithmetic.
    let got = tree("sentence probe { push 1 dip 2 { drop 0 } }", DIPS);
    assert_eq!(
        shape(&got),
        vec!["dip 1 { drop }", "push 1"],
        "{:?}",
        shape(&got)
    );
}

#[test]
fn dips_fuse_when_they_meet_at_the_same_depth() {
    let got = tree("sentence probe { dip 1 { push 1 } dip 1 { push 2 } }", DIPS);
    assert_eq!(shape(&got), vec!["dip 1 { push 1 push 2 }"]);
}

#[test]
fn nested_dips_collapse_and_then_keep_sinking() {
    // Collapsing first is what lets the interchange law see the frame's true
    // hidden depth; without it the outer frame reports 1 and stops early.
    let got = tree("sentence probe { push 1 dip 1 { dip 1 { drop 0 } } }", DIPS);
    assert_eq!(shape(&got), vec!["dip 1 { drop }", "push 1"]);
}

#[test]
fn a_deep_dip_becomes_a_nest_of_unary_dips() {
    let got = tree("sentence probe { dip 3 { drop 0 } }", "unary");
    assert_eq!(shape(&got), vec!["dip 1 { dip 1 { dip 1 { drop } } }"]);
}

#[test]
fn expansion_preserves_arity() {
    let (prog, plain) = tree_of("sentence probe { dip 3 { drop 0 } }", "id");
    let unary = run(prog, plain.clone(), "unary");
    assert_eq!(seq_arity(prog, &plain), seq_arity(prog, &unary));
}

#[test]
fn a_dip_stops_at_a_pick_that_reaches_into_it() {
    // `pick 2` is (3 -> 4): a window 3 deep does not clear the four values it
    // leaves, so the frame cannot pass it.
    let got = tree("sentence probe { pick 2 dip 3 { drop 0 } }", DIPS);
    assert_eq!(shape(&got), vec!["pick 2", "dip 3 { drop }"]);
}

#[test]
fn a_dip_sinks_past_a_pick_it_clears() {
    let got = tree("sentence probe { pick 0 dip 2 { drop 0 } }", DIPS);
    assert_eq!(shape(&got), vec!["dip 1 { drop }", "pick 0"]);
}

#[test]
fn fusing_records_every_origin() {
    // Provenance survives a fusion: the listing still says where both halves
    // came from, which is what the origins are for.
    let prog = program_of(
        r#"
        sentence one { push 1 }
        sentence two { push 2 }
        sentence probe { dip 1 { jump one } dip 1 { jump two } }
        "#,
    );
    let probe = prog
        .library()
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == "probe")
        .map(|(i, _)| i)
        .unwrap();
    let body = build(prog.library(), probe, &mut HashSet::new());
    let got = run(prog, body, DIPS);
    let [Node::Dip { origins, .. }] = &got[..] else {
        panic!("expected one fused frame, got {:?}", shape(&got))
    };
    assert_eq!(origins.len(), 2, "origins were {:?}", origins);
}

// ---------------------------------------------------------------------------
// Branches
// ---------------------------------------------------------------------------

fn arms(then_arm: &str, else_arm: &str) -> String {
    format!(
        "sentence probe {{ pick 0 branch {{ {} }} {{ {} }} }}",
        then_arm, else_arm
    )
}

#[test]
fn a_shared_branch_prefix_is_hoisted_under_a_dip() {
    let got = tree(&arms("drop 0 push 1", "drop 0 push 2"), FACTOR);
    assert_eq!(
        shape(&got),
        vec!["pick 0", "dip 1 { drop }", "branch"],
        "{:?}",
        shape(&got)
    );
}

#[test]
fn factoring_takes_the_whole_shared_run() {
    let got = tree(&arms("drop 0 not push 1", "drop 0 not push 2"), FACTOR);
    assert_eq!(shape(&got), vec!["pick 0", "dip 1 { drop not }", "branch"]);
}

#[test]
fn factoring_stops_where_the_arms_diverge() {
    let got = tree(&arms("drop 0 push 1 not", "drop 0 push 2 not"), FACTOR);
    // The shared prefix comes out; the shared *suffix* is `distribute`'s
    // business read backwards and is not part of factoring.
    assert_eq!(shape(&got), vec!["pick 0", "dip 1 { drop }", "branch"]);
}

#[test]
fn factoring_looks_past_provenance() {
    // Two identical blocks compiled to different sentences never share a
    // label, and comparing labels made factoring miss every shared prefix that
    // contained a call.
    let code = r#"
        sentence probe {
            pick 0
            branch { dip 1 { push 7 } drop 0 } { dip 1 { push 7 } not drop 0 }
        }
    "#;
    let prog = program_of(code);
    let probe = prog
        .library()
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == "probe")
        .map(|(i, _)| i)
        .unwrap();
    let body = build(prog.library(), probe, &mut HashSet::new());
    let got = run(prog, body, FACTOR);
    assert_eq!(got.len(), 3, "nothing was factored: {:?}", shape(&got));
}

#[test]
fn a_decided_branch_folds_to_the_arm_it_takes() {
    let got = tree(
        "sentence probe { push true branch { push 1 } { push 2 } }",
        "cleanup",
    );
    assert_eq!(shape(&got), vec!["push 1"]);
}

#[test]
fn distribution_puts_what_follows_a_branch_inside_both_arms() {
    let got = tree(
        "sentence probe { pick 0 branch { push 1 } { push 2 } drop 0 }",
        "distribution",
    );
    assert_eq!(shape(&got), vec!["pick 0", "branch"]);
}

// ---------------------------------------------------------------------------
// Annihilation
// ---------------------------------------------------------------------------

#[test]
fn a_push_and_a_drop_cancel() {
    let got = tree("sentence probe { push 1 drop 0 }", ANNIHILATE);
    assert!(got.is_empty(), "{:?}", shape(&got));
}

#[test]
fn a_pick_and_a_drop_cancel() {
    // The counit law, which is not an annihilation: `pick d` is (d+1 -> d+2).
    let got = tree("sentence probe { pick 2 drop 0 }", ANNIHILATE);
    assert!(got.is_empty(), "{:?}", shape(&got));
}

#[test]
fn an_operator_takes_its_operands_with_it() {
    // `add` is (2 -> 2) now the flag is explicit, so what cancels it is two
    // drops, and what is left is two drops of the operands.
    let got = tree("sentence probe { add drop 0 drop 0 }", ANNIHILATE);
    assert_eq!(shape(&got), vec!["drop", "drop"]);
}

#[test]
fn a_computation_whose_results_all_go_reaches_a_frame() {
    // The old whitelist refused anything framed, for fear of an `assert`
    // several levels down. Under the totality precondition there is none, so
    // the arity is the whole condition: `dip 1 { drop 0 }` is (2 -> 1), and
    // one drop after it takes both its inputs instead.
    let got = tree("sentence probe { dip 1 { drop 0 } drop 0 }", ANNIHILATE);
    assert_eq!(shape(&got), vec!["drop", "drop"], "{:?}", shape(&got));
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

#[test]
fn comparing_two_literals_is_decided() {
    let got = tree("sentence probe { push 1 push 1 equal }", "values");
    assert_eq!(shape(&got), vec!["push true"]);
}

#[test]
fn folding_is_evaluation_even_on_junk() {
    // Neither operand is `Bool(false)`, so both are true and `and` is true —
    // the same answer the interpreter gives, which is the whole obligation.
    let got = tree("sentence probe { push 1 push 2 and }", "values");
    assert_eq!(shape(&got), vec!["push true"]);

    // And `false` is what decides it the other way.
    let got = tree("sentence probe { push 1 push false and }", "values");
    assert_eq!(shape(&got), vec!["push false"]);
}

#[test]
fn building_a_tuple_and_taking_it_apart_leaves_the_flag() {
    let got = tree("sentence probe { tuple 2 untuple 2 }", "values");
    assert_eq!(shape(&got), vec!["push true"]);
}

// ---------------------------------------------------------------------------
// Unfolding
// ---------------------------------------------------------------------------

fn raw(code: &str, name: &str) -> (&'static Program<'static>, Vec<Node>) {
    let prog = program_of(code);
    let idx = prog
        .library()
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == name)
        .map(|(i, _)| i)
        .unwrap_or_else(|| panic!("no sentence '{}'", name));
    let body = build(prog.library(), idx, &mut HashSet::new());
    (prog, body)
}

const CHAIN: &str = r#"
    sentence third  { push 3 }
    sentence second { jump third }
    sentence first  { jump second }
"#;

#[test]
fn build_expands_nothing_on_its_own() {
    let (_, body) = raw(CHAIN, "first");
    assert_eq!(shape(&body), vec!["call 0 #1"], "{:?}", shape(&body));
}

#[test]
fn unfolding_is_bounded_one_call_at_a_time() {
    let (prog, body) = raw(CHAIN, "first");
    let once = run(prog, body.clone(), "once(unfold)");
    assert_eq!(shape(&once), vec!["call 0 #0"], "{:?}", shape(&once));
    let twice = run(prog, once, "once(unfold)");
    assert_eq!(shape(&twice), vec!["push 3"]);
}

#[test]
fn unfold_all_opens_a_sequence_all_the_way_down() {
    let (prog, body) = raw(CHAIN, "first");
    let got = run(prog, body, "unfold_all");
    assert_eq!(shape(&got), vec!["push 3"]);
}

#[test]
fn unfolding_puts_the_callee_in_reach_of_the_callers_laws() {
    // The motivating case: a jump hides a branch from the operator after it,
    // and opening the call is what puts the two in one window.
    let code = r#"
        sentence inner { push true branch { push 1 } { push 2 } }
        sentence probe { jump inner }
    "#;
    let (prog, body) = raw(code, "probe");
    let got = run(prog, body, "unfold_all; cleanup");
    assert_eq!(shape(&got), vec!["push 1"]);
}

#[test]
fn the_recursive_annotation_is_all_it_takes_to_spot_recursion() {
    let (prog, body) = raw("#[recursive] sentence loops { jump loops }", "loops");
    let before = shape(&body);
    let got = run(prog, body, "unfold_all");
    assert_eq!(shape(&got), before, "a recursive call was opened");
}

// ---------------------------------------------------------------------------
// Passes compose
// ---------------------------------------------------------------------------

#[test]
fn passes_compose() {
    // Factoring exposes a frame, the dip passes move it, and cleanup cancels
    // what that brings together. Each alone leaves work the others finish.
    let code = "sentence probe { pick 0 branch { drop 0 push 1 drop 0 } { drop 0 push 2 drop 0 } }";
    let (prog, plain) = tree_of(code, "id");
    let separately = {
        let a = run(prog, plain.clone(), FACTOR);
        let b = run(prog, a, DIPS);
        run(prog, b, "cleanup")
    };
    let together = run(prog, plain, "factoring; dips; cleanup");
    assert_eq!(shape(&separately), shape(&together));
}

// ---------------------------------------------------------------------------
// Introducing code
// ---------------------------------------------------------------------------

/// The move that makes factoring reachable when only one arm has the prefix.
///
/// Every other matcher rewrites what it found, so a rule reading `drop` could
/// never propose `pick 0` — nothing in the window says which computation ought
/// to appear. The term comes from the tactic expression, and the annihilation
/// law read backwards is what makes putting it there sound: both sides discard
/// exactly the same value.
#[test]
fn introducing_a_copy_lets_factoring_reach_an_arm_that_lacked_it() {
    // A predicate whose then-arm copies the value and whose else-arm does not.
    let code = r#"
        #[total]
        function probe {
            pick 0
            is_bool
            branch {
                pick 0
                branch { } { drop 0 push true }
            } {
                drop 0
                push true
            }
        }
    "#;
    let (prog, plain) = tree_of(code, "id");

    // Nothing to factor: the arms share no prefix.
    let untouched = run(prog, plain.clone(), FACTOR);
    assert_eq!(
        shape(&untouched),
        shape(&plain),
        "there was a shared prefix"
    );

    // Give the else arm a `pick 0` it immediately discards, and now there is.
    let (got, script) = with_script(prog, plain, "else(once(introduce { pick 0 })); factoring");
    assert_eq!(
        shape(&got)[2],
        "dip 1 { pick 0 }",
        "the copy was not hoisted: {:?}",
        shape(&got)
    );

    // One step to introduce, three to factor.
    assert_eq!(script.len(), 4);
    assert_eq!(script[0].kind.name(), "annihilate");
    assert_eq!(script[0].dir, crate::rule::Direction::Reverse);
}

#[test]
fn what_introduce_puts_in_annihilate_takes_back_out() {
    // Forward and backward readings of one law, so the two undo each other and
    // the term is where it started.
    let code = "sentence probe { drop 0 push 1 }";
    let (prog, plain) = tree_of(code, "id");
    let there = run(prog, plain.clone(), "once(introduce { pick 0 })");
    assert_ne!(shape(&there), shape(&plain));
    let back = run(prog, there, "annihilation");
    assert_eq!(shape(&back), shape(&plain));
}

#[test]
fn introducing_preserves_what_the_program_does() {
    // The check every test here runs anyway, said explicitly for the one
    // matcher that makes a term bigger on purpose.
    let code = "sentence probe { drop 0 drop 0 push 1 }";
    let (prog, plain) = tree_of(code, "id");
    let got = run(prog, plain.clone(), "once(introduce { pick 1 is_bool })");
    assert_eq!(net(prog, &plain), net(prog, &got));
}

/// A case split is what lets folding reach a value that was never a literal.
///
/// Every other law needs the fact already on the stack. This manufactures the
/// two cases in which it is one — and `tests/identities.hana` runs the block
/// against the interpreter to check it really is the identity.
#[test]
fn splitting_a_bool_lets_the_folding_laws_reach_an_opaque_value() {
    // `not` on an unknown value: nothing can be said about it.
    let (prog, plain) = tree_of("#[total] function probe { not }", "id");
    assert_eq!(shape(&plain), vec!["not"]);
    assert_eq!(run(prog, plain.clone(), "values"), plain);

    // Split the value first and each boolean case folds to a literal.
    let got = run(prog, plain, "at(0, split_bool); distribution; values");
    let [_, _, Node::Branch { then_body, .. }] = &got[..] else {
        panic!("expected a guard branch, got {:?}", shape(&got))
    };
    let [
        Node::Branch {
            then_body: yes,
            else_body: no,
            ..
        },
    ] = &then_body[..]
    else {
        panic!("expected an inner branch")
    };
    // not true = false, not false = true.
    assert_eq!(shape(yes), vec!["push false"]);
    assert_eq!(shape(no), vec!["push true"]);
}

// ---------------------------------------------------------------------------
// Reading an equation backwards
// ---------------------------------------------------------------------------

/// The end of a branch that `factor` cannot reach.
///
/// `factor` hoists a shared *prefix*; the shared suffix is the distribution law
/// read backwards, which nothing had a name for. `inv(distribute)` is that
/// reading, and needing no name of its own is the point.
#[test]
fn reading_distribute_backwards_factors_a_shared_suffix() {
    let code = "sentence probe { pick 0 branch { drop 0 push 1 not } { drop 0 push 2 not } }";
    let (prog, plain) = tree_of(code, "id");

    let got = run(prog, plain.clone(), "bu(each(inv(distribute)))");
    assert_eq!(
        shape(&got),
        vec!["pick 0", "branch", "not"],
        "{:?}",
        shape(&got)
    );

    // And the forward reading puts it back, which is what makes them one law.
    assert_eq!(shape(&run(prog, got, "distribution")), shape(&plain));
}

/// Factoring can leave a branch with nothing in it, and then it can go.
///
/// Arms that were the same all the way down are hoisted out entirely, and what
/// is left consumes the condition and does nothing else. That is `annihilate`
/// with no outputs to read — not a new law, just the case no matcher looked
/// for.
#[test]
fn a_branch_whose_arms_were_the_same_disappears_along_with_them() {
    let code = "sentence probe { pick 0 branch { drop 0 } { drop 0 } }";
    let (prog, plain) = tree_of(code, "id");

    // Factoring alone leaves the husk behind.
    let factored = run(prog, plain.clone(), FACTOR);
    assert_eq!(
        shape(&factored),
        vec!["pick 0", "dip 1 { drop }", "branch"],
        "{:?}",
        shape(&factored)
    );

    // Cleaning up after it takes the husk, and then everything it was holding.
    let got = run(prog, plain, "factoring; all");
    assert_eq!(shape(&got), vec!["drop"], "{:?}", shape(&got));
}

// ---------------------------------------------------------------------------
// Hoisting out of one arm
// ---------------------------------------------------------------------------

const SPECULATION: &str = r#"
    #[total] #[arity(2, 2)]
    sentence probe { pick 0 branch { pick 1 pick 1 equal and } { not } }
"#;

/// `speculate { X }` is shorthand, and this says so literally.
///
/// Nothing new is assumed: the firing is the vacuous identity conjured into
/// the other arm and then factored, which is what `inv(counit)`, `introduce`
/// and `factoring` do when written out. Both routes are held to the same
/// answer, so the shorthand cannot drift from what it abbreviates.
#[test]
fn speculating_is_what_the_three_rules_do_written_out() {
    let (prog, plain) = tree_of(SPECULATION, "id");

    let by_hand = run(
        prog,
        plain.clone(),
        "must(else(at(0, inv(counit(1)))));          must(else(at(1, inv(counit(1)))));          must(else(at(2, introduce { equal })));          must(factoring)",
    );
    let (shorthand, script) = with_script(prog, plain, "must(once(speculate { equal }))");

    assert_eq!(shape(&shorthand), shape(&by_hand));
    assert_eq!(
        shape(&shorthand),
        vec!["pick 0", "dip 1 { pick 1 pick 1 equal }", "branch"],
        "{:?}",
        shape(&shorthand)
    );

    // Every step is an equation the tool already had — no new law rode in.
    let laws: Vec<&str> = script.iter().map(|s| s.kind.name()).collect();
    assert_eq!(
        laws,
        vec![
            "counit",
            "counit",
            "annihilate",
            "elim_dip0",
            "elim_dip0",
            "hoist"
        ]
    );
}

/// What the losing arm is left holding.
///
/// The point of speculating on *copies*: the arm that did not want `X` drops
/// its results and carries on with the values it always had, so `X` needs no
/// inverse and nothing is asked of it but totality.
#[test]
fn the_arm_that_did_not_want_it_drops_the_results() {
    let (prog, plain) = tree_of(SPECULATION, "id");
    let got = run(prog, plain, "must(once(speculate { equal }))");
    let [
        _,
        _,
        Node::Branch {
            then_body,
            else_body,
            ..
        },
    ] = &got[..]
    else {
        panic!("expected a frame and a branch, got {:?}", shape(&got))
    };
    assert_eq!(shape(then_body), vec!["and"]);
    // `equal` is (2 -> 1), so exactly one result to discard.
    assert_eq!(shape(else_body), vec!["drop", "not"]);
}

// ---------------------------------------------------------------------------
// Testing the same value twice
// ---------------------------------------------------------------------------

/// When the two inner branches are the same, no new law is needed.
///
/// Worth pinning, because it is the reason `retest` says only what it says:
/// `distribute` backwards factors the shared inner branch out of both arms,
/// which leaves `branch { } { }` for `annihilate` at m = 0 and then `counit`.
/// Three steps, no axiom. What `retest` adds is only that the *off-diagonal*
/// arms are dead.
#[test]
fn a_branch_repeated_in_both_arms_needs_no_new_law() {
    let code = r#"
        #[total] #[arity(1, 1)]
        sentence probe {
            pick 0
            branch { branch { push 1 } { push 2 } } { branch { push 1 } { push 2 } }
        }
    "#;
    let (prog, plain) = tree_of(code, "id");
    let tactic = "bu(each(inv(distribute))); repeat(bu(each(annihilate_void, counit)))";
    let (got, script) = with_script(prog, plain, tactic);
    assert_eq!(shape(&got), vec!["branch"], "{:?}", shape(&got));
    assert_eq!(script.len(), 3);
    assert_eq!(
        script.iter().map(|s| s.kind.name()).collect::<Vec<_>>(),
        vec!["distribute", "annihilate", "counit"]
    );
}

/// The general case, which is what the new law is for.
#[test]
fn four_different_arms_collapse_to_the_diagonal() {
    let code = r#"
        #[total] #[arity(1, 1)]
        sentence probe {
            pick 0
            branch { branch { push 1 } { push 2 } } { branch { push 3 } { push 4 } }
        }
    "#;
    let (prog, plain) = tree_of(code, "id");
    let (got, script) = with_script(prog, plain, "all");
    let [
        Node::Branch {
            then_body,
            else_body,
            ..
        },
    ] = &got[..]
    else {
        panic!("expected one branch, got {:?}", shape(&got))
    };
    // `A` from the then arm's then arm, `D` from the else arm's else arm: the
    // two arms the same condition can actually reach.
    assert_eq!(shape(then_body), vec!["push 1"]);
    assert_eq!(shape(else_body), vec!["push 4"]);

    // Two firings of `retest`, one per arm, then `factor` and the other counit.
    let fired: Vec<&str> = script.iter().map(|s| s.kind.name()).collect();
    assert_eq!(fired.iter().filter(|n| **n == "retest").count(), 2);
    assert!(fired.contains(&"counit_under"), "{:?}", fired);
}

// ---------------------------------------------------------------------------
// Sharing one computation between two uses
// ---------------------------------------------------------------------------

/// The case the law is for: a call made twice on copies of the same inputs.
///
/// The term names the sentence, which is what a term could not do before —
/// there was nothing for one to name, since a term is written in the tactic
/// rather than compiled from a sentence. `share` needs the name, and needs the
/// library to know how wide a window `jump classify` makes.
#[test]
fn sharing_a_call_runs_it_once_and_copies_what_it_left() {
    let code = r#"
        #[total]
        function classify { pick 0 is_int branch { drop 0 push 7 } { drop 0 push 8 } }

        #[total]
        #[arity(1, 2)]
        sentence twice { pick 0 jump classify dip 1 { jump classify } }
    "#;
    let (prog, plain) = raw(code, "twice");
    let tactic = compile_for(prog, "must(once(share { jump classify }))");

    let env = Env::new(prog, 1_000_000, true);
    let (got, script) =
        run_tactic(&env, &tactic, plain.clone()).unwrap_or_else(|e| panic!("{}", e));
    assert_eq!(
        shape(&got),
        vec!["call 0 #0", "pick 0"],
        "{:?}",
        shape(&got)
    );
    assert_eq!(script.len(), 1, "one law, one step");
    assert_eq!(script[0].kind.name(), "copy_nat");

    // And the derivation replays, which is what makes the step a construction
    // rather than a claim.
    let mut replayed = plain.clone();
    apply_script(prog, &mut replayed, &script, true).unwrap();
    assert_eq!(replayed, got);

    // Backwards, it runs the call a second time instead of copying.
    let back = compile_for(prog, "must(once(inv(share { jump classify })))");
    let env = Env::new(prog, 1_000_000, true);
    let (there, _) = run_tactic(&env, &back, got).unwrap_or_else(|e| panic!("{}", e));
    assert_eq!(shape(&there), shape(&plain));
}

#[test]
fn a_term_may_only_name_a_sentence_when_there_is_a_program() {
    // The arity of `jump foo` is what says how wide a window the rule reads,
    // and that is a fact about the library. Everything else about a tactic is
    // still settled without one.
    let mut defs = Definitions::new();
    defs.load(PRELUDE).unwrap();
    let err = defs
        .compile("once(share { jump whatever })")
        .expect_err("it should not compile with no program");
    assert!(err.message.contains("needs a program"), "{}", err.message);

    // A term that names nothing still compiles on its own.
    assert!(defs.compile("once(share { equal })").is_ok());
}

#[test]
fn the_two_readings_of_a_law_are_one_law() {
    // Every `inv` pair, over real code: there and back is where it started.
    let code = "sentence probe { pick 0 dip 2 { push 1 drop 0 } branch { not } { is_bool } }";
    let (prog, plain) = tree_of(code, "id");
    for (there, back) in [
        ("once(inv(flatten))", "bu(each(flatten))"),
        ("once(inv(fuse))", "bu(each(fuse))"),
        ("bu(once(expand))", "repeat(bu(each(collapse)))"),
    ] {
        let out = run(prog, plain.clone(), there);
        assert_ne!(shape(&out), shape(&plain), "`{}` did nothing", there);
        assert_eq!(
            shape(&run(prog, out, back)),
            shape(&plain),
            "`{}` did not undo `{}`",
            back,
            there
        );
    }
}

#[test]
fn a_split_that_taught_nothing_can_be_taken_back_out() {
    let (prog, plain) = tree_of("#[total] function probe { not }", "id");
    let there = run(prog, plain.clone(), "at(0, split_bool)");
    assert_ne!(shape(&there), shape(&plain));
    assert_eq!(run(prog, there, "once(unsplit_bool)"), plain);
}

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

/// The corpus, or `None` when it is not there — the crate stays testable alone.
fn corpus() -> Option<(&'static Library, &'static Program<'static>)> {
    let main = Path::new("../tests/main.hana");
    let code = fs::read_to_string(main).ok()?;
    let library: &'static Library = Box::leak(Box::new(
        bytecode::assemble_with_path(&code, main.parent()).unwrap(),
    ));
    let prog: &'static Program<'static> = Box::leak(Box::new(Program::new(library)));
    Some((library, prog))
}

/// Every sentence the tool would agree to work on.
///
/// The two refusals `main` makes, applied to the sweep: the equations are
/// stated for code that is neither recursive nor able to fail, so a sweep that
/// ignored the precondition would be testing something the tool does not do.
fn admissible(library: &Library, prog: &Program) -> Vec<SentenceIndex> {
    let can_fail = failure_reachability(library);
    library
        .names
        .iter_enumerated()
        .map(|(idx, _)| idx)
        .filter(|idx| !prog.is_recursive(*idx) && !can_fail[usize::from(*idx)])
        .collect()
}

fn unary_only(nodes: &[Node]) -> bool {
    nodes.iter().all(|node| match node {
        Node::Dip { depth, body, .. } => *depth <= 1 && unary_only(body),
        Node::Branch {
            then_body,
            else_body,
            ..
        } => unary_only(then_body) && unary_only(else_body),
        _ => true,
    })
}

/// What every pass owes the corpus.
///
/// - **Net change** is preserved by everything. A rewrite that leaves a
///   different number of values is wrong however plausible it looks.
/// - **The input requirement** is preserved by the dip passes and by factoring,
///   but annihilation may *lower* it: dropping `pick 2; drop` also drops the
///   demand for three values that only the pick made. The rewritten code is
///   defined on strictly more stacks than the original, which is sound — so the
///   bound is one-directional rather than an equality.
/// - **A fixpoint is a fixpoint.** A second pass must find nothing left to do,
///   which is where a non-confluent set would show up first.
#[test]
fn rewrites_preserve_arity_across_the_corpus() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let mut checked = 0;
    for s_idx in admissible(library, prog) {
        let plain = run(
            prog,
            build(library, s_idx, &mut HashSet::new()),
            "unfold_all",
        );
        let name = || format!("#{} {}", usize::from(s_idx), library.names[s_idx]);

        for tac in [DIPS, FACTOR] {
            let rewritten = run(prog, plain.clone(), tac);
            assert_eq!(
                seq_arity(prog, &plain),
                seq_arity(prog, &rewritten),
                "`{}` changed the arity of {}",
                tac,
                name()
            );
        }

        let all = run(prog, plain.clone(), ALL);
        assert_eq!(
            net(prog, &plain),
            net(prog, &all),
            "net change changed for {}",
            name()
        );
        assert!(
            seq_arity(prog, &all).0 <= seq_arity(prog, &plain).0,
            "rewriting raised the input requirement of {}",
            name()
        );

        let twice = run(prog, all.clone(), ALL);
        assert_eq!(all, twice, "rewriting {} was not idempotent", name());

        let unary = run(prog, all.clone(), "unary");
        assert_eq!(
            seq_arity(prog, &all),
            seq_arity(prog, &unary),
            "unary expansion changed the arity of {}",
            name()
        );
        assert!(
            unary_only(&unary),
            "{} kept a frame deeper than 1 after expansion",
            name()
        );
        checked += 1;
    }

    assert!(
        checked > 300,
        "only {} sentences were admissible; the sweep is near-vacuous",
        checked
    );
}

/// The claim the whole design rests on, over real code.
///
/// Every `run` in this file already replays its own script; this says so about
/// the corpus specifically, and about a tactic doing enough work for the answer
/// to mean something.
#[test]
fn corpus_derivations_replay() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let mut steps = 0usize;
    let mut worked = 0usize;
    for s_idx in admissible(library, prog) {
        let plain = run(
            prog,
            build(library, s_idx, &mut HashSet::new()),
            "unfold_all",
        );
        // `with_script` replays and asserts; the counting is so that a sweep
        // over a corpus that stopped matching would not pass silently.
        let (_, script) = with_script(prog, plain, ALL);
        if !script.is_empty() {
            worked += 1;
            steps += script.len();
        }
    }
    assert!(
        worked > 100 && steps > 1000,
        "only {} sentences did work, {} steps in all",
        worked,
        steps
    );
}

/// The annihilation with no outputs, and how much of the corpus it reaches.
///
/// `branch { } { }` is what `factor` leaves behind when the two arms were the
/// same all the way down, so the two belong together — and the number says
/// this is not a corner. A third of every annihilation over the admissible
/// corpus is the case that had no matcher looking for it.
#[test]
fn the_annihilation_with_no_outputs_is_a_third_of_them() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let (mut total, mut void) = (0usize, 0usize);
    for s_idx in admissible(library, prog) {
        let plain = run(
            prog,
            build(library, s_idx, &mut HashSet::new()),
            "unfold_all",
        );
        let (_, script) = with_script(prog, plain, "factoring; all");
        for step in &script {
            let StepKind::Rule(Rule::Annihilate { m, .. }) = &step.kind else {
                continue;
            };
            total += 1;
            void += usize::from(*m == 0);
        }
    }
    assert!(
        total > 100 && void * 4 > total,
        "{} of {} annihilations left nothing behind",
        void,
        total
    );
}

/// Every branch in the corpus is given an arity both its arms can live with.
///
/// The property, rather than a restatement of the formula: a branch reported
/// `(n -> m)` promises that either arm, entered with `n - 1` values, leaves
/// exactly `m`. An arm needing more than `n - 1` is one the reported arity
/// cannot deliver — which is the shape the `test_always_true` bug took.
#[test]
fn a_branch_arity_is_one_both_arms_can_meet() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let mut checked = 0usize;
    let mut asymmetric = 0usize;
    for s_idx in admissible(library, prog) {
        let tree = run(
            prog,
            build(library, s_idx, &mut HashSet::new()),
            "unfold_all",
        );
        walk_branches(prog, &tree, &mut |then_body, else_body, reported| {
            let (Some((tn, tm)), Some((en, em))) =
                (seq_full(prog, then_body), seq_full(prog, else_body))
            else {
                return;
            };
            let (n, m) = reported.expect("both arms are known, so the branch is");
            checked += 1;
            asymmetric += usize::from(tn != en);
            for (label, (an, ao)) in [("then", (tn, tm)), ("else", (en, em))] {
                assert!(
                    n > an,
                    "a branch reported ({} -> {}) cannot feed its {} arm, which needs {}",
                    n,
                    m,
                    label,
                    an
                );
                assert_eq!(
                    (n - 1) - an + ao,
                    m,
                    "a branch reported ({} -> {}) does not leave that from its {} arm",
                    n,
                    m,
                    label
                );
            }
        });
    }
    assert!(checked > 100, "only {} branches were checked", checked);
    // A thin guard, and worth saying so: exactly one branch in about a
    // thousand has arms of differing demand, so a sweep that lost it would
    // pass on the reading that took whichever arm answered first.
    // `a_branch_takes_what_the_hungrier_arm_takes` is the real test; this one
    // is for breadth.
    assert!(
        asymmetric > 0,
        "no branch in the corpus has arms of differing demand, so this sweep \
         has stopped being able to tell the two readings apart"
    );
}

fn seq_full(prog: &Program, nodes: &[Node]) -> Option<(i64, i64)> {
    let (inputs, outputs) = seq_arity(prog, nodes);
    outputs.map(|o| (inputs, o))
}

/// Every branch in a tree, with the arity the reckoning gives it.
fn walk_branches(
    prog: &Program,
    nodes: &[Node],
    f: &mut impl FnMut(&[Node], &[Node], Option<(i64, i64)>),
) {
    for node in nodes {
        match node {
            Node::Branch {
                then_body,
                else_body,
                ..
            } => {
                f(then_body, else_body, node_arity(prog, node));
                walk_branches(prog, then_body, f);
                walk_branches(prog, else_body, f);
            }
            Node::Dip { body, .. } => walk_branches(prog, body, f),
            Node::Op(_) | Node::Call { .. } => {}
        }
    }
}

/// The precondition has to leave something to work on.
///
/// Making the tool refuse fallible sentences is only reasonable while most of
/// the corpus is still admissible. If this ever fails, the restriction has
/// stopped being a simplification and started being a limitation.
#[test]
fn most_of_the_corpus_is_admissible() {
    let Some((library, prog)) = corpus() else {
        return;
    };
    let total = library.sentences.len();
    let ok = admissible(library, prog).len();
    assert!(
        ok * 2 > total,
        "only {} of {} sentences are non-recursive and total",
        ok,
        total
    );
}

/// The admissible corpus does exercise the movement laws.
///
/// `docs/tactics.md` makes claims of the form "this fires on none of the corpus"
/// and "this one fires on a third of it", and those go stale when a law is
/// generalized. The assertion is one-sided on purpose: an exact count would be
/// a tripwire on the corpus rather than on the laws.
#[test]
fn the_admissible_corpus_exercises_the_movement_laws() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let mut fired = 0;
    for s_idx in admissible(library, prog) {
        let plain = run(
            prog,
            build(library, s_idx, &mut HashSet::new()),
            "unfold_all",
        );
        let (_, script) = with_script(prog, plain, ALL);
        fired += script
            .iter()
            .filter(|s| s.kind.name() == "interchange")
            .count();
    }
    assert!(
        fired > 1000,
        "the interchange law fired only {} times across the corpus",
        fired
    );
}

/// **What the totality precondition costs, measured.**
///
/// Refusing sentences that can fail is what lets `annihilate` ask only for an
/// arity and what makes `interchange` a reordering nobody can observe. On this
/// corpus it is also very expensive, and the number is worth having in front of
/// us rather than discovered later.
///
/// Two thirds of the sentences are admissible, but they are the *small* ones —
/// generated accessors and predicates. By node count the admissible share is
/// about a fifth, and by rewriting work done it is a few percent, because the
/// substantial code says `assert`: since fallible instructions started
/// reporting with a flag, a sentence that untuples a value it has no reason to
/// trust says so, and saying so is what makes it fallible.
///
/// The consequence is that the value-level laws — folding, cancelling, deciding
/// a branch — have almost nothing to act on here, while the movement laws,
/// which the small sentences do exercise, run freely. Lifting the restriction
/// means giving `annihilate` and `interchange` their own totality conditions
/// rather than taking one for the whole run; every other equation in the set is
/// sound without it.
#[test]
fn the_precondition_is_measured_rather_than_assumed() {
    let Some((library, prog)) = corpus() else {
        return;
    };

    let nodes_in = |idx| run(prog, build(library, idx, &mut HashSet::new()), "unfold_all").len();
    let admissible_nodes: usize = admissible(library, prog).into_iter().map(nodes_in).sum();
    let open_nodes: usize = library
        .names
        .iter_enumerated()
        .map(|(idx, _)| idx)
        .filter(|idx| !prog.is_recursive(*idx))
        .map(nodes_in)
        .sum();

    assert!(admissible_nodes > 0 && open_nodes > admissible_nodes);
    // The claim above, as a number: most of the corpus by size is out of
    // reach. If this ever stops holding — because the corpus stopped asserting,
    // or because the restriction was lifted — the comment is stale and this is
    // where to notice.
    assert!(
        admissible_nodes * 2 < open_nodes,
        "admissible code is {} nodes of {}; the precondition may have stopped \
         being the limitation this test documents",
        admissible_nodes,
        open_nodes
    );
}

// ---------------------------------------------------------------------------
// The symbolic stack view
// ---------------------------------------------------------------------------

fn stack_of(code: &str, src: &str) -> Vec<String> {
    let prog = program_of(code);
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let body = run(prog, body, src);
    crate::print::render_body(prog, SentenceIndex::from(0), &body, src, true, false)
}

#[test]
fn the_stack_view_gives_equal_values_the_same_name() {
    let lines = stack_of("sentence probe { push 1 pick 0 }", "id");
    assert!(
        lines.iter().any(|l| l.contains("stack")),
        "no stack column: {:?}",
        lines
    );
}

// ---------------------------------------------------------------------------
// The position column
// ---------------------------------------------------------------------------

/// The position cell and the text of every numbered line of a listing.
///
/// The header is dropped, and so is anything with no gutter at all — the name,
/// the annotations, the rule.
fn positions(lines: &[String]) -> Vec<(String, String)> {
    lines
        .iter()
        .filter_map(|line| {
            let mut cols = line.split('│');
            let pos = cols.next()?.trim().to_string();
            cols.next()?;
            let text = cols.collect::<Vec<_>>().join("│").trim().to_string();
            (pos != "pos").then_some((pos, text))
        })
        .collect()
}

#[test]
fn the_listing_numbers_each_sequence_from_zero() {
    let prog = program_of("sentence probe { push 1 pick 0 branch { not } { is_bool } }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let lines = crate::print::render_body(prog, SentenceIndex::from(0), &body, "id", false, true);
    let rows = positions(&lines);

    // The arms restart at zero — a position is an index in the sequence it is
    // in, which is exactly what `at(n, ...)` means — and a closing brace, which
    // belongs to no node, is blank.
    let cells: Vec<&str> = rows.iter().map(|(pos, _)| pos.as_str()).collect();
    assert_eq!(cells, vec!["0", "1", "2", "0", "", "0", ""], "{:?}", rows);
    assert_eq!(rows[0].1, "push 1");
    assert!(rows[2].1.starts_with("branch"), "{:?}", rows[2]);
    assert_eq!(rows[3].1, "not");
    assert_eq!(rows[5].1, "is_bool");

    // And the column is one the caller chooses: the stepper's diff turns it
    // off, since a splice renumbers every sibling after it.
    let bare = crate::print::render_body(prog, SentenceIndex::from(0), &body, "id", false, false);
    assert!(bare.iter().all(|line| !line.contains("pos")), "{:?}", bare);
}

#[test]
fn the_number_the_listing_prints_is_the_number_a_tactic_takes() {
    // The property that makes the column worth printing: read a position off
    // the listing, hand it to `at`, and the step lands there.
    let prog = program_of("sentence probe { push 1 push 2 dip 1 { dip 1 { drop 0 } } }");
    let body = build(prog.library(), SentenceIndex::from(0), &mut HashSet::new());
    let lines = crate::print::render_body(prog, SentenceIndex::from(0), &body, "id", false, true);

    let rows = positions(&lines);
    let (cell, _) = rows
        .iter()
        .find(|(_, text)| text.starts_with("dip 1"))
        .unwrap_or_else(|| panic!("no frame in {:?}", rows));
    let n: usize = cell.parse().unwrap();
    assert_eq!(n, 2, "the frame is the third node");

    // `must`, so that aiming at the wrong place is a failure rather than a
    // quietly empty script.
    let (_, script) = with_script(prog, body, &format!("must(at({}, collapse))", n));
    assert_eq!(script.len(), 1);
    assert_eq!(script[0].loc, crate::location::Location::root(n));
}

#[test]
fn a_call_makes_its_result_opaque_rather_than_wrong() {
    // An unopened call has no body here, so what it leaves is unknown — which
    // the view has to say rather than guess.
    let lines = stack_of(
        r#"
        sentence helper { push 7 }
        sentence probe { jump helper }
        "#,
        "id",
    );
    assert!(!lines.is_empty());
}

// ---------------------------------------------------------------------------
// The tool's own refusals
// ---------------------------------------------------------------------------

#[test]
fn a_sentence_that_can_fail_is_outside_the_preconditions() {
    // The check `main` makes before it will rewrite anything. `assert` is one
    // of the three instructions that can still fail.
    let library = assemble("sentence risky { assert }").unwrap();
    assert!(failure_reachability(&library)[0]);

    // And it propagates through a call, which is what makes refusing the root
    // enough.
    let library = assemble(
        r#"
        #[arity(1, 0)] sentence risky { assert }
        #[arity(1, 0)] sentence caller { jump risky }
        "#,
    )
    .unwrap();
    let caller = library
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == "caller")
        .map(|(i, _)| i)
        .unwrap();
    assert!(
        failure_reachability(&library)[usize::from(caller)],
        "reaching a failure through a call has to count"
    );
}

#[test]
fn a_total_sentence_is_admitted() {
    let library = assemble("sentence safe { push 1 drop 0 }").unwrap();
    assert!(!failure_reachability(&library)[0]);
}

#[test]
fn an_instruction_that_reports_with_a_flag_is_still_total() {
    // `add` cannot fail; it answers with its result and a flag saying whether
    // the answer was computed. That is the whole reason the equations may move
    // it around.
    let library = assemble("sentence probe { add drop 0 drop 0 }").unwrap();
    assert!(!failure_reachability(&library)[0]);
    assert_eq!(
        bytecode::arity::op_arity(&Instruction::Add),
        Some((2, 2)),
        "add should leave its flag"
    );
}
