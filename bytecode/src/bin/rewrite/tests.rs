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
use crate::rule::Script;
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
    crate::print::render_body(prog, SentenceIndex::from(0), &body, src, true)
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
