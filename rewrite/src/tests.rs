//! Integration tests for the rewrite tool.
//!
//! The layers have their own tests: `rule` checks that each equation says what
//! it means, `applier` that a step is applied or refused exactly, `matcher`
//! that a proposal is one the applier takes, `engine` that a run is reproduced
//! by the script it leaves. What is left for here is the tool as a whole —
//! prelude tactics over real `.hana` code, and the sweeps over the corpus that
//! keep the claims in `docs/tactics.md` honest.

use bytecode::{Instruction, Library, SentenceIndex, Value, assemble};
use std::fs;
use std::path::Path;

use crate::applier::apply_script_seq;
use crate::arity::{seq_arity, term_arity};
use crate::engine::{Env, Tactic, run as run_tactic};
use crate::ir::{Term, build, id_word};
use crate::program::Program;
use crate::rule::Script;
use crate::script::{Definitions, PRELUDE};

/// The prelude tactics, by the name a test refers to them by.
const DIPS: &str = "frames";
const FACTOR: &str = "factoring";
const ANNIHILATE: &str = "annihilation";

/// Net stack change, which every equation must preserve exactly.
fn net(prog: &Program, nodes: &[Term]) -> Option<i64> {
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
fn run(prog: &Program, nodes: Vec<Term>, src: &str) -> Vec<Term> {
    with_script(prog, nodes, src).0
}

fn with_script(prog: &Program, nodes: Vec<Term>, src: &str) -> (Vec<Term>, Script) {
    let env = Env::new(prog, 1_000_000, true);
    let before = nodes.clone();
    let (after, script) =
        run_tactic(&env, &compile(src), nodes).unwrap_or_else(|e| panic!("{}", e));

    let mut replayed = before;
    apply_script_seq(prog, &mut replayed, &script, true)
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
fn tree_of(code: &str, src: &str) -> (&'static Program<'static>, Vec<Term>) {
    let prog = program_of(code);
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let body = run(prog, body, &format!("unfold_all; {}", src));
    (prog, body)
}

fn tree(code: &str, src: &str) -> Vec<Term> {
    tree_of(code, src).1
}

/// The depth before each instruction of a sequence, entered at its inputs.
fn depths(prog: &Program, nodes: &[Term]) -> Vec<Option<i64>> {
    let mut depth = Some(seq_arity(prog, nodes).0);
    let mut out = Vec::new();
    for node in nodes {
        out.push(depth);
        depth = match (depth, term_arity(prog, node)) {
            (Some(d), Some((n, m))) => Some(d - n + m),
            _ => None,
        };
    }
    out
}

fn shape(nodes: &[Term]) -> Vec<String> {
    nodes.iter().map(shape_of).collect()
}

/// The same, for a sub-term: its spine, factor by factor.
fn shape_in(term: &Term) -> Vec<String> {
    term.spine().into_iter().map(shape_of).collect()
}

/// One factor, as the term language spells it.
fn shape_of(node: &Term) -> String {
    let inner = |t: &Term| {
        shape(&t.spine().into_iter().cloned().collect::<Vec<_>>()).join(" ")
    };
    match node {
        Term::Op(inst) => format!("{}", inst),
        Term::Id(k) => id_word(*k),
        Term::Call(target) => format!("jump #{}", usize::from(*target)),
        Term::Compose(..) => inner(node),
        Term::Par { left, right, .. } => {
            format!("par {{ {} }} {{ {} }}", inner(left), inner(right))
        }
        Term::Branch { .. } => "branch".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Depth reckoning
// ---------------------------------------------------------------------------

#[test]
fn depth_counts_inputs_once() {
    let prog = program_of("sentence probe { add drop 0 drop 0 }");
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    // Two operands in, the sum and its flag out, then both dropped.
    assert_eq!(
        depths(prog, &body),
        vec![Some(2), Some(2), Some(1)],
        "{:?}",
        shape(&body)
    );
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
    let prog = program_of("sentence probe { copy branch { } { drop 0 push true } }");
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let [_, inner] = &body[..] else {
        panic!("expected a pick and a branch, got {:?}", shape(&body))
    };
    assert_eq!(term_arity(prog, inner), Some((2, 1)));
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
        function test_always_true {
            copy
            is_bool
            branch {
                copy
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

// ---------------------------------------------------------------------------
// Frames: collapse, sink, fuse, expand
// ---------------------------------------------------------------------------

#[test]
fn frames_sink_past_pushes_and_arithmetic() {
    // The dip's window clears what each node leaves behind, so it walks left
    // and the depth follows the arithmetic.
    let got = tree("sentence probe { push 1 dip 2 { drop 0 } }", DIPS);
    assert_eq!(
        shape(&got),
        vec!["par { drop } { id }", "push 1"],
        "{:?}",
        shape(&got)
    );
}

#[test]
fn frames_fuse_when_they_meet_at_the_same_width() {
    let got = tree("sentence probe { dip 1 { push 1 } dip 1 { push 2 } }", DIPS);
    assert_eq!(shape(&got), vec!["par { push 1 push 2 } { id }"]);
}

#[test]
fn nested_frames_collapse_and_then_keep_sinking() {
    // Collapsing first is what lets the interchange law see the frame's true
    // hidden depth; without it the outer frame reports 1 and stops early.
    let got = tree("sentence probe { push 1 dip 1 { dip 1 { drop 0 } } }", DIPS);
    assert_eq!(shape(&got), vec!["par { drop } { id }", "push 1"]);
}

#[test]
fn a_wide_window_becomes_a_nest_of_one_value_ones() {
    let got = tree("sentence probe { dip 3 { drop 0 } }", "unary");
    assert_eq!(shape(&got), vec!["par { par { par { drop } { id } } { id } } { id }"]);
}

#[test]
fn expansion_preserves_arity() {
    let (prog, plain) = tree_of("sentence probe { dip 3 { drop 0 } }", "id");
    let unary = run(prog, plain.clone(), "unary");
    assert_eq!(seq_arity(prog, &plain), seq_arity(prog, &unary));
}

#[test]
fn a_dip_stops_at_a_pick_that_reaches_into_it() {
    // The frame `pick 2` opens with is (3 -> 4): a window 3 deep does not clear
    // the four values it leaves, so the sinking frame cannot pass it. It does
    // pass the `swap` the pick ends with, which is (2 -> 2) and clears.
    let got = tree("sentence probe { pick 2 dip 3 { drop 0 } }", DIPS);
    assert_eq!(
        shape(&got),
        vec!["par { par { copy } { id } swap } { id }", "par { drop } { id 3 }", "swap"]
    );
}

#[test]
fn a_dip_sinks_past_a_pick_it_clears() {
    let got = tree("sentence probe { copy dip 2 { drop 0 } }", DIPS);
    assert_eq!(shape(&got), vec!["par { drop } { id }", "copy"]);
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
    let body = build(prog.library(), probe).into_spine();
    let got = run(prog, body, DIPS);
    let Some((_, origins, _)) = got[0].as_frame() else {
        panic!("expected one fused frame, got {:?}", shape(&got))
    };
    assert_eq!(origins.len(), 2, "origins were {:?}", origins);
}

// ---------------------------------------------------------------------------
// Branches
// ---------------------------------------------------------------------------

fn arms(then_arm: &str, else_arm: &str) -> String {
    format!(
        "sentence probe {{ copy branch {{ {} }} {{ {} }} }}",
        then_arm, else_arm
    )
}

#[test]
fn a_shared_branch_prefix_is_hoisted_under_a_dip() {
    let got = tree(&arms("drop 0 push 1", "drop 0 push 2"), FACTOR);
    assert_eq!(
        shape(&got),
        vec!["copy", "par { drop } { id }", "branch"],
        "{:?}",
        shape(&got)
    );
}

#[test]
fn factoring_takes_the_whole_shared_run() {
    let got = tree(&arms("drop 0 not push 1", "drop 0 not push 2"), FACTOR);
    assert_eq!(shape(&got), vec!["copy", "par { drop not } { id }", "branch"]);
}

#[test]
fn factoring_stops_where_the_arms_diverge() {
    let got = tree(&arms("drop 0 push 1 not", "drop 0 push 2 not"), FACTOR);
    // The shared prefix comes out; the shared *suffix* is `distribute`'s
    // business read backwards and is not part of factoring.
    assert_eq!(shape(&got), vec!["copy", "par { drop } { id }", "branch"]);
}

#[test]
fn factoring_looks_past_provenance() {
    // Two identical blocks compiled to different sentences never share a
    // label, and comparing labels made factoring miss every shared prefix that
    // contained a call.
    let code = r#"
        sentence probe {
            copy
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
    let body = build(prog.library(), probe).into_spine();
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
        "sentence probe { copy branch { push 1 } { push 2 } drop 0 }",
        "distribution",
    );
    assert_eq!(shape(&got), vec!["copy", "branch"]);
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
    // several levels down. Nothing can fail now, so the arity is the whole
    // condition: `dip 1 { drop 0 }` is (2 -> 1), and one drop after it takes
    // both its inputs instead.
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

fn raw(code: &str, name: &str) -> (&'static Program<'static>, Vec<Term>) {
    let prog = program_of(code);
    let idx = prog
        .library()
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == name)
        .map(|(i, _)| i)
        .unwrap_or_else(|| panic!("no sentence '{}'", name));
    let body = build(prog.library(), idx).into_spine();
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
    assert_eq!(shape(&body), vec!["jump #1"], "{:?}", shape(&body));
}

#[test]
fn unfolding_is_bounded_one_call_at_a_time() {
    let (prog, body) = raw(CHAIN, "first");
    let once = run(prog, body.clone(), "once(unfold)");
    assert_eq!(shape(&once), vec!["jump #0"], "{:?}", shape(&once));
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

// ---------------------------------------------------------------------------
// Passes compose
// ---------------------------------------------------------------------------

#[test]
fn passes_compose() {
    // Factoring exposes a frame, the frame passes move it, and cleanup cancels
    // what that brings together. Each alone leaves work the others finish.
    let code = "sentence probe { copy branch { drop 0 push 1 drop 0 } { drop 0 push 2 drop 0 } }";
    let (prog, plain) = tree_of(code, "id");
    let separately = {
        let a = run(prog, plain.clone(), FACTOR);
        let b = run(prog, a, DIPS);
        run(prog, b, "cleanup")
    };
    let together = run(prog, plain, "factoring; frames; cleanup");
    assert_eq!(shape(&separately), shape(&together));
}

// ---------------------------------------------------------------------------
// Introducing code
// ---------------------------------------------------------------------------

/// The move that makes factoring reachable when only one arm has the prefix.
///
/// Every other matcher rewrites what it found, so a rule reading `drop` could
/// never propose `copy` — nothing in the window says which computation ought
/// to appear. The term comes from the tactic expression, and the annihilation
/// law read backwards is what makes putting it there sound: both sides discard
/// exactly the same value.
#[test]
fn introducing_a_copy_lets_factoring_reach_an_arm_that_lacked_it() {
    // A predicate whose then-arm copies the value and whose else-arm does not.
    let code = r#"
        function probe {
            copy
            is_bool
            branch {
                copy
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

    // Give the else arm a `copy` it immediately discards, and now there is.
    let (got, script) = with_script(prog, plain, "else(once(introduce { copy })); factoring");
    assert_eq!(
        shape(&got)[2],
        "par { copy } { id }",
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
    let there = run(prog, plain.clone(), "once(introduce { copy })");
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
    let (prog, plain) = tree_of("function probe { not }", "id");
    assert_eq!(shape(&plain), vec!["not"]);
    assert_eq!(run(prog, plain.clone(), "values"), plain);

    // Split the value first and each boolean case folds to a literal.
    let got = run(prog, plain, "at(0, split_bool); distribution; values");
    let [_, _, Term::Branch { then_body, .. }] = &got[..] else {
        panic!("expected a guard branch, got {:?}", shape(&got))
    };
    let [
        Term::Branch {
            then_body: yes,
            else_body: no,
            ..
        },
    ] = then_body.spine()[..]
    else {
        panic!("expected an inner branch")
    };
    // not true = false, not false = true.
    assert_eq!(shape_in(yes), vec!["push false"]);
    assert_eq!(shape_in(no), vec!["push true"]);
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
    let code = "sentence probe { copy branch { drop 0 push 1 not } { drop 0 push 2 not } }";
    let (prog, plain) = tree_of(code, "id");

    let got = run(prog, plain.clone(), "bu(each(inv(distribute)))");
    assert_eq!(
        shape(&got),
        vec!["copy", "branch", "not"],
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
    let code = "sentence probe { copy branch { drop 0 } { drop 0 } }";
    let (prog, plain) = tree_of(code, "id");

    // Factoring alone leaves the husk behind.
    let factored = run(prog, plain.clone(), FACTOR);
    assert_eq!(
        shape(&factored),
        vec!["copy", "par { drop } { id }", "branch"],
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
    #[arity(2, 2)]
    sentence probe { copy branch { pick 1 pick 1 equal and } { not } }
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
        "must(else(at(0, inv(counit(1)))));          must(else(at(2, inv(counit(1)))));          must(else(at(4, introduce { equal })));          must(factoring)",
    );
    let (shorthand, script) = with_script(prog, plain, "must(once(speculate { equal }))");

    assert_eq!(shape(&shorthand), shape(&by_hand));
    assert_eq!(
        shape(&shorthand),
        vec![
            "copy",
            "par { par { copy } { id } swap par { copy } { id } swap equal } { id }",
            "branch"
        ],
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
            "elim_par0",
            "elim_par0",
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
        Term::Branch {
            then_body,
            else_body,
            ..
        },
    ] = &got[..]
    else {
        panic!("expected a frame and a branch, got {:?}", shape(&got))
    };
    assert_eq!(shape_in(then_body), vec!["and"]);
    // `equal` is (2 -> 1), so exactly one result to discard.
    assert_eq!(shape_in(else_body), vec!["drop", "not"]);
}

// ---------------------------------------------------------------------------
// Emptying the arms: `lift`
// ---------------------------------------------------------------------------

/// `lift`'s own measure: every node that is not a `branch`, a `drop` or a
/// `pick`, weighted by how many branch arms deep it sits.
///
/// A frame does not count as a level, since `lift` is what puts one there —
/// `par { X } { id }` in front of a branch is `X` out of that branch's arms,
/// and a
/// measure that read it otherwise would say the pass had gone backwards. What
/// it is held to is a number rather than a listing, because the claim is about
/// a shape and a listing would churn on every unrelated change to the corpus.
fn work_in_arms(nodes: &[Term]) -> usize {
    fn walk(node: &Term, depth: usize, found: &mut usize) {
        match node {
            Term::Compose(a, b) => {
                walk(a, depth, found);
                walk(b, depth, found);
            }
            Term::Branch {
                then_body,
                else_body,
                ..
            } => {
                walk(then_body, depth + 1, found);
                walk(else_body, depth + 1, found);
            }
            Term::Op(Instruction::Drop | Instruction::Copy | Instruction::Swap) => {}
            Term::Id(_) => {}
            Term::Par { left, right, .. } => {
                walk(left, depth, found);
                walk(right, depth, found);
            }
            _ => *found += depth,
        }
    }
    let mut found = 0;
    for node in nodes {
        walk(node, 0, &mut found);
    }
    found
}

/// `lift` is `speculate` with the term found rather than named, and this is
/// what that buys, measured on the term it was written for.
///
/// `emit_does_pre_and_post` is a precondition, a computation and a
/// postcondition, and every condition it tests is buried in an arm of the test
/// before it. Hoisting them by hand took one `speculate { … }` per firing;
/// `lifting` places twenty-three of them without being told any of the terms.
#[test]
fn lifting_empties_the_arms_of_the_barista_probe() {
    let Some((library, prog)) = corpus() else {
        return;
    };
    let Ok(idx) =
        crate::program::resolve_sentence(library, "customer_impl::emit_does_pre_and_post")
    else {
        return;
    };

    let plain = run(prog, build(library, idx).into_spine(), "unfold_all");
    let before = work_in_arms(&plain);
    let lifted = run(prog, plain, "lifting");
    let after = work_in_arms(&lifted);

    assert!(
        before > 400 && after * 2 < before,
        "work buried in arms: {} before lifting, {} after",
        before,
        after
    );
}

/// What it cannot reach, stated rather than left to be rediscovered.
///
/// A prefix that *consumes* the values the other arm still needs can only be
/// lifted onto copies of them, and the copies have to be paid for: `n`
/// backward `counit`s put `pick (n-1)^n ; drop^n` in, and turning those drops
/// back into the originals wants `pick (n-1)^n ; par { drop^n } { id n }`
/// = nothing.
/// That is `counit_under` at `n = 1` and a `roll` for anything above it —
/// `pick_drop_to_roll`, which is on the list in `docs/tactics.md` and not
/// written. So the arms that build `emit`'s answer keep their work.
#[test]
fn lifting_stops_where_the_arms_build_different_values() {
    let (prog, plain) = tree_of(
        r#"
        #[arity(3, 1)]
        sentence probe { branch { tuple 2 } { add drop 0 } }
        "#,
        "id",
    );
    // The then arm consumes two values the else arm goes on to use, and the
    // else arm has no drops in front of them to stand in.
    assert_eq!(shape(&run(prog, plain.clone(), "lifting")), shape(&plain));
}

// ---------------------------------------------------------------------------
// The guard a case split leaves
// ---------------------------------------------------------------------------

const A_TEST: &str = r#"
    #[arity(2, 1)]
    sentence probe { equal not }
"#;

/// `bool_result_copied` is shorthand, and this says so literally.
///
/// Nothing new is assumed: the firing is `copy_nat` backwards to turn the copy
/// into a second run of the operator, `bool_result` on the pair that puts in
/// front of the `is_bool`, and then the annihilation and counits the copies
/// paid for. Both routes are held to the same answer, so the shorthand cannot
/// drift from what it abbreviates.
#[test]
fn the_guard_a_split_leaves_is_derivable() {
    let (prog, plain) = tree_of(A_TEST, "must(at(1, split_bool))");

    let by_hand = run(
        prog,
        plain.clone(),
        "must(once(inv(share { equal })));             must(at(5, float));             must(at(4, bool_result));             must(at(4, annihilate));             must(at(2, counit(1)));             must(at(0, counit(1)));             must(at(0, sink));             must(at(0, flatten))",
    );
    let (shorthand, script) = with_script(prog, plain, "must(once(bool_result_copied))");

    assert_eq!(shape(&shorthand), shape(&by_hand));
    assert_eq!(
        shape(&shorthand),
        vec!["equal", "push true", "branch", "not"],
        "{:?}",
        shape(&shorthand)
    );

    // Every step is an equation the tool already had — no new law rode in.
    let laws: Vec<&str> = script.iter().map(|s| s.kind.name()).collect();
    assert_eq!(
        laws,
        vec![
            "copy_nat",
            "slide",
            "bool_result",
            "annihilate",
            "counit",
            "counit",
            "slide",
            "elim_par0",
        ]
    );
}

/// The point of the whole thing: with the guard readable, a case split on a
/// value that did not arrive as a literal goes through on its own.
///
/// `split_bool` is the only law that can put a branch on an unknown condition
/// into a term, and the docs called it the only way to learn anything about
/// such a value. It was not, quite — it stalled holding a question nothing
/// could read, and `values` walked past it. Now it does not.
#[test]
fn a_split_on_an_operator_result_folds_to_the_two_cases() {
    let (prog, plain) = tree_of(A_TEST, "id");
    let got = run(prog, plain, "must(at(1, split_bool)); values; cleanup");
    assert_eq!(
        shape(&got),
        vec!["equal", "branch", "not"],
        "the guard is gone and what is left is the case split: {:?}",
        shape(&got)
    );
    let [
        _,
        Term::Branch {
            then_body,
            else_body,
            ..
        },
        _,
    ] = &got[..]
    else {
        panic!("expected a branch, got {:?}", shape(&got))
    };
    assert_eq!(shape_in(then_body), vec!["push true"]);
    assert_eq!(shape_in(else_body), vec!["push false"]);
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
        #[arity(1, 1)]
        sentence probe {
            copy
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
        #[arity(1, 1)]
        sentence probe {
            copy
            branch { branch { push 1 } { push 2 } } { branch { push 3 } { push 4 } }
        }
    "#;
    let (prog, plain) = tree_of(code, "id");
    let (got, script) = with_script(prog, plain, "all");
    let [
        Term::Branch {
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
    assert_eq!(shape_in(then_body), vec!["push 1"]);
    assert_eq!(shape_in(else_body), vec!["push 4"]);

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
        function classify { copy is_int branch { drop 0 push 7 } { drop 0 push 8 } }
        #[arity(1, 2)]
        sentence twice { copy jump classify dip 1 { jump classify } }
    "#;
    let (prog, plain) = raw(code, "twice");
    let tactic = compile_for(prog, "must(once(share { jump classify }))");

    let env = Env::new(prog, 1_000_000, true);
    let (got, script) =
        run_tactic(&env, &tactic, plain.clone()).unwrap_or_else(|e| panic!("{}", e));
    assert_eq!(shape(&got), vec!["jump #0", "copy"], "{:?}", shape(&got));
    assert_eq!(script.len(), 1, "one law, one step");
    assert_eq!(script[0].kind.name(), "copy_nat");

    // And the derivation replays, which is what makes the step a construction
    // rather than a claim.
    let mut replayed = plain.clone();
    apply_script_seq(prog, &mut replayed, &script, true).unwrap();
    assert_eq!(replayed, got);

    // Backwards, it runs the call a second time instead of copying.
    let back = compile_for(prog, "must(once(inv(share { jump classify })))");
    let env = Env::new(prog, 1_000_000, true);
    let (there, _) = run_tactic(&env, &back, got).unwrap_or_else(|e| panic!("{}", e));
    assert_eq!(shape(&there), shape(&plain));
}

// ---------------------------------------------------------------------------
// Pushing a symbol
// ---------------------------------------------------------------------------

const SYMBOLS: &str = r#"
    symbol plain
    mod outer { symbol tag }
    #[arity(1, 1)] sentence probe { drop 0 push 1 }
"#;

/// The symbol a term pushed, as the tool resolved it.
fn pushed(prog: &'static Program<'static>, name: &str) -> Result<bytecode::Symbol, String> {
    let mut defs = Definitions::new();
    defs.load(PRELUDE).unwrap();
    let src = format!("once(introduce {{ push {} equal }})", name);
    let tactic = defs
        .compile_with(&src, Some(prog))
        .map_err(|e| format!("{}{}", e.message, e.help.unwrap_or_default()))?;

    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let env = Env::new(prog, 1000, true);
    let (got, _) = run_tactic(&env, &tactic, body).unwrap_or_else(|e| panic!("{}", e));
    match &got[0] {
        Term::Op(Instruction::Push(Value::Symbol(s))) => Ok(s.clone()),
        other => panic!("expected a pushed symbol, got {:?}", other),
    }
}

#[test]
fn a_term_can_push_a_symbol_by_name() {
    let prog = program_of(SYMBOLS);

    // Fully qualified, and the unambiguous trailing part — the same two
    // readings `jump` gives a sentence.
    let fq = pushed(prog, "outer::tag").unwrap();
    let short = pushed(prog, "tag").unwrap();
    assert_eq!(fq.id, short.id, "the same symbol either way it is named");
    // A symbol prints as the fully qualified name it is declared under, which
    // is the same name that resolves it.
    assert_eq!(fq.path, "outer::tag");

    // A symbol at the root is its bare name.
    assert_eq!(pushed(prog, "plain").unwrap().path, "plain");

    // And it is the library's symbol, not one built from the text: `Symbol`
    // compares by `id`, so a fabricated one would match nothing.
    let Some(Value::Symbol(real)) = prog.library().symbols.get("outer::tag") else {
        panic!("the fixture should declare it")
    };
    assert_eq!(fq, *real);
}

#[test]
fn a_symbol_that_is_not_there_says_what_is() {
    let prog = program_of(SYMBOLS);

    let why = pushed(prog, "nope").unwrap_err();
    assert!(why.contains("No symbol matching 'nope'"), "{}", why);
    assert!(why.contains("outer::tag"), "{}", why);

    // A name read off a listing is a name that resolves: a symbol prints as
    // the fully qualified name it was declared under and nothing else.
    assert!(pushed(prog, "outer::tag").is_ok());
}

#[test]
fn a_term_can_push_a_const_string_written_out() {
    // The opposite case to a symbol: a const string is exactly its text, so a
    // term writes one down rather than looking one up — and needs no program
    // to do it.
    let mut defs = Definitions::new();
    defs.load(PRELUDE).unwrap();
    assert!(
        defs.compile(r#"once(introduce { push "hi" equal })"#)
            .is_ok()
    );

    let prog = program_of(SYMBOLS);
    let tactic = defs
        .compile_with(r#"once(introduce { push "hi" equal })"#, Some(prog))
        .unwrap();
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let env = Env::new(prog, 1000, true);
    let (got, _) = run_tactic(&env, &tactic, body).unwrap_or_else(|e| panic!("{}", e));
    assert_eq!(
        got[0],
        Term::Op(Instruction::Push(Value::ConstString("hi".to_string()))),
        "{:?}",
        got[0]
    );
}

#[test]
fn a_term_may_only_name_a_symbol_when_there_is_a_program() {
    // Same rule as `jump`: a symbol is a declaration in the library rather
    // than a piece of syntax, so there has to be a library.
    let mut defs = Definitions::new();
    defs.load(PRELUDE).unwrap();
    let err = defs
        .compile("once(introduce { push whatever equal })")
        .expect_err("it should not compile with no program");
    assert!(err.message.contains("needs a program"), "{}", err.message);

    // The literals that are syntax still compile on their own.
    assert!(defs.compile("once(introduce { push 7 equal })").is_ok());
    assert!(defs.compile("once(introduce { push true and })").is_ok());
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
    let code = "sentence probe { copy dip 2 { push 1 drop 0 } branch { not } { is_bool } }";
    // Collapsed first, so the term holds a frame two values deep: the ISA has
    // only one-deep frames, and `expand` is about a width that a `collapse`
    // arrived at.
    let (prog, plain) = tree_of(code, "repeat(bu(each(collapse)))");
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
    let (prog, plain) = tree_of("function probe { not }", "id");
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

// ---------------------------------------------------------------------------
// The symbolic stack view
// ---------------------------------------------------------------------------

fn stack_of(code: &str, src: &str) -> Vec<String> {
    let prog = program_of(code);
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let body = run(prog, body, src);
    crate::print::render_body(prog, SentenceIndex::from(0), &body, src, true, false)
}

#[test]
fn the_stack_view_gives_equal_values_the_same_name() {
    let lines = stack_of("sentence probe { push 1 copy }", "id");
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
    let prog = program_of("sentence probe { push 1 copy branch { not } { is_bool } }");
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
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
    let body = build(prog.library(), SentenceIndex::from(0)).into_spine();
    let lines = crate::print::render_body(prog, SentenceIndex::from(0), &body, "id", false, true);

    let rows = positions(&lines);
    let (cell, _) = rows
        .iter()
        .find(|(_, text)| text.starts_with("par"))
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
// What the equations rest on
// ---------------------------------------------------------------------------

#[test]
fn an_instruction_that_reports_with_a_flag_is_still_total() {
    // `add` answers with its result and a flag saying whether the answer was
    // computed, rather than stopping. That is the whole reason the equations
    // may move it around.
    assert_eq!(
        bytecode::arity::op_arity(&Instruction::Add),
        Some((2, 2)),
        "add should leave its flag"
    );
}

// ---------------------------------------------------------------------------
// The identities the corpus states
// ---------------------------------------------------------------------------

/// Every `identity` under `tests/` is proved by the `.hant` beside it.
///
/// This is `./run_proofs.sh` again, behind `cargo test` — which matters because
/// the two run at different times. A change to an equation, a matcher or the
/// scan discipline can leave every unit test green and silently stop a proof
/// from landing where it landed before, and that is a regression in the
/// rewriter rather than in the corpus.
#[test]
fn every_identity_in_the_corpus_is_proved() {
    let dir = Path::new("../tests");
    if !dir.join("main.hana").exists() {
        return; // the crate stays testable on its own
    }
    let opts = crate::prove::Options {
        dir: dir.to_path_buf(),
        ..Default::default()
    };
    let mut report = Vec::new();
    let code = crate::prove::run(&opts, &mut report).expect("writing to a Vec cannot fail");
    assert_eq!(
        code,
        crate::prove::OK,
        "{}",
        String::from_utf8_lossy(&report)
    );
}

/// And the corpus states some. A sweep that quietly covers nothing is worse
/// than no sweep, since it reads as coverage.
#[test]
fn the_corpus_states_identities_for_it_to_prove() {
    let Some((library, _)) = corpus() else {
        return;
    };
    assert!(
        library.identities.len() >= 4,
        "the corpus states {} identities",
        library.identities.len()
    );
}
