//! Spending a path condition, end to end.
//!
//! `if is_symbol(x) then is_symbol(x) else true` is `true` — the then arm
//! recomputes the very test its branch decided. Three boxes, and the
//! decision procedure does not close it on its own. This is the route that
//! does, one law at a time, because every step of it is a fact about the
//! table worth keeping under test.
//!
//! **Dedup.** The arm's test and the condition's own test read one source,
//! so they are one box. Nothing stands between an arm and what it reads —
//! a branch is a `select` and the `copy` that fed both arms is gone by
//! `copy-elim` — so this is δ-naturality on two boxes like any other pair,
//! and the then block *is* the condition afterwards.
//!
//! **Promise.** `promised-bool` writes down what the instruction set
//! already guarantees: `is_symbol` answers a bool, so `is_symbol` is
//! `is_symbol ; as_bool`. The coercion is a no-op on a value already a
//! bool; what it is for is to *stand there*, a type assertion manifested in
//! the graph.
//!
//! **Specialize.** `specialize-bool` reads it. The rule holds the `as_bool`
//! that made the condition — which is how it says the condition is a bool
//! — and a block answering with that very coercion. A truthy bool is
//! `true`, so the then block folds to `push true`. Both arms then answer
//! alike and the branch collapses.
//!
//! Only the last two steps are the route: identifying the arm's
//! recomputation with the condition is the wiring pass's own work, and
//! what is left is the two rows that are about the machine rather than the
//! wiring.

use bytecode::assemble;
use rewrite::diagram2::rules::Law;
use rewrite::diagram2::{rules, tactic};
use rewrite::goal::Goal;
use rewrite::graph::{Graph, NodeKind, Source, isomorphic};
use rewrite::term::{Context, Prim, TermIndex, lower};

fn term_of(terms: &mut Context, body: &str) -> TermIndex {
    let code = format!("sentence probe {{ {} }}", body);
    let library = assemble(&code).unwrap();
    let idx = library
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == "probe")
        .map(|(idx, _)| idx)
        .expect("the probe is the one sentence");
    lower(terms, &library, idx).expect("the probe lowers")
}

fn drive(graph: &mut Graph, tactic: &tactic::Tactic) {
    let mut deriv = rules::Derivation::default();
    tactic::run(graph, &mut deriv, tactic).expect("the tactic finds its laws");
}

/// A law to fixpoint.
fn saturate(law: Law) -> tactic::Tactic {
    tactic::Tactic::Repeat(Box::new(tactic::fire_first(vec![law])), None)
}

/// The goal as it is built, with only the right side settled: the left is
/// handed over literally, so a test can say which pass does what to it.
fn probe() -> (Context, Goal) {
    let mut ctx = Context::new();
    let lhs = term_of(
        &mut ctx,
        "pick 0 is_symbol branch { is_symbol } { drop 0 push true }",
    );
    let rhs = term_of(&mut ctx, "drop 0 push true");
    let mut goal = Goal::aligned(&mut ctx, lhs, rhs);
    drive(&mut goal.rhs, &tactic::decide());
    (ctx, goal)
}

/// The goal with the wiring laws spent on its left side too — where the
/// route below starts.
fn settled() -> (Context, Goal) {
    let (ctx, mut goal) = probe();
    drive(&mut goal.lhs, &tactic::saturate_structural());
    (ctx, goal)
}

/// A branch's one end: its condition, and its first block.
fn select(graph: &Graph) -> (Source, Source) {
    let (id, _) = graph
        .live()
        .find(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
        .expect("the goal is a branch");
    let sources = graph.sources(id);
    (sources[0], sources[1])
}

/// The two rows the route turns on are about what the machine computes,
/// and no list drives `promised-bool`. So the decision procedure alone
/// still leaves this open, and should.
#[test]
fn the_decision_procedure_does_not_close_it() {
    let (_ctx, mut goal) = settled();
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        !isomorphic(&goal.lhs, &goal.rhs),
        "the table found the route on its own — say so here rather than pretending it did not"
    );
}

/// The arm's test and the condition's test are two boxes on one source
/// once `copy-elim` has run, so the **wiring pass alone** makes the then
/// block the condition itself — which is half of what `specialize-bool` is
/// anchored on.
#[test]
fn the_wiring_pass_makes_the_block_the_condition() {
    let (_ctx, mut goal) = probe();
    let (condition, then_block) = select(&goal.lhs);
    assert_ne!(
        condition, then_block,
        "as built, the arm's test is its own box"
    );

    drive(&mut goal.lhs, &tactic::saturate_structural());
    let (condition, then_block) = select(&goal.lhs);
    assert_eq!(
        condition, then_block,
        "the arm's recomputation was not identified with the condition"
    );
}

/// The whole route, and it closes.
#[test]
fn dedup_promise_specialize() {
    let (_ctx, mut goal) = settled();
    drive(&mut goal.lhs, &saturate(Law::PromisedBool));

    // The other half of the anchor: the condition is manifestly a bool.
    let (condition, _) = select(&goal.lhs);
    let Source::Port { node, .. } = condition else {
        panic!("the condition is a boundary input");
    };
    assert!(
        matches!(goal.lhs.kind(node), NodeKind::Op(Prim::AsBool)),
        "the promise was not written down in front of the branch"
    );

    drive(
        &mut goal.lhs,
        &tactic::fire_first(vec![Law::SpecializeBool]),
    );
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        isomorphic(&goal.lhs, &goal.rhs),
        "the path condition was spent and the goal still did not close"
    );
}
