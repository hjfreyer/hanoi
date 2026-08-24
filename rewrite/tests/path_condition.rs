//! Spending a path condition, end to end.
//!
//! `if is_symbol(x) then is_symbol(x) else true` is `true` — the then arm
//! recomputes the very test its branch decided. Three boxes, and the
//! decision procedure does not close it on its own. This is the route that
//! does, one law at a time, because every step of it is a fact about the
//! table worth keeping under test.
//!
//! **Widen.** The else arm drops its view of `x`; compute `is_symbol` on it
//! first and drop *that* instead, so both arms do the same work. That is
//! `dead-node` backwards — a rule is an equation and an equation runs both
//! ways — and it is the one deliberate step, the move no driver makes on
//! its own. Everything after it is the table's own business.
//!
//! **Hoist.** `fork-hoist` lifts the pair out in front of the branch,
//! because the same operation done in both arms was always one operation.
//! It has to be `fork-hoist` and not `fork-dedup`: the two state the same
//! equation and differ in where the answer is read, and `fork-dedup` reads
//! it from outside the fork — a `view-value` spent in the same breath.
//! Once every arm reads around a fork the fork is dead, and the anchor the
//! rest of this needs would be gone. `fork-hoist` hands the answer back as
//! a stack slot of the fork's own.
//!
//! **Dedup.** The hoisted test and the condition's own test now read one
//! source, so they are one box. The fork's slot *is* the condition.
//!
//! **Promise.** `promised-bool` writes down what the instruction set
//! already guarantees: `is_symbol` answers a bool, so `is_symbol` is
//! `is_symbol ; as_bool`. The coercion is a no-op on a value already a
//! bool; what it is for is to *stand there*, a type assertion manifested in
//! the graph.
//!
//! **Specialize.** `specialize-bool` reads it. The rule holds the `as_bool`
//! in front of the fork — which is how it says the condition is a bool —
//! and the fork's slot, and the block reading that slot's view. A truthy
//! bool is `true`, so the then block folds to `push true`. Both arms then
//! answer alike and the branch collapses.
//!
//! One arm's worth of work is widened here because the arm recomputes one
//! box. A condition that is a *conjunction* — which is the shape the
//! corpus's contract claims actually have — is the same route with a wider
//! widening: the else arm has to be given the whole of what the then arm
//! recomputes before `fork-hoist` has a pair to lift, one backward
//! `dead-node` per box. Nothing new is needed for it, and it is not written
//! out here.

use bytecode::assemble;
use rewrite::diagram2::rules::{Direction, Law, Match, Rule, Step};
use rewrite::diagram2::{self, Graph, NodeId, NodeKind, Source, rules, tactic};
use rewrite::goal::Goal;
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

/// The goal, cleaned up by the wiring laws alone — which leave the branch
/// layer's anchors standing, since only `view-value` re-points a fork's
/// outputs and `dead-node` only takes a fork nothing reads.
fn probe() -> (Context, Goal) {
    let mut ctx = Context::new();
    let lhs = term_of(
        &mut ctx,
        "pick 0 is_symbol branch { is_symbol } { drop 0 push true }",
    );
    let rhs = term_of(&mut ctx, "drop 0 push true");
    let mut goal = Goal::aligned(&mut ctx, lhs, rhs);
    drive(&mut goal.lhs, &tactic::saturate_structural());
    drive(&mut goal.rhs, &tactic::decide());
    (ctx, goal)
}

/// The fork a branch still has, and its arity.
fn fork_of(graph: &Graph) -> Option<(NodeId, usize)> {
    graph.live().find_map(|(id, kind)| match kind {
        NodeKind::Fork { arity, .. } => Some((id, *arity)),
        _ => None,
    })
}

/// The one end of a branch that every branch has: its condition, and its
/// first block.
fn select(graph: &Graph) -> (Source, Source) {
    let (id, _) = graph
        .live()
        .find(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
        .expect("the goal is a branch");
    let sources = graph.sources(id);
    (sources[0], sources[1])
}

/// The else arm drops its view of the value; compute `is_symbol` on it
/// first, so both arms do the one thing `fork-hoist` can lift out.
fn widen(graph: &mut Graph) {
    let (fork, arity) = fork_of(graph).expect("the wiring laws leave the fork standing");
    // Outputs `0..arity` are the then view, `arity..2 * arity` the else.
    let step = Step {
        rule: Rule::DeadNode {
            kind: NodeKind::Op(Prim::IsSymbol),
        },
        dir: Direction::Backward,
        at: Match {
            nodes: Vec::new(),
            inputs: vec![Source::Port {
                node: fork,
                port: arity,
            }],
            outputs: Vec::new(),
            branches: Vec::new(),
        },
    };
    rules::Derivation::default()
        .push(graph, step)
        .expect("the table accepts the backward dead-node");
}

/// Nothing here is automatic. The widening is a deliberate step — no driver
/// invents work for an arm that was throwing its input away — so the
/// decision procedure alone still leaves this open, and should.
#[test]
fn the_decision_procedure_does_not_close_it() {
    let (_ctx, mut goal) = probe();
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        !diagram2::isomorphic(&goal.lhs, &goal.rhs),
        "the table found the route on its own — say so here rather than pretending it did not"
    );
}

/// Widening is `dead-node` run backwards, and the table takes it.
#[test]
fn the_table_runs_dead_node_backwards() {
    let (_ctx, mut goal) = probe();
    let before = goal.lhs.live_count();
    widen(&mut goal.lhs);
    assert_eq!(
        goal.lhs.live_count(),
        before + 1,
        "the backward step introduced no box"
    );
    goal.lhs.check().expect("and left a well-formed graph");
}

/// The hoist keeps the fork, and leaves its new slot holding the condition
/// — which is half of what `specialize-bool` is anchored on.
#[test]
fn the_hoist_leaves_the_slot_holding_the_condition() {
    let (_ctx, mut goal) = probe();
    let (condition, then_block) = select(&goal.lhs);
    assert_ne!(
        condition, then_block,
        "before the route the arm's test is its own box"
    );

    widen(&mut goal.lhs);
    for law in [Law::ForkHoist, Law::Dedup] {
        drive(&mut goal.lhs, &tactic::fire_first(vec![law]));
    }

    let (fork, arity) = fork_of(&goal.lhs).expect("the hoist keeps the fork");
    let (condition, then_block) = select(&goal.lhs);
    assert_eq!(
        goal.lhs.sources(fork)[arity],
        condition,
        "the fork's hoisted slot is not the condition"
    );
    assert_eq!(
        then_block,
        Source::Port {
            node: fork,
            port: arity - 1
        },
        "the then block does not read the view of the hoisted slot"
    );
}

/// The whole route, and it closes.
#[test]
fn widen_hoist_dedup_promise_specialize() {
    let (_ctx, mut goal) = probe();
    widen(&mut goal.lhs);
    drive(&mut goal.lhs, &tactic::fire_first(vec![Law::ForkHoist]));
    drive(&mut goal.lhs, &saturate(Law::Dedup));
    drive(&mut goal.lhs, &saturate(Law::PromisedBool));

    // The other half of the anchor: the condition is manifestly a bool.
    let (condition, _) = select(&goal.lhs);
    let Source::Port { node, .. } = condition else {
        panic!("the condition is a boundary input");
    };
    assert!(
        matches!(goal.lhs.kind(node), NodeKind::Op(Prim::AsBool)),
        "the promise was not written down in front of the fork"
    );

    drive(
        &mut goal.lhs,
        &tactic::fire_first(vec![Law::SpecializeBool]),
    );
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        diagram2::isomorphic(&goal.lhs, &goal.rhs),
        "the path condition was spent and the goal still did not close"
    );
}
