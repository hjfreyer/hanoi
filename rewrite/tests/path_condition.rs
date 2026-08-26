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
//! **Identify.** A branch's two views of a value are a `copy`, so
//! `copy-elim` makes both arms read the one wire and `dedup` makes the two
//! tests one box. That box *is* the condition, which is the whole of what
//! this step is for.
//!
//! This is where the route used to spend `fork-hoist` and lose a step
//! arguing about which hoist to spend: a `fork` was a copy under another
//! name, and `fork-hoist` versus `fork-dedup` was a choice about whether
//! the answer came back through it. The views are an ordinary copy now and
//! the two laws that took them apart are gone, so the same identification
//! is `copy-elim` and `dedup` — laws that were here before branches were.
//!
//! **Promise.** `promised-bool` writes down what the instruction set
//! already guarantees: `is_symbol` answers a bool, so `is_symbol` is
//! `is_symbol ; as_bool`. The coercion is a no-op on a value already a
//! bool; what it is for is to *stand there*, a type assertion manifested in
//! the graph.
//!
//! **Specialize.** `specialize-bool` reads it. The rule holds the `as_bool`
//! that made the condition and the select that discards the untaken block,
//! and it fires where one wire is both the condition and a block. A truthy
//! bool is `true`, so that block folds to the literal — and the rest is
//! ordinary rewriting.
//!
//! A condition that is a *conjunction* — which is the shape the corpus's
//! contract claims actually have — is the same route with a wider widening:
//! the else arm has to be given the whole of what the then arm recomputes
//! before the identification has a pair to make one, one backward
//! `dead-node` per box. Nothing new is needed for it, and it is not written
//! out here.

use bytecode::assemble;
use rewrite::diagram2::rules::{Direction, Law, Match, Rule, Step};
use rewrite::diagram2::{self, Graph, NodeKind, Source, rules, tactic};
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

/// The goal, with the wiring laws that do not touch the branch spent on it.
///
/// `copy-elim` is held back on purpose: the widening below reads the else
/// arm's own view of the value, so the copy that hands the two arms their
/// views has to be standing when it runs.
fn probe() -> (Context, Goal) {
    let mut ctx = Context::new();
    let lhs = term_of(
        &mut ctx,
        "pick 0 is_symbol branch { is_symbol } { drop 0 push true }",
    );
    let rhs = term_of(&mut ctx, "drop 0 push true");
    let mut goal = Goal::aligned(&mut ctx, lhs, rhs);
    drive(
        &mut goal.lhs,
        &tactic::Tactic::Repeat(
            Box::new(tactic::fire_first(vec![
                Law::DeadNode,
                Law::IdElim,
                Law::SwapElim,
            ])),
            None,
        ),
    );
    drive(&mut goal.rhs, &tactic::decide());
    (ctx, goal)
}

/// The copy a branch hands its arms their views with, and its width.
fn views_of(graph: &Graph) -> Option<(rewrite::diagram2::NodeId, usize)> {
    graph.live().find_map(|(id, kind)| match kind {
        NodeKind::Copy(n) => Some((id, *n)),
        _ => None,
    })
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

/// The else arm drops its view of the value; compute `is_symbol` on it
/// first, so both arms do the one thing the identification can make one.
fn widen(graph: &mut Graph) {
    let (copy, arity) = views_of(graph).expect("the arms' views are still a copy");
    // Outputs `0..arity` are the then view, `arity..2 * arity` the else.
    let step = Step {
        rule: Rule::DeadNode {
            kind: NodeKind::Op(Prim::IsSymbol),
        },
        dir: Direction::Backward,
        at: Match {
            nodes: Vec::new(),
            inputs: vec![Source::Port {
                node: copy,
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

/// The identification leaves the then block reading the condition itself —
/// which is what `specialize-bool` is anchored on.
#[test]
fn identifying_the_two_tests_makes_the_block_the_condition() {
    let (_ctx, mut goal) = probe();
    let (condition, then_block) = select(&goal.lhs);
    assert_ne!(
        condition, then_block,
        "before the route the arm's test is its own box"
    );

    widen(&mut goal.lhs);
    drive(&mut goal.lhs, &saturate(Law::CopyElim));
    drive(&mut goal.lhs, &saturate(Law::Dedup));

    let (condition, then_block) = select(&goal.lhs);
    assert_eq!(
        condition, then_block,
        "the two tests are still two boxes, so there is nothing to specialize on"
    );
}

/// The whole route, and it closes.
#[test]
fn widen_identify_promise_specialize() {
    let (_ctx, mut goal) = probe();
    widen(&mut goal.lhs);
    drive(&mut goal.lhs, &saturate(Law::CopyElim));
    drive(&mut goal.lhs, &saturate(Law::Dedup));
    drive(&mut goal.lhs, &saturate(Law::PromisedBool));

    // The other half of the anchor: the condition is manifestly a bool.
    let (condition, _) = select(&goal.lhs);
    let Source::Port { node, .. } = condition else {
        panic!("the condition is a boundary input");
    };
    assert!(
        matches!(goal.lhs.kind(node), NodeKind::Op(Prim::AsBool)),
        "the promise was not written down on the condition"
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
