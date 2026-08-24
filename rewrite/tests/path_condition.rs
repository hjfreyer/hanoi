//! Spending a path condition: how close the table gets, and on what it stops.
//!
//! `if is_symbol(x) then is_symbol(x) else true` is `true` — the then arm
//! recomputes the very test its branch decided. Three boxes, and the
//! decision procedure does not close it. This pins down why, because the
//! reason is one law wide and the route to it is worth keeping.
//!
//! The route is: **widen, hoist, dedup.** The else arm drops its view of
//! `x`; compute `is_symbol` on it first and drop *that* instead, so both
//! arms do the same work — `dead-node`, backwards, which the table already
//! states as an equation and so already runs in reverse. Then `fork-dedup`
//! lifts the pair out in front of the branch, because the same operation
//! done in both arms was always one operation. Then `dedup` merges it with
//! the condition's own test, since the two now read one source.
//!
//! Every one of those steps works today, and together they land the goal on
//! `select(c, c, true)` — the select's then block reading the **condition's
//! own port**. That is the whole hypothesis a rule would need, and no rule
//! reads it:
//!
//! - `specialize-bool` says exactly this, and says it of a block reading a
//!   *fork view* of the condition. `fork-dedup` routes the value around the
//!   fork rather than through it, so by the time the fact is true the shape
//!   it is stated for is gone. It is not that the driver fires the laws in
//!   an unlucky order — the hoist is what establishes the fact, and the
//!   hoist is what empties the fork.
//! - `select-const` reaches a fork-less select, and only with a *literal*
//!   condition. This one is computed.
//!
//! So the missing row is `select-const`'s neighbour: at a select, a block
//! reading the condition's own port is `true` on the then side and `false`
//! on the else side, whenever the condition comes from an operation the
//! instruction set promises yields a bool. The promise is load-bearing —
//! with a truthy non-bool condition like `5` the then block is `5`, not
//! `true`.
//!
//! When that law lands, the last assertion here flips from "does not close"
//! to "closes", and this file becomes its regression test.

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

/// The one end of a branch that every branch has, and what it reads.
fn select(graph: &Graph) -> (Source, Source) {
    let (id, _) = graph
        .live()
        .find(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
        .expect("the goal is a branch");
    let sources = graph.sources(id);
    (sources[0], sources[1])
}

#[test]
fn the_decision_procedure_does_not_close_it() {
    let (_ctx, mut goal) = probe();
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        !diagram2::isomorphic(&goal.lhs, &goal.rhs),
        "the table closed this on its own — delete this file and the law it asks for"
    );
}

/// Widening the else arm is `dead-node` run backwards, and the table takes
/// it: a rule is an equation, and an equation runs both ways.
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

/// Widen, hoist, dedup — and the then block comes to read the condition's
/// own port. That is the fact a proof needs and the last one the table can
/// establish on its own.
#[test]
fn the_route_reaches_the_fact_and_stops() {
    let (_ctx, mut goal) = probe();

    let (condition, then_block) = select(&goal.lhs);
    assert_ne!(
        condition, then_block,
        "before the route the arm's test is its own box"
    );

    widen(&mut goal.lhs);
    for law in [Law::ForkDedup, Law::Dedup] {
        drive(&mut goal.lhs, &tactic::fire_first(vec![law]));
    }

    let (condition, then_block) = select(&goal.lhs);
    assert_eq!(
        condition, then_block,
        "the route did not identify the then block with the condition"
    );

    // And there it stops. Nothing in the table reads that fact: the whole
    // branch layer, the wiring laws and the value layer, to fixpoint, do
    // not turn `select(c, c, true)` into `true`.
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        !diagram2::isomorphic(&goal.lhs, &goal.rhs),
        "a law now spends the path condition — flip this assertion"
    );
}

/// The else arm drops its view of the value; compute `is_symbol` on it
/// first, so that both arms do the one thing `fork-dedup` can lift out.
fn widen(graph: &mut Graph) {
    let (fork, arity) = graph
        .live()
        .find_map(|(id, kind)| match kind {
            NodeKind::Fork { arity, .. } => Some((id, *arity)),
            _ => None,
        })
        .expect("the wiring laws leave the fork standing");
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
