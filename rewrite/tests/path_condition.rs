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
//! states as an equation and so already runs in reverse. Then `fork-hoist`
//! lifts the pair out in front of the branch, because the same operation
//! done in both arms was always one operation. Then `dedup` merges it with
//! the condition's own test, since the two now read one source.
//!
//! The hoist has to be `fork-hoist` rather than `fork-dedup`. The two state
//! the same equation and differ in where the answer is read: `fork-dedup`
//! reads it from outside the fork, which is a `view-value` spent in the same
//! breath, and once every arm reads around the fork the fork is dead. The
//! fact would then be true and the shape that can name it gone. `fork-hoist`
//! hands the answer back as a stack slot of the fork's own, so the value
//! stays inside the branch.
//!
//! Every one of those steps works today, and together they land the goal
//! exactly on the shape `specialize-bool` is written for: the fork's slot
//! *is* the condition, and the select's then block reads a view of that
//! slot. One thing still stops it. The rule's pattern puts an `as_bool`
//! between the view and the block — the coercion that makes an arbitrary
//! truthy value into the bool the branch decided — and here the condition is
//! `is_symbol`, which the instruction set already promises is a bool. There
//! is no coercion to match, and no law says `as_bool` of a promised bool is
//! that bool, so none can be introduced.
//!
//! So what is left is not a missing row but a rule that cannot see a
//! condition already in the form it wants: `specialize-bool` needs to accept
//! a block reading the view directly, when the condition's producer promises
//! a bool. That promise has to be *stated* rather than tested, the way
//! `tested-bool` states it — by carrying the producing kind in the payload.
//!
//! When that lands, the last assertion here flips from "does not close" to
//! "closes", and this file becomes its regression test.

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
    for law in [Law::ForkHoist, Law::Dedup] {
        drive(&mut goal.lhs, &tactic::fire_first(vec![law]));
    }

    // The fork is still standing, and the slot it now carries is the
    // condition itself — which is what `specialize-bool` is anchored on.
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

    // And there it stops. `specialize-bool` wants an `as_bool` between the
    // view and the block, and a condition that is already a bool has none.
    drive(&mut goal.lhs, &tactic::decide());
    assert!(
        !diagram2::isomorphic(&goal.lhs, &goal.rhs),
        "a law now spends the path condition — flip this assertion"
    );
}

/// The fork a branch still has, and its arity.
fn fork_of(graph: &Graph) -> Option<(rewrite::diagram2::NodeId, usize)> {
    graph.live().find_map(|(id, kind)| match kind {
        NodeKind::Fork { arity, .. } => Some((id, *arity)),
        _ => None,
    })
}

/// The else arm drops its view of the value; compute `is_symbol` on it
/// first, so that both arms do the one thing `fork-hoist` can lift out.
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
