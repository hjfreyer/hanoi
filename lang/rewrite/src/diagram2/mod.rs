//! The literal diagram: a term as a graph of boxes, rewritten until the
//! connections are direct.
//!
//! A term becomes a graph **one leaf at a time**, `id`, `swap`, `copy` and
//! `drop` each getting a box of their own, and only then does anything get
//! simplified — by rewriting, against the table in [`rules`]. Nothing is
//! simplified by representation beyond what the wiring cannot say
//! ([docs/rules.md](../../../../docs/rules.md) opens with that list): the
//! point of the literal reading is that every other identification is a
//! *step*, named, checked, and on the record.
//!
//! The graph itself is [`crate::graph`] — boxes, the links between them,
//! well-formedness, and whether two of them are the same diagram. What is
//! here is everything that knows a graph came from a *term* and is headed
//! back to one: [`build`] writes one, [`read_back`] reads one out,
//! [`inline`] opens a call in place, and [`rules`] and [`tactic`] are the
//! table and the driving of it.
//!
//! A branch is not one box either, and that is the one place this is not a
//! literal reading of the term. It is **two**, with its arms as ordinary
//! boxes in between: a `fork(n)` hands each arm its own view of the stack,
//! both arms run, and the `select(n)` it is paired with keeps one of the
//! two answers. That `fork` is exactly the `(pick (n-1))^n` of the
//! single-arm hoist in [docs/totality.md](../../../../docs/totality.md), and the
//! hoist is why the translation is allowed: every prim is total and has no
//! effect but the stack, so work on the path not taken costs an answer
//! nobody reads rather than a failure.
//!
//! The gain is that an arm is no longer opaque — a rule reaches into one
//! from outside, and a value reaches out. The price is the fork, which is a
//! `copy` in everything but name and is a separate kind only so that
//! `copy-elim` leaves it alone. Deleting it would cost the one fact nothing
//! else records: which port is an arm's *own* view of a value. A rule that
//! holds on one side of a branch and not the other — `specialize-equal`,
//! where a value that tested `equal` to a literal is that literal in the
//! then arm — has nowhere to write its answer once both arms read the same
//! port.
//!
//! **Both ends read the condition, and both read it at port 0.** A fork
//! does not compute with it; it reads it so that a rule anchored there can
//! *name* it. That matters because a rule is a local window and the arms
//! lie between the two ends, so no window holds both: `specialize-equal`
//! has to be stated at the fork, and its left-hand side has to mention the
//! `equal` that decides the branch. Reading the condition at the same port
//! on both ends is what makes such a rule say the same thing whichever end
//! it is written at. Two readers of one port is a `copy`, which
//! [`build`] emits and `copy-elim` takes back out, so a built graph is
//! still a wiring diagram and the rewritten one still has both ends on the
//! one source.
//!
//! ## The rules
//!
//! Each one is a **pair of graphs** [`rules::sides`] builds from a payload
//! — the whole of what a rule *is* — and a rewrite is pointing at a
//! subgraph isomorphic to the first and putting the second in its place.
//! Four of them delete a box and join what it was standing between:
//!
//! - `id-elim` — the readers of an `id`'s output read its input instead.
//! - `swap-elim` — the two lines cross by being re-pointed, and the
//!   crossing stops existing. σ involutive, σ-natural and Yang–Baxter all
//!   fall out of the fact that nothing recorded the crossing afterwards.
//! - `copy-elim` — both of a `copy`'s outputs come to name the port it was
//!   reading, and that port acquires a *second reader*. This is the one
//!   rule that changes the shape of the data rather than shrinking it, and
//!   it is where the cartesian structure enters: a value is produced once
//!   and read freely.
//! - `dead-node` — a node nothing reads is deleted, and its own producers
//!   are asked the same question. `drop(n)` has no outputs at all, so it is
//!   this rule's base case rather than a rule of its own; the language is
//!   total and pure, which is what licenses deleting the work underneath —
//!   the same license that lets both arms of a branch run. Its side
//!   condition is not tested but *stated*: the left side of the pair
//!   exports no port at all, so a box with a reader is not that graph.
//!
//! One does not, and it is the reason a table is worth having over a
//! `match`:
//!
//! - `dedup` — δ-naturality. Two boxes of one kind reading one set of
//!   sources are one box read twice, so `push 9 ; push 9` and `push 9 ;
//!   copy(1)` settle in the same place. It refuses a `fork`, for the reason
//!   the `fork` exists.
//!
//! What the rules leave is a DAG of `Op`s, `Call`s and `Fork`/`Select`
//! pairs whose
//! ports fan out where a `copy` used to be — the same shape `diagram`
//! arrives at by construction, reached instead by named rewrites over data
//! that existed the whole way.
//!
//! ## Nothing here spends them
//!
//! There was a `rewrite` in this module — a worklist that ran
//! [`rules::structural`] to fixpoint, and the only way a graph ever got
//! smaller. It is gone, and the rules and the laws it spent are untouched.
//! What it decided was fixed: *those* laws, in *that* order, everywhere
//! they fired, chosen here rather than by whoever is proving something. A
//! choice of laws and of where to spend them is a strategy, and strategies
//! are written in [`crate::hant`]; this is a table and the operations that
//! read it, and the driver comes back as a tactic over both.
//!
//! So a graph out of [`build`] is the literal translation and stays that
//! way until something applies a rule to it. [`rules`] is where that
//! happens: [`rules::sides`] turns a payload into the [`Pair`] of graphs it
//! states, [`find`](crate::graph::find) and [`rules::propose`] say where a
//! law could fire, [`rules::apply`] fires one and hands back its inverse,
//! and [`rules::replay`] runs a list of them. Only the first of those is
//! this module's own work — the rest is [`Pair::apply`] wearing a law's
//! name.
//!
//! **Ports link to ports; there is no wire** — [`crate::graph`]'s doing, and
//! what makes a rewrite here a re-pointing rather than a declaration that
//! two names are equivalent. An input names the one output port it reads
//! ([`Source`]) and an output names the input ports that read it
//! ([`Sink`](crate::graph::Sink)),
//! so nothing accumulates: after each step the graph is already in its final
//! state, which is what makes `dead-node` an O(1) test and lets
//! [`Graph::check`] hold every link to agreeing at both ends — a
//! half-updated link is caught where it happens rather than surviving as a
//! wrong answer.
//!
//! **Two boundaries are drawn on purpose**, and they moved when the old
//! `diagram` engine retired and this module became the prover's:
//!
//! - **Equality is one question, asked at the end.** [`isomorphic`](crate::graph::isomorphic) says
//!   whether two graphs are the same diagram, and [`crate::strategy`]'s
//!   closer asks it once, after driving both sides through the table.
//!   Nothing here saturates toward a canonical form by decree: `push 1 ;
//!   push 2 ; add` and `push 2 ; push 1 ; add` are related exactly when a
//!   strategy spends the laws that relate them. The tests still hold the
//!   *wiring* laws to the `meaning` oracle, which evaluates a program with
//!   **every operation left opaque** — `add` on two wires stays `add(x,
//!   y)` — so the oracle judges the wiring and nothing else.
//! - **The value folds live in [`rules::folding`], not in
//!   [`rules::structural`].** A literal window runs on the machine itself
//!   (`rules::Rule::Fold` and its kin), but only when a strategy fires it:
//!   the structural list still spends no value, so a graph shrinks by
//!   wiring alone until whoever is proving something asks for more.
//!
//!   Layer 2 **is** in the table — [`rules::branching`] folds a literal
//!   condition into its arm, deletes a branch whose arms answer alike,
//!   lifts work both arms do out in front, and writes what a test decided
//!   into the block that tested it. It is not in [`rules::structural`]
//!   either, for two reasons worth keeping apart: three of those
//!   laws turn on what an operation *computes*, which the opaque oracle
//!   cannot judge and `vm` can; and the other three take a branch apart,
//!   which is a strategy, and this module decides no strategy.
//!
//!   A rule that folds a branch carries its **arms as payload**, the way
//!   the term version carried subterms, so the window holds the whole
//!   branch: `select-literal` takes the fork, both arms and the select
//!   together, and no rule leaves one end of a branch standing without the
//!   other. `rules` says which laws hold one end, which hold a whole
//!   branch, and what each can say as a result.
//!
//! [`read_back`] is the other half of the translation: a graph is scheduled
//! onto a stack, and the routing between one step and the next is *layered*
//! — one `*`-product of `copy`/`id`/`drop` to get the multiplicities right,
//! then a `*`-product of `swap`s per transposition round to get the order
//! right. A box is placed where its operands already sit rather than on
//! top, so the survivors pass either side of it and nothing is dragged up
//! and put back; `pick 1` comes back as `copy(1) * id(1) ; id(1) * swap`.
//! That is a choice about legibility and nothing more. What comes back is
//! not the term it was built from — a branch in particular reads back as
//! both arms run flat and then a branch that throws one answer away, which
//! is what the graph now says a branch is.

use std::collections::HashSet;

use bytecode::{Library, SentenceIndex};

use crate::graph::{Direction, Graph, Match, NodeId, NodeKind, Pair, Source, schedule};
use crate::term::{Context, Prim, Term, TermIndex, lower};

#[cfg(test)]
mod meaning;
pub mod query;
pub mod render;
pub mod rules;
pub mod tactic;

// ---- a term, literally ---------------------------------------------------------

/// The graph of a term: one node per leaf, nothing simplified.
///
/// Every law of the structural layer still has a spelling here, which is
/// the difference from [`crate::diagram`] and the whole premise of the
/// module — the table in [`rules`] is what spends them.
pub fn build(terms: &Context, term: TermIndex) -> Graph {
    let arity = terms.arity(term);
    let mut graph = Graph::empty(arity.inputs);
    let inputs: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();
    let outputs = emit(&mut graph, terms, term, inputs);
    graph.close(outputs);
    graph
}

/// One term on the sources standing for its inputs, deepest first,
/// answering with the sources standing for its outputs.
fn emit(graph: &mut Graph, terms: &Context, term: TermIndex, inputs: Vec<Source>) -> Vec<Source> {
    debug_assert_eq!(
        inputs.len(),
        terms.arity(term).inputs,
        "the caller cuts by arity"
    );
    match terms.get(term) {
        Term::Id(n) => graph.add(NodeKind::Id(*n), inputs),
        Term::Copy(n) => graph.add(NodeKind::Copy(*n), inputs),
        Term::Drop(n) => graph.add(NodeKind::Drop(*n), inputs),
        Term::Op(prim) => graph.add(NodeKind::Op(prim.clone()), inputs),
        Term::Call { target, arity } => graph.add(
            NodeKind::Call {
                target: *target,
                arity: *arity,
            },
            inputs,
        ),
        // `;` is not a node: sequencing is one box's output port being
        // another's input.
        Term::Compose(first, then) => {
            let middle = emit(graph, terms, *first, inputs);
            emit(graph, terms, *then, middle)
        }
        // `*` is not a node either: side by side is two boxes sharing no
        // ports. The second argument gets the top, as it does in the term.
        Term::Par(deep, top) => {
            let mut inputs = inputs;
            let above = inputs.split_off(inputs.len() - terms.arity(*top).inputs);
            let mut outputs = emit(graph, terms, *deep, inputs);
            outputs.extend(emit(graph, terms, *top, above));
            outputs
        }
        // A branch is not a node either, and this is the change from the
        // arms-in-a-box it used to be: the condition is set aside, a `fork`
        // hands each arm its own view of the stack, both arms are emitted
        // into this same graph, and the `select` it is paired with keeps one
        // of the two answers. What was a boundary is now two boxes with the
        // arms between them, so every rule reaches through it — and the one
        // fact the boundary carried, which arm a value belongs to, is still
        // written down.
        Term::Branch { if_true, if_false } => {
            let mut inputs = inputs;
            let cond = inputs.pop().expect("a branch reads its condition");
            let branch = graph.next_branch();
            // Block-wise, exactly the `(pick (n-1))^n` the hoist rule spells
            // out. Arms that take nothing have no views to tell apart, and
            // then the `select` is the only end there is to read the
            // condition.
            let (if_true_in, if_false_in, chooses) = if inputs.is_empty() {
                (Vec::new(), Vec::new(), cond)
            } else {
                // Both ends read the condition, and two readers of one port
                // is a `copy` — said outright here rather than smuggled in,
                // so a built graph is still monogamous and `copy-elim` is
                // still the one thing that breaks it.
                let views = graph.add(NodeKind::Copy(1), vec![cond]);
                let arity = inputs.len();
                let mut takes = vec![views[0]];
                takes.extend(inputs);
                let mut blocks = graph.add(NodeKind::Fork { arity, branch }, takes);
                let above = blocks.split_off(arity);
                (blocks, above, views[1])
            };
            let mut ports = vec![chooses];
            ports.extend(emit(graph, terms, *if_true, if_true_in));
            ports.extend(emit(graph, terms, *if_false, if_false_in));
            let arity = terms.arity(*if_true).outputs;
            graph.add(NodeKind::Select { arity, branch }, ports)
        }
    }
}

/// Opens calls in place: every [`NodeKind::Call`] — or, with `only`, every
/// call to that one sentence — replaced by the graph of its body, its
/// readers re-pointed at what the body leaves.
///
/// Definitional unfolding, not a law: this is [`build`]'s work continued —
/// the same [`build`], spliced in where the call was — and it changes what
/// is provable exactly the way the term version did, which is why it is a
/// proof step and never a rewrite the table proposes. Unlabelled, it opens
/// all the way down (recursion is forbidden, so the walk drains); labelled,
/// one pass, and the opened body's own calls stay shut.
///
/// It is a [`Pair::apply`] like any other, and that is the point: the pair
/// is the call's own one-box window against the body's graph — equal by
/// definition rather than by any law — and the [`Match`] is read straight
/// off the call, since a window of one box that exports every port has
/// nothing left to choose. What makes the splice safe is what makes every
/// splice safe, so nothing here re-points a link by hand.
///
/// Answers how many calls it opened — zero is the caller's business to
/// refuse.
pub fn inline(
    graph: &mut Graph,
    terms: &mut Context,
    library: &Library,
    only: Option<SentenceIndex>,
) -> Result<usize, crate::term::Error> {
    let mut opened = 0;
    loop {
        let calls: Vec<(NodeId, SentenceIndex)> = graph
            .live()
            .filter_map(|(id, kind)| match kind {
                NodeKind::Call { target, .. } if only.is_none_or(|t| t == *target) => {
                    Some((id, *target))
                }
                _ => None,
            })
            .collect();
        if calls.is_empty() {
            return Ok(opened);
        }
        for (id, target) in calls {
            let body = lower(terms, library, target)?;
            let call = graph.kind(id).clone();
            // The one thing the pair needs of the two sides is that they
            // agree on what they take and leave, and a call carries its
            // arity for exactly the reason the term does.
            let pair = Pair::new(Graph::of_box(call), build(terms, body))
                .expect("a call and its body agree by arity, and both are graphs");
            let at = Match {
                nodes: vec![id],
                inputs: graph.sources(id).to_vec(),
                outputs: (0..graph.kind(id).arity().outputs)
                    .map(|port| graph.sinks(Source::Port { node: id, port }).to_vec())
                    .collect(),
                branches: Vec::new(),
            };
            pair.apply(graph, Direction::Forward, &at)
                .expect("a call is the window its own box fills");
            opened += 1;
        }
        if only.is_some() {
            return Ok(opened);
        }
    }
}

// ---- reading a graph back as a term ----------------------------------------------

/// The graph as a [`Term`] again.
///
/// A graph has no stack, so one has to be reimposed: the nodes are put in a
/// topological order and run one at a time, with a **routing** step between
/// them that gathers what the next box reads and lets go of what nothing
/// wants any more. A [`Source`] is a stable name for a value — one producer
/// port — which is exactly what a stack slot needs to be keyed by.
///
/// Two things keep the result readable, and they are where this differs
/// from `diagram`'s reify. The routing is **layered**: one `*`-product to
/// fix the multiplicities, then one per transposition round to fix the
/// order, instead of a bubble chain per value. And a box is placed **where
/// its operands already are** rather than on top, so the survivors pass
/// either side of it and a term written `X * id(1)` comes back as
/// `X * id(1)` rather than as the roll pair it is equal to.
///
/// Both are about legibility. This does not undo [`build`], and a branch is
/// where that shows plainest — the arms were flattened into the graph and
/// are scheduled like any other work, so what comes back runs both of them
/// and then chooses.
pub fn read_back(graph: &Graph, terms: &mut Context) -> TermIndex {
    let order = schedule(graph);
    // What is still wanted at or after each step, the boundary included.
    let mut wanted: Vec<HashSet<Source>> = vec![HashSet::new(); order.len() + 1];
    wanted[order.len()] = graph.outputs().iter().copied().collect();
    for k in (0..order.len()).rev() {
        let mut set = wanted[k + 1].clone();
        set.extend(graph.sources(order[k]).iter().copied());
        wanted[k] = set;
    }

    let mut steps: Vec<TermIndex> = Vec::new();
    let mut stack: Vec<Source> = (0..graph.arity().inputs).map(Source::Input).collect();
    for (k, &id) in order.iter().enumerate() {
        let sources: Vec<Source> = graph.sources(id).to_vec();
        let keep: Vec<Source> = stack
            .iter()
            .copied()
            .filter(|src| wanted[k + 1].contains(src))
            .collect();
        // Where the box goes. Not the top: a box sits just above whatever
        // it reads that lies deepest, so one that only touches the middle
        // of the stack stays in the middle instead of dragging its operands
        // up and the survivors back down afterwards. Putting everything on
        // top would mean the same thing and read far worse — `X * id(1)`
        // would come back as the roll pair it is equal to — and legibility
        // is the whole of the reason. A box that reads nothing has nothing
        // to sit above, so it lands on top.
        let anchor = sources
            .iter()
            .filter_map(|src| stack.iter().position(|held| held == src))
            .min()
            .unwrap_or(stack.len());
        let below = stack[..anchor]
            .iter()
            .filter(|src| wanted[k + 1].contains(src))
            .count();
        let above = keep.len() - below;

        let mut want: Vec<Source> = keep[..below].to_vec();
        want.extend(sources.iter().copied());
        want.extend(keep[below..].iter().copied());
        steps.extend(route(terms, &stack, &want));

        // The survivors pass either side of the box, so a step spans the
        // whole stack — which is what lets the fold below be a plain
        // `compose`, and a width mismatch a loud one.
        let step = box_term(terms, graph.kind(id));
        let step = terms.under(step, below);
        let step = if above > 0 {
            let untouched = terms.id(above);
            terms.par(step, untouched)
        } else {
            step
        };
        steps.push(step);

        let mut next: Vec<Source> = keep[..below].to_vec();
        next.extend(
            (0..graph.kind(id).arity().outputs).map(|port| Source::Port { node: id, port }),
        );
        next.extend(keep[below..].iter().copied());
        stack = next;
    }
    steps.extend(route(terms, &stack, graph.outputs()));

    let mut steps = steps.into_iter();
    // Nothing to do at all is the identity on the inputs, not on nothing.
    let Some(first) = steps.next() else {
        return terms.id(graph.arity().inputs);
    };
    let spine = steps.fold(first, |acc, next| {
        terms
            .compose(acc, next)
            .expect("every step spans the whole stack")
    });
    settle(terms, spine)
}

/// The two unit laws, spent on a term the loop above wrote wide on purpose.
///
/// Every step it emits spans the whole stack — that is what makes the fold a
/// plain `compose` and a width mismatch a loud one — and it pays for that by
/// naming each untouched wire separately: one factor per slot in a routing
/// layer, and a whole row for a box that is itself an `id`. The width is
/// load-bearing while the term is being built and pure noise once it is
/// built, so it comes off here rather than never:
///
/// - `id(a) * id(b)` = `id(a + b)`, over the flattened `*`-spine. Taking the
///   spine as a list rather than pairwise is the whole of it: the products
///   are left-nested, so `id(3) * swap * id(1) * id(1)` has no adjacent pair
///   to match on and only merges once the row is a run of factors.
/// - `id(n) ; t` = `t` = `t ; id(n)`. A row whose box is an `Id` touches
///   nothing, and a graph out of [`build`] is full of them.
///
/// Both laws hold on the nose — this deletes `id` boxes and changes nothing
/// else, so what comes back builds to the same graph the structural laws
/// take the original to. Nothing but the report reads a term from here, and
/// the report is the reason to do it.
fn settle(terms: &mut Context, term: TermIndex) -> TermIndex {
    match *terms.get(term) {
        Term::Par(..) => {
            let mut factors = Vec::new();
            flatten_par(terms, term, &mut factors);
            let mut settled: Vec<TermIndex> = Vec::with_capacity(factors.len());
            for factor in factors {
                let factor = settle(terms, factor);
                match (terms.get(factor), settled.last().map(|&m| terms.get(m))) {
                    // A wire block of no wires is not a factor.
                    (Term::Id(0), _) => {}
                    // A run of untouched wires is one block, however the
                    // products happen to be nested.
                    (Term::Id(a), Some(Term::Id(b))) => {
                        let width = a + b;
                        settled.pop();
                        let block = terms.id(width);
                        settled.push(block);
                    }
                    _ => settled.push(factor),
                }
            }
            let mut factors = settled.into_iter();
            let first = factors
                .next()
                .expect("a product of nothing is not a product");
            factors.fold(first, |acc, factor| terms.par(acc, factor))
        }
        Term::Compose(left, right) => {
            let (left, right) = (settle(terms, left), settle(terms, right));
            match (terms.get(left), terms.get(right)) {
                (Term::Id(_), _) => right,
                (_, Term::Id(_)) => left,
                _ => terms
                    .compose(left, right)
                    .expect("settling a step keeps its arity"),
            }
        }
        Term::Branch { if_true, if_false } => {
            let if_true = settle(terms, if_true);
            let if_false = settle(terms, if_false);
            terms.push(Term::Branch { if_true, if_false })
        }
        _ => term,
    }
}

/// A `*`-spine as the list of factors it is, left to right.
fn flatten_par(terms: &Context, term: TermIndex, out: &mut Vec<TermIndex>) {
    if let Term::Par(left, right) = *terms.get(term) {
        flatten_par(terms, left, out);
        flatten_par(terms, right, out);
    } else {
        out.push(term);
    }
}

/// The term one box stands for; a branch answers with its arms read back.
fn box_term(terms: &mut Context, kind: &NodeKind) -> TermIndex {
    match kind {
        NodeKind::Id(n) => terms.id(*n),
        NodeKind::Copy(n) => terms.copy(*n),
        NodeKind::Drop(n) => terms.drop(*n),
        NodeKind::Op(prim) => terms.op(prim.clone()),
        NodeKind::Call { target, arity } => terms.call(*target, *arity),
        // The two views of the stack are what a `copy` makes; the node is
        // only distinct so that rewriting leaves it alone. Its condition
        // computes nothing — it is read so that a rule can see it — so what
        // it comes back as is the condition let go of.
        NodeKind::Fork { arity, .. } => {
            let (gone, both) = (terms.drop(1), terms.copy(*arity));
            terms.par(gone, both)
        }
        // Both blocks are already on the stack by the time this runs — the
        // arms were scheduled like any other work — so the branch left to
        // write is only the choice between them: keep one block, let the
        // other go. The condition has to come up from the bottom first,
        // which is what the node's port order costs and the only place it
        // costs anything.
        NodeKind::Select { arity: n, .. } => {
            let up = hoist(terms, 2 * n + 1);
            let (keep, lose) = (terms.id(*n), terms.drop(*n));
            let if_true = terms.par(keep, lose);
            let (lose, keep) = (terms.drop(*n), terms.id(*n));
            let if_false = terms.par(lose, keep);
            let choose = terms
                .branch(if_true, if_false)
                .expect("each arm keeps one block of two");
            terms
                .compose(up, choose)
                .expect("the hoist leaves the width it was given")
        }
    }
}

/// `[a, x₁..x_k] -> [x₁..x_k, a]`: the deepest wire brought to the top, one
/// crossing at a time.
///
/// What a `select` costs at the boundary between a graph, where its
/// condition is port 0, and a term, where a `branch` reads its condition
/// off the top of the stack.
fn hoist(terms: &mut Context, width: usize) -> TermIndex {
    let mut chain: Option<TermIndex> = None;
    for below in 0..width.saturating_sub(1) {
        let swap = terms.op(Prim::Swap);
        let step = terms.under(swap, below);
        let above = width - below - 2;
        let step = if above > 0 {
            let untouched = terms.id(above);
            terms.par(step, untouched)
        } else {
            step
        };
        chain = Some(match chain {
            None => step,
            Some(acc) => terms
                .compose(acc, step)
                .expect("every crossing spans the whole stack"),
        });
    }
    chain.unwrap_or_else(|| terms.id(width))
}

/// The steps taking a stack of *distinct* sources to `want`, which may
/// repeat what it takes and leave out what it does not.
///
/// Two layers, and each is one `;`-step: the multiplicities first, then the
/// order. Both are `*`-products over the whole width, so a step reads as a
/// row of the diagram rather than as a chain of moves.
fn route(terms: &mut Context, have: &[Source], want: &[Source]) -> Vec<TermIndex> {
    debug_assert!(
        want.iter().all(|w| have.contains(w)),
        "routing cannot conjure a value the stack does not hold"
    );
    let copies: Vec<usize> = have
        .iter()
        .map(|h| want.iter().filter(|w| *w == h).count())
        .collect();

    let mut steps = Vec::new();
    // The copy layer: one factor per slot, `drop(1)` for a value nothing
    // wants, `id(1)` for one that is wanted once, a short chain otherwise.
    if copies.iter().any(|&k| k != 1) {
        let mut layer: Option<TermIndex> = None;
        for &k in &copies {
            let factor = duplicate(terms, k);
            layer = Some(match layer {
                None => factor,
                Some(acc) => terms.par(acc, factor),
            });
        }
        if let Some(layer) = layer {
            steps.push(layer);
        }
    }

    // Where each of the duplicated slots has to end up.
    let mut spread: Vec<Source> = Vec::new();
    for (j, &h) in have.iter().enumerate() {
        spread.extend(std::iter::repeat_n(h, copies[j]));
    }
    let mut taken = vec![false; want.len()];
    let mut places: Vec<usize> = Vec::with_capacity(spread.len());
    for &src in &spread {
        let slot = want
            .iter()
            .enumerate()
            .find(|&(i, &w)| !taken[i] && w == src)
            .map(|(i, _)| i)
            .expect("the copy layer produced exactly what is wanted");
        taken[slot] = true;
        places.push(slot);
    }

    // The permutation layer: odd–even transposition rounds, each a
    // `*`-product of `swap`s and the identities between them. `swap` is the
    // only reordering the term language has, so a sequence of rounds is
    // what a permutation costs — but each round is one flat row.
    let width = places.len();
    for round in 0..width {
        let crossings: Vec<usize> = (round % 2..width.saturating_sub(1))
            .step_by(2)
            .filter(|&i| places[i] > places[i + 1])
            .collect();
        if crossings.is_empty() {
            continue;
        }
        for &i in &crossings {
            places.swap(i, i + 1);
        }
        let mut layer: Option<TermIndex> = None;
        let mut slot = 0;
        while slot < width {
            let factor = if crossings.contains(&slot) {
                slot += 2;
                terms.op(Prim::Swap)
            } else {
                slot += 1;
                terms.id(1)
            };
            layer = Some(match layer {
                None => factor,
                Some(acc) => terms.par(acc, factor),
            });
        }
        if let Some(layer) = layer {
            steps.push(layer);
        }
    }
    debug_assert!(
        places.windows(2).all(|pair| pair[0] < pair[1]),
        "the rounds sort"
    );
    steps
}

/// `1 -> k`: the value dropped, passed through, or copied that many times.
fn duplicate(terms: &mut Context, k: usize) -> TermIndex {
    match k {
        0 => terms.drop(1),
        1 => terms.id(1),
        _ => {
            let mut chain = terms.copy(1);
            for held in 2..k {
                let more = terms.copy(1);
                let step = terms.under(more, held - 1);
                chain = terms
                    .compose(chain, step)
                    .expect("each link of the chain meets the last");
            }
            chain
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::meaning::{Meaning, boundary, eval_graph, eval_term};
    use super::*;
    use crate::graph::isomorphic;
    use crate::term::lower;
    use bytecode::{Library, SentenceIndex, assemble};

    /// The term a sentence written inline lowers to, built in `terms`.
    pub(crate) fn term_of(terms: &mut Context, body: &str) -> TermIndex {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        lower(terms, &library, idx).unwrap()
    }

    /// The graph a body builds, checked, with the arena its term lives in.
    pub(crate) fn built(body: &str) -> (Context, Graph) {
        let mut terms = Context::new();
        let term = term_of(&mut terms, body);
        let graph = build(&terms, term);
        graph.check().unwrap_or_else(|e| panic!("{}\n{}", e, graph));
        (terms, graph)
    }

    /// Every sentence the integration suite compiles, lowered into one
    /// arena — the same corpus `diagram`'s round trip runs on.
    pub(crate) fn corpus() -> (Library, Context, Vec<(SentenceIndex, TermIndex)>) {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(std::path::Path::parent)
            .expect("the crate sits in the workspace, beside the corpus")
            .join("hana");
        let text = std::fs::read_to_string(tests.join("main.hana")).unwrap();
        let mut map = bytecode::SourceMap::new();
        let file = map.add("main.hana", text);
        let library = bytecode::assemble_source(&mut map, file, Some(&tests))
            .unwrap_or_else(|e| panic!("{}", map.render(&e)));
        let mut arena = Context::new();
        let lowered = crate::term::lower_all(&mut arena, &library).unwrap();
        let terms = lowered.iter_enumerated().map(|(i, &t)| (i, t)).collect();
        (library, arena, terms)
    }

    // ---- the literal translation ----

    #[test]
    fn a_term_is_one_box_per_leaf() {
        // `push 1 ; id(1) * push 2 ; add`: four leaves, four boxes. The `;`
        // and the `*` have no spelling — sequencing is one box's output
        // port being another's input, side by side is two boxes sharing no
        // ports — but the `id(1)` the padding introduced is right there as
        // a box, which is the difference from `diagram`.
        let (_terms, graph) = built("push 1 push 2 add");
        assert_eq!(graph.live_count(), 4);
        assert!(
            graph
                .live()
                .any(|(_, kind)| matches!(kind, NodeKind::Id(1))),
            "the padding is data here:\n{}",
            graph
        );
        assert!(graph.is_monogamous());
    }

    #[test]
    fn a_branch_is_its_arms_and_a_select() {
        // The arms are not inside anything: the four boxes of the `then`
        // arm and the one of the `else` arm sit in this graph beside the
        // `select` that picks between their answers. Both arms take
        // nothing, so there is no `copy` to fork the stack either.
        let (_terms, graph) = built("branch { push 1 push 2 add } { push 2 }");
        assert_eq!(graph.live_count(), 6, "{}", graph);

        let (id, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select { arity: 1, .. }))
            .expect("the branch ends in a select");
        // Its three inputs: the condition, which is the sentence's own
        // input and sits at port 0 the way it does on a fork, and then the
        // `then` answer and the `else` answer.
        let inputs = graph.sources(id).to_vec();
        assert_eq!(inputs.len(), 3);
        assert_eq!(inputs[0], Source::Input(0), "the condition is port 0");
        assert!(
            matches!(
                (inputs[1], inputs[2]),
                (Source::Port { .. }, Source::Port { .. })
            ),
            "each block is an arm's answer"
        );
    }

    // ---- routing, the read-back's own layer ----

    #[test]
    fn a_route_is_a_copy_layer_and_then_swap_rounds() {
        let terms = &mut Context::new();
        let have = [Source::Input(0), Source::Input(1)];

        // Nothing to do at all emits nothing.
        assert!(route(terms, &have, &have).is_empty());

        // One flat product handles every multiplicity at once: drop the
        // deep slot, keep two copies of the top one.
        let steps = route(terms, &have, &[Source::Input(1), Source::Input(1)]);
        assert_eq!(steps.len(), 1);
        assert_eq!(format!("{}", terms.display(steps[0])), "drop(1) * copy(1)");

        // A pure exchange is one round of one swap.
        let steps = route(terms, &have, &[Source::Input(1), Source::Input(0)]);
        assert_eq!(steps.len(), 1);
        assert_eq!(format!("{}", terms.display(steps[0])), "swap");
    }

    // ---- the corpus ----

    #[test]
    fn the_whole_corpus_builds() {
        let (library, arena, terms) = corpus();
        assert!(terms.len() > 100, "the corpus should be a real one");
        for (idx, term) in terms {
            let graph = build(&arena, term);
            graph
                .check()
                .unwrap_or_else(|e| panic!("sentence {}: {}", library.names[idx], e));
            assert!(
                graph.is_monogamous(),
                "sentence {} built with a shared port",
                library.names[idx]
            );
            assert_eq!(
                graph.arity(),
                arena.arity(term),
                "sentence {} changed arity in the translation",
                library.names[idx]
            );
        }
    }

    /// The tightest check of [`build`] there is, and the shortest: the graph
    /// means what the term means, with nothing translated back.
    #[test]
    fn a_graph_means_what_its_term_means() {
        let (library, arena, terms) = corpus();
        for (idx, term) in terms {
            let graph = build(&arena, term);
            let mut m = Meaning::default();
            let inputs = boundary(&mut m, arena.arity(term).inputs);
            let (as_term, as_graph) = (
                eval_term(&mut m, &arena, term, inputs.clone()),
                eval_graph(&mut m, &graph, &inputs),
            );
            assert_eq!(
                as_term, as_graph,
                "sentence {} means something else as a graph",
                library.names[idx]
            );
        }
    }

    // ---- opening a call ----

    /// A call opened in place is the body's boxes on the call's wires —
    /// the same graph building the opened term would have made.
    #[test]
    fn a_call_opens_in_place() {
        let code = r#"
            #[arity(1,1)] sentence inner { not not }
            #[arity(1,1)] sentence outer { jump crate::inner }
            sentence probe { jump crate::outer }
        "#;
        let library = assemble(code).unwrap();
        let named = |name: &str| {
            library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(idx, _)| idx)
                .unwrap()
        };
        let mut terms = Context::new();
        let term = lower(&mut terms, &library, named("probe")).unwrap();
        let mut graph = build(&terms, term);

        // A labelled inline opens that sentence and leaves what it calls
        // shut.
        let mut labelled = graph.clone();
        let opened = inline(&mut labelled, &mut terms, &library, Some(named("outer"))).unwrap();
        assert_eq!(opened, 1);
        labelled.check().unwrap();
        assert!(matches!(
            labelled.live().next().map(|(_, k)| k),
            Some(NodeKind::Call { target, .. }) if *target == named("inner")
        ));

        // Unlabelled opens all the way down, and lands on the graph the
        // opened term builds.
        let opened = inline(&mut graph, &mut terms, &library, None).unwrap();
        assert_eq!(opened, 2);
        graph.check().unwrap();
        let (_t, flat) = built("not not");
        assert!(isomorphic(&graph, &flat), "\n{}\n{}", graph, flat);
        assert_eq!(inline(&mut graph, &mut terms, &library, None).unwrap(), 0);
    }
}
