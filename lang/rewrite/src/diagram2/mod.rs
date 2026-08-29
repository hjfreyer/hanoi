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
//! here is everything that knows a graph came from a *term*: [`build`]
//! writes one, [`inline`] opens a call in place, and [`rules`] and
//! [`tactic`] are the table and the driving of it. The translation runs
//! one way only — a graph is read by [`render`], not turned back into a
//! term.
//!
//! A branch is one box, and its arms are not inside it. A `copy(n)` hands
//! both arms the stack, both arms are emitted as ordinary boxes, and the
//! `select(n)` keeps one of the two answers. That `copy` is exactly the
//! `(pick (n-1))^n` of the single-arm hoist in
//! [docs/totality.md](../../../../docs/totality.md), and the hoist is why the
//! translation is allowed: every prim is total and has no effect but the
//! stack, so work on the path not taken costs an answer nobody reads
//! rather than a failure.
//!
//! So an arm is not opaque: a rule reaches into one from outside, and a
//! value reaches out. `copy-elim` deletes that copy like any other, after
//! which both arms read the one port — which is what makes the branch
//! layer short. A block that *is* the value the condition tested is that
//! value, and a rule can say so by naming one source twice.
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
//!   copy(1)` settle in the same place.
//!
//! What the rules leave is a DAG of `Op`s, `Call`s and `Select`s whose
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
//!   Every one of those rows is stated at the `select`, which is the whole
//!   of a branch: `select-literal` reads a literal condition and answers
//!   with the blocks it chooses, leaving the untaken arm to `dead-node`.
//!   `rules` says what each row can say and why.
//!
//! Nothing translates the other way. A graph is *read* as a graph — see
//! [`render`], which lays one out as a listing whose lines name the boxes
//! a next step would name back — and the term a graph came from is not
//! reconstructed. It could not be the term it was built from anyway: a
//! branch is flattened into the graph and its arms scheduled like any
//! other work, so anything reimposing a stack would answer with both arms
//! run flat and a choice at the end.

use bytecode::{Library, SentenceIndex};

use crate::graph::{Direction, Graph, Match, NodeId, NodeKind, Pair, Source};
use crate::term::{Context, Term, TermIndex, lower};

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
        // arms-in-a-box it used to be: the condition is set aside, a `copy`
        // hands each arm the stack, both arms are emitted into this same
        // graph, and the `select` keeps one of the two answers. What was a
        // boundary is a box with the arms in front of it, so every rule
        // reaches through it.
        Term::Branch { if_true, if_false } => {
            let mut inputs = inputs;
            let cond = inputs.pop().expect("a branch reads its condition");
            // Block-wise, exactly the `(pick (n-1))^n` the hoist rule spells
            // out. Arms that take nothing have nothing to be handed, and
            // then there is no copy at all.
            let (if_true_in, if_false_in) = if inputs.is_empty() {
                (Vec::new(), Vec::new())
            } else {
                let arity = inputs.len();
                let mut blocks = graph.add(NodeKind::Copy(arity), inputs);
                let above = blocks.split_off(arity);
                (blocks, above)
            };
            let mut ports = vec![cond];
            ports.extend(emit(graph, terms, *if_true, if_true_in));
            ports.extend(emit(graph, terms, *if_false, if_false_in));
            let arity = terms.arity(*if_true).outputs;
            graph.add(NodeKind::Select { arity }, ports)
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
        // nothing, so there is no `copy` handing out the stack either.
        let (_terms, graph) = built("branch { push 1 push 2 add } { push 2 }");
        assert_eq!(graph.live_count(), 6, "{}", graph);

        let (id, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select { arity: 1, .. }))
            .expect("the branch ends in a select");
        // Its three inputs: the condition, which is the sentence's own
        // input and sits at port 0, and then the `then` answer and the
        // `else` answer.
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
