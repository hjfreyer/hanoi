//! The trusted kernel: what a proof's truth rests on, and nothing else.
//!
//! The line drawn around this module is what a bug would cost. A bug in
//! here could let a false identity through; a bug anywhere else in the
//! crate seeds a step [`rules::apply`] refuses or a proof
//! [`Proof::check`](goal::Proof::check) fails, never a wrong graph. So what
//! lives here is exactly the set of things that have to be right, and
//! nothing that only has to be found:
//!
//! - [`term`] — the model a claim is stated over, and the lowering from
//!   bytecode that says what a sentence *means*.
//! - [`graph`] — what a claim is carried in: boxes, the links between
//!   them, well-formedness, whether two graphs are the same diagram, and
//!   the one rewriting operation there is, a [`Pair`] put down where a
//!   [`Match`] says, checked port by port before anything moves.
//! - [`build`] and [`inline`], below — a term translated *literally* into
//!   a graph, and a call opened in place by definition.
//! - [`rules`] — the table, every law a pair of graphs, and
//!   [`rules::apply`], the one way a graph is ever rewritten.
//! - [`goal`] — a claim, and the [`Proof`](goal::Proof) that re-performs
//!   every step of its discharge against the claim as stated.
//!
//! Searching is not here. Which law, where, in what order — the tactics of
//! [`crate::tactic`], the queries of [`crate::query`], the strategies of
//! [`crate::hant`] run by [`crate::strategy`] — is untrusted convenience,
//! and every step it takes comes back through [`rules::apply`]. The one
//! thing the kernel takes on someone else's word is a citation:
//! [`Proof::Cited`](goal::Proof::Cited) holds the cited claim's *use* to
//! account and leaves its *truth* to the corpus, which proves every
//! identity and refuses a cycle.
//!
//! ## A term, literally
//!
//! A term becomes a graph **one operation at a time**, and only the
//! operations: `id`, `swap`, `copy` and `drop` are how a stack program
//! spells things a graph says by naming — a wire is nothing, a crossing
//! is two names in the other order, a fan-out is one source named twice,
//! and a discard is a source named nowhere. [`build`] is where that
//! translation happens and the only place that ever knew about the
//! stack. The translation runs one way only — a graph is read by
//! [`crate::render`], not turned back into a term.
//!
//! ## What the representation already says
//!
//! A box is its kind and the sources its input ports read, and asking for
//! one twice answers with the one that is already there. So a family of
//! laws is not in the table and could not be: there is no graph for
//! either side of them to be.
//!
//! - **`id-elim`, `swap-elim`** — a wire and a crossing are not boxes.
//!   σ involutive, σ-natural and Yang–Baxter all fall out of nothing
//!   having recorded a crossing in the first place.
//! - **`copy-elim`** — a value read twice is two references. The
//!   cartesian structure is not something a rewrite introduces; it is
//!   what a source having many readers *is*.
//! - **`dead-node`** — a box the boundary does not reach is not part of
//!   the program. Discarding is licensed by totality and purity, and
//!   there is nothing to fire.
//! - **`dedup`** — δ-naturality. `push 9 ; push 9` and `push 9 ; copy(1)`
//!   do not *settle* in the same place; they are written in the same
//!   place, because a value is named by what it is.
//!
//! A branch is one box and its arms are not inside it. Both arms are
//! handed the **same sources** — not a copy of them — so an operation
//! both arms do is one box, and a block that *is* the value the condition
//! tested is that value outright. That both arms are computed is the
//! single-arm hoist of
//! [docs/totality.md](../../../../docs/totality.md), and the hoist is why
//! the translation is allowed: every prim is total and has no effect but
//! the stack, so work on the path not taken costs an answer nobody reads
//! rather than a failure. An arm is not opaque either: a rule reaches
//! into one from outside, and a value reaches out.
//!
//! ## The rules
//!
//! Each one is a **pair of graphs** [`rules::sides`] builds from a payload
//! — the whole of what a rule *is* — and a rewrite is pointing at part of
//! a graph that is the first and putting the second in its place. What is
//! left in the table is the two things a representation cannot decide:
//! what a branch means, and what an operation computes.
//!
//! So a graph out of [`build`] is the translation and stays that way
//! until something applies a rule to it. [`rules`] is where that happens:
//! [`rules::sides`] turns a payload into the [`Pair`] of graphs it
//! states, [`find`](graph::find) and [`rules::propose`] say where a
//! law could fire, [`rules::apply`] fires one and hands back its inverse,
//! and [`rules::replay`] runs a list of them. Only the first of those is
//! the table's own work — the rest is [`Pair::apply`] wearing a law's
//! name.
//!
//! **A box reads; nothing records being read.** An input port names the
//! one source it reads ([`Source`]) and that is the whole of the
//! structure, so a rewrite cannot half-update a link: a box is immutable,
//! and replacing a value means building the boxes that read it afresh.
//! Who reads a port is a *reading* ([`Graph::sinks`]),
//! computed over the boxes the boundary reaches — which is why a box a
//! rewrite left behind counts for nothing without anything having to
//! collect it.
//!
//! **Two boundaries are drawn on purpose**, and they moved when the old
//! `diagram` engine retired and this kernel became the prover's:
//!
//! - **Equality is one question, asked at the end.** [`isomorphic`](graph::isomorphic) says
//!   whether two graphs are the same diagram, and [`crate::strategy`]'s
//!   closer asks it once, after driving both sides through the table.
//!   Nothing here saturates toward a canonical form by decree: `push 1 ;
//!   push 2 ; add` and `push 2 ; push 1 ; add` are related exactly when a
//!   strategy spends the laws that relate them. What holds the laws to
//!   meaning is the corpus itself: [`crate::strategy`]'s tests pin which
//!   of `hana`'s identities the bare table decides, so a law that stopped
//!   saying something true shows up as a claim that stopped closing.
//! - **The value folds live in [`rules::folding`], and the branch layer
//!   in [`rules::branching`].** A literal window runs on the machine
//!   itself (`rules::Rule::Fold` and its kin), but only when a strategy
//!   fires it. Every row of the branch layer is stated at the `select`,
//!   which is the whole of a branch: `select-literal` reads a literal
//!   condition and answers with the blocks it chooses, and the untaken
//!   arm stops being reached. `rules` says what each row can say and
//!   why.
//!
//! Nothing translates the other way. A graph is *read* as a graph — see
//! [`crate::render`], which lays one out as a listing whose lines name the boxes
//! a next step would name back — and the term a graph came from is not
//! reconstructed. It could not be the term it was built from anyway: a
//! branch is flattened into the graph and its arms scheduled like any
//! other work, so anything reimposing a stack would answer with both arms
//! run flat and a choice at the end.

use bytecode::{Library, SentenceIndex};

use crate::kernel::graph::{Direction, Graph, Match, NodeKind, Pair, Source};
use crate::kernel::term::{Context, Prim, Term, TermIndex, lower};

pub mod goal;
pub mod graph;
pub mod rules;
pub mod term;

// ---- a term, literally ---------------------------------------------------------

/// The graph of a term: one node per leaf, nothing simplified.
///
/// Every law of the structural layer still has a spelling here, which is
/// the whole premise of the kernel — the table in [`rules`] is what spends
/// them.
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
        // The four the stack needed and a graph of values does not. `id`
        // is the sources themselves; `copy` is naming them twice, since a
        // value read twice is two references to one box; `drop` is naming
        // them nowhere, which is what makes a discarded computation a box
        // the boundary does not reach; and `swap` is the other order.
        // None of them is a box, so none of them is ever a rewrite.
        Term::Id(_) => inputs,
        Term::Copy(n) => {
            debug_assert_eq!(inputs.len(), *n, "the caller cuts by arity");
            let mut out = inputs.clone();
            out.extend(inputs);
            out
        }
        Term::Drop(_) => Vec::new(),
        Term::Op(Prim::Swap) => {
            let mut out = inputs;
            out.reverse();
            out
        }
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
        // A branch is a `select` **per answer** and the arms in front of
        // them. Both arms are handed the same stack — not a copy of it, the
        // same sources — and whatever each computes from it are the blocks
        // the selects keep one of, paired off answer by answer. Work on the
        // path not taken is a value nobody reads.
        //
        // The `n` selects read one condition and are peers: none is
        // upstream of another, and no box says they came from one `branch`.
        // Nothing needs to. A branch means a choice per answer, so `n`
        // choices is what it *is*, and the grouping a wider box would have
        // carried is the listing's to read back off the condition.
        Term::Branch { if_true, if_false } => {
            let mut inputs = inputs;
            let cond = inputs.pop().expect("a branch reads its condition");
            let then = emit(graph, terms, *if_true, inputs.clone());
            let els = emit(graph, terms, *if_false, inputs);
            then.into_iter()
                .zip(els)
                .map(|(t, e)| graph.add(NodeKind::Select, vec![cond, t, e])[0])
                .collect()
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
) -> Result<usize, crate::kernel::term::Error> {
    let mut opened = 0;
    // One at a time, asked again each time round. A rewrite rebuilds
    // everything downstream of what it replaced, so a call that sat under
    // an opened one is a *new* box afterwards and the id that named it is
    // stale — which is why the calls are looked for rather than listed.
    //
    // Draining is one pass either way: a sentence may not reach itself, so
    // a call to `target` never appears inside `target`'s own body, and
    // `only` opening until none is left opens exactly the ones that were
    // there.
    loop {
        let call = graph.live().find_map(|(id, kind)| match kind {
            NodeKind::Call { target, .. } if only.is_none_or(|t| t == *target) => {
                Some((id, *target))
            }
            _ => None,
        });
        let Some((id, target)) = call else {
            return Ok(opened);
        };
        let body = lower(terms, library, target)?;
        let call = graph.kind(id).clone();
        // The one thing the pair needs of the two sides is that they agree
        // on what they take and leave, and a call carries its arity for
        // exactly the reason the term does.
        let pair = Pair::new(Graph::of_box(call), build(terms, body))
            .expect("a call and its body agree by arity, and both are graphs");
        let at = Match {
            nodes: vec![id],
            inputs: graph.sources(id).to_vec(),
            sel: None,
        };
        pair.apply(graph, Direction::Forward, &at)
            .expect("a call is the window its own box fills");
        opened += 1;
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::kernel::graph::isomorphic;
    use crate::kernel::term::lower;
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
    /// arena.
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
        let lowered = crate::kernel::term::lower_all(&mut arena, &library).unwrap();
        let terms = lowered.iter_enumerated().map(|(i, &t)| (i, t)).collect();
        (library, arena, terms)
    }

    // ---- the literal translation ----

    #[test]
    fn a_term_is_one_box_per_operation() {
        // `push 1 ; id(1) * push 2 ; add`: four leaves, three boxes. The
        // `;` and the `*` have no spelling — sequencing is one box's
        // output port being another's input, side by side is two boxes
        // sharing no ports — and neither has the `id(1)` the padding
        // introduced, which is a wire and so is not a box at all.
        let (_terms, graph) = built("push 1 push 2 add");
        assert_eq!(graph.live_count(), 3, "\n{}", graph);

        // And a value said twice is said once: the two literals are one
        // box, read twice, before anything has had a chance to rewrite.
        let (_terms, shared) = built("push 1 push 1 add");
        assert_eq!(shared.live_count(), 2, "\n{}", shared);
        let (lit, _) = shared
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(_))))
            .expect("the literal");
        assert_eq!(
            shared.sinks(Source::Port { node: lit, port: 0 }).len(),
            2,
            "one literal, read twice:\n{}",
            shared
        );
    }

    #[test]
    fn a_branch_is_its_arms_and_a_select() {
        // The arms are not inside anything: the boxes of the `then` arm
        // sit in this graph beside the `select` that picks between their
        // answers. `push 2` is one box, written once and read by both the
        // `add` and the `else` block.
        let (_terms, graph) = built("branch { push 1 push 2 add } { push 2 }");
        assert_eq!(graph.live_count(), 4, "{}", graph);

        let (id, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select))
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
            assert_eq!(
                graph.arity(),
                arena.arity(term),
                "sentence {} changed arity in the translation",
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
