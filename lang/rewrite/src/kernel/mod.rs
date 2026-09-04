//! The trusted kernel: what a proof's truth rests on, and nothing else.
//!
//! The line drawn around this module is what a bug would cost. A bug in
//! here could let a false identity through; a bug anywhere else in the
//! crate seeds a step [`rules::apply`] refuses or a run
//! [`certify`](goal::certify) will not replay, never a wrong graph. So what
//! lives here is exactly the set of things that have to be right, and
//! nothing that only has to be found:
//!
//! - [`prim`] — what a box computes and how many values it reads: the
//!   vocabulary the rest is written in.
//! - [`graph`] — what a claim is carried in: boxes, the links between
//!   them, well-formedness, whether two graphs are the same diagram, and
//!   the one rewriting operation there is, a [`Pair`](graph::Pair) put down
//!   where a [`Match`](graph::Match) says, checked port by port before
//!   anything moves.
//! - [`lower`] — the walk from a sentence's instructions to the graph it
//!   computes, which is what says a sentence *means*.
//! - [`rules`] — the table, every law a pair of graphs, and
//!   [`rules::apply`], the one way a graph is ever rewritten. One row,
//!   [`rules::Rule::Open`], is a fact of the library rather than of the
//!   table: a call is its body.
//! - [`goal`] — a claim, and [`certify`](goal::certify), the one judgement
//!   the kernel makes of a proof: a flat run of steps, replayed on the
//!   claim's left side, lands on its right.
//!
//! Searching is not here. Which law, where, in what order — the tactics of
//! [`crate::tactic`], the queries of [`crate::query`], the strategies of
//! [`crate::hant`] run by [`crate::strategy`] — is untrusted convenience,
//! and every step it takes comes back through [`rules::apply`]. Nor is
//! the shape of an argument: the tree of goals a strategy carves, what met
//! in the middle, what was cited, is [`crate::proof`]'s *draft*, and what
//! the kernel is handed is the run [`crate::proof::flatten`] reads off it.
//! The kernel takes nothing on anyone's word: a cited claim arrives as its
//! own steps, and a body a call is opened to is rebuilt from the library
//! before it is spent.
//!
//! ## A sentence, literally
//!
//! A sentence becomes a graph **one operation at a time**, and only the
//! operations: `copy`, `drop`, `swap` and the passing-through a sentence
//! leaves implicit are how a stack program spells things a graph says by
//! naming — a fan-out is one source named twice, a discard is a source
//! named nowhere, a crossing is two names in the other order, and a value
//! nothing touched is a source still sitting where it was. [`lower`] is
//! where that walk happens and the only place that ever knew about the
//! stack. It runs one way only — a graph is read by [`crate::render`],
//! not turned back into instructions.
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
//! A branch is one box per answer and its arms are not inside them. Both
//! arms are handed the **same sources** — not a copy of them — so an
//! operation both arms do is one box, and a block that *is* the value the
//! condition tested is that value outright. That both arms are computed is
//! the single-arm hoist of
//! [docs/totality.md](../../../../docs/totality.md), and the hoist is why
//! the walk is allowed: every prim is total and has no effect but
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
//! So a graph out of [`lower`] is what the sentence says and stays that
//! way until something applies a rule to it. [`rules`] is where that
//! happens:
//! [`rules::sides`] turns a payload into the [`Pair`](graph::Pair) of graphs it
//! states, [`find`](graph::find) and [`rules::propose`] say where a
//! law could fire, [`rules::apply`] fires one and hands back its inverse,
//! and [`rules::replay`] runs a list of them. Only the first of those is
//! the table's own work — the rest is [`Pair::apply`](graph::Pair::apply) wearing a law's
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
//! Nothing walks the other way. A graph is *read* as a graph — see
//! [`crate::render`], which lays one out as a listing whose lines name the
//! boxes a next step would name back — and the sentence a graph came from
//! is not reconstructed. It could not be that sentence anyway: the arms of
//! a branch are in the graph beside the `select`s and scheduled like any
//! other work, so anything reimposing a stack would answer with both arms
//! run flat and a choice at the end.

pub mod goal;
pub mod graph;
pub mod lower;
pub mod prim;
pub mod rules;

pub use lower::{Error, call_arity, lower};

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::kernel::graph::Graph;
    use bytecode::{Library, SentenceIndex, assemble};

    /// The graph a body written inline lowers to, checked.
    pub(crate) fn built(body: &str) -> Graph {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        let graph = lower(&library, idx).unwrap();
        graph.check().unwrap_or_else(|e| panic!("{}\n{}", e, graph));
        graph
    }

    /// Every sentence the integration suite compiles, as the graph it
    /// computes.
    pub(crate) fn corpus() -> (Library, Vec<(SentenceIndex, Graph)>) {
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
        let graphs = library
            .sentences
            .keys()
            .map(|idx| (idx, lower(&library, idx).unwrap()))
            .collect();
        (library, graphs)
    }
}
