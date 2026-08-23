//! Machinery for proving Hanoi programs equivalent.
//!
//! [`term`] is the model claims are stated over — terms live in a
//! [`Context`](term::Context) arena and are passed around as
//! [`TermIndex`](term::TermIndex) — and [`parse`] reads one back out of the
//! language it prints in; [`diagram2`] is the engine — a term translated
//! *literally* into a graph, structural boxes and all, rewritten until the
//! connections are direct against a table ([`diagram2::rules`]) whose
//! every law is a pair of graphs and whose every rewrite is one of them
//! swapped for the other, with what to spend and where left to whoever
//! drives it ([`diagram2::tactic`]); [`goal`] is a claim — two graphs —
//! and what became of it; [`hant`] is the strategy language a human
//! directs a proof with; [`strategy`] interprets one; [`corpus`] loads a
//! source tree's identities and proofs together. `bin/prove` drives the
//! lot.
//!
//! There was a second engine here — `diagram`, an interned value-DAG under
//! ordered case trees, a decision procedure for its fragment. It is gone,
//! and what it decided the table now spends as named laws: its folds run
//! the same machine ([`diagram2::rules::Law::Fold`] and kin), its case
//! trees became the branch layer plus the `cases` proof step, and its one
//! un-inspectable verdict became a derivation's worth of checked rewrites
//! and a final isomorphism.

pub mod corpus;
pub mod diagram2;
pub mod goal;
pub mod hant;
pub mod parse;
pub mod strategy;
pub mod term;

pub use term::{Arity, Context, Error, Prim, Term, TermIndex, lower, lower_all};
