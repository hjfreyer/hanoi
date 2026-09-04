//! Machinery for proving Hanoi programs equivalent.
//!
//! The crate is cut in two, and the cut is what a bug would cost.
//!
//! [`kernel`] is everything a proof's *truth* rests on: [`term`](kernel::term)
//! is the model claims are stated over — terms live in a
//! [`Context`] arena and are passed around as [`TermIndex`]; [`graph`](kernel::graph) is what
//! a claim is *carried* in — boxes, the links between them, well-formedness,
//! whether two of them are the same diagram, and the one rewriting operation
//! there is: a [`Pair`](kernel::graph::Pair) of graphs put down where a
//! [`Match`](kernel::graph::Match) says, checked before anything moves;
//! [`kernel::build`] is the term translated *literally* into a graph,
//! structural boxes and all;
//! [`rules`](kernel::rules) is the table whose every law *is* such a pair;
//! and [`goal`](kernel::goal) is a claim — two graphs — and
//! [`certify`](kernel::goal::certify), which replays a flat run of steps on
//! the one and asks whether it landed on the other. A bug in any of that
//! could let a false identity through, which is why it is one module and
//! why nothing in it searches.
//!
//! Everything outside the kernel can only fail loudly. [`tactic`] and
//! [`query`] find steps, with what to spend and where left to whoever drives
//! them; [`hant`] is the strategy language a human directs a proof with;
//! [`strategy`] interprets one, writing a [`proof`] — a *draft*, the tree
//! of goals it carved and the steps each spent — that [`proof::flatten`]
//! turns into the one run the kernel is handed; [`render`] lays a stuck
//! graph out for reading; [`corpus`] loads a source tree's identities
//! and proofs together. A bug in any of these seeds a step the kernel
//! refuses or a run that does not land, never a wrong graph. `bin/prove`
//! drives the lot.
//!
//! There was a second engine here — `diagram`, an interned value-DAG under
//! ordered case trees, a decision procedure for its fragment. It is gone,
//! and what it decided the table now spends as named laws: its folds run
//! the same machine ([`kernel::rules::Law::Fold`] and kin), its case
//! trees became the branch layer plus the `cases` proof step, and its one
//! un-inspectable verdict became a derivation's worth of checked rewrites
//! and a final isomorphism.

pub mod corpus;
pub mod hant;
pub mod kernel;
pub mod proof;
pub mod query;
pub mod render;
pub mod strategy;
pub mod tactic;

pub use kernel::term::{Arity, Context, Error, Prim, Term, TermIndex, lower, lower_all};
