//! Machinery for proving Hanoi programs equivalent.
//!
//! [`term`] is the model claims are stated over and [`parse`] reads one back
//! out of the language it prints in; [`lang`] is that model as an e-graph
//! language and [`rules`] the equations over it; [`goal`] is a claim and what
//! became of it; [`hant`] is the strategy language a human directs a proof
//! with; [`strategy`] interprets one; [`corpus`] loads a source tree's
//! identities and proofs together. `bin/prove` drives the lot.

pub mod corpus;
pub mod goal;
pub mod hant;
pub mod lang;
pub mod parse;
pub mod rules;
pub mod strategy;
pub mod term;

pub use term::{Arity, Error, Prim, Term, lower, lower_all};
