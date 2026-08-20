//! Machinery for proving Hanoi programs equivalent.
//!
//! [`term`] is the model claims are stated over and [`parse`] reads one back
//! out of the language it prints in; [`diagram`] is the engine — programs as
//! wiring in an interned arena, canonicalized into ordered, shared case
//! trees, so equality of the fragment it covers is *decided* rather than
//! searched for; [`goal`] is a claim and what became of it; [`hant`] is the
//! strategy language a human directs a proof with; [`strategy`] interprets
//! one; [`corpus`] loads a source tree's identities and proofs together.
//! `bin/prove` drives the lot.

pub mod corpus;
pub mod diagram;
pub mod goal;
pub mod hant;
pub mod parse;
pub mod strategy;
pub mod term;

pub use term::{Arity, Error, Prim, Term, lower, lower_all};
