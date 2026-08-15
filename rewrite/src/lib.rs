//! Machinery for proving Hanoi programs equivalent.
//!
//! The first thing such a proof needs is something to state itself over, and a
//! list of instructions is not it: composition is implicit, untyped, and joined
//! by `dip` as a second way of combining programs that no law about the first
//! one reaches. [`term`] is the model that replaces all three with two
//! arity-exact operators, and it is all that lives here so far — the rules, the
//! matching and the search come next, and are meant to be stated over a model
//! that settled first.

pub mod goal;
pub mod hint;
pub mod lang;
pub mod rules;
pub mod strategy;
pub mod term;

pub use term::{Arity, Error, Prim, Term, lower, lower_all};
