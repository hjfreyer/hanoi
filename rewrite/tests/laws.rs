//! The laws, each doing what it says.
//!
//! `rules.egg` states the equational theory; this is the check that the
//! statements are the ones intended — one small goal per law or cluster of
//! laws, closed by saturation alone. `corpus.rs` is the other half of the net:
//! it holds the whole pipeline to the identities the corpus states.

use bytecode::Value;
use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::{Config, Prover};
use rewrite::{Arity, Prim, Term};

/// Saturates the two terms and answers whether they met.
fn provable(lhs: &Term, rhs: &Term) -> bool {
    let library = bytecode::Library::new();
    let prover = Prover::new(&library, Config::default());
    matches!(
        prover.saturate(&Goal::aligned(lhs.clone(), rhs.clone())),
        Outcome::Closed(_)
    )
}

fn op(p: Prim) -> Term {
    Term::op(p)
}

#[test]
fn a_test_of_a_test_is_decided() {
    // `is_bool ; is_bool` = `drop ; push true`.
    let lhs = Term::pad_compose(op(Prim::IsBool), op(Prim::IsBool));
    let rhs = Term::pad_compose(Term::drop(1), op(Prim::Push(Value::Bool(true))));
    assert!(provable(&lhs, &rhs));
}

#[test]
fn two_spellings_of_one_test_meet_in_the_middle() {
    // `is_bool ; is_bool` = `is_int ; is_bool`: neither reduces to the
    // other, and the e-graph does not care.
    let lhs = Term::pad_compose(op(Prim::IsBool), op(Prim::IsBool));
    let rhs = Term::pad_compose(op(Prim::IsInt), op(Prim::IsBool));
    assert!(provable(&lhs, &rhs));
}

#[test]
fn a_literal_window_folds_to_what_the_machine_answers() {
    // `push 1 ; push 2 ; add` = `push 3`, junk semantics included.
    let lhs = Term::pad_compose(
        Term::pad_compose(op(Prim::Push(Value::Int(1))), op(Prim::Push(Value::Int(2)))),
        op(Prim::Add),
    );
    assert!(provable(&lhs, &op(Prim::Push(Value::Int(3)))));

    // And off the domain: `push true ; push 2 ; add` = `push 0`.
    let junk = Term::pad_compose(
        Term::pad_compose(
            op(Prim::Push(Value::Bool(true))),
            op(Prim::Push(Value::Int(2))),
        ),
        op(Prim::Add),
    );
    assert!(provable(&junk, &op(Prim::Push(Value::Int(0)))));
}

#[test]
fn copying_a_constant_is_pushing_it_twice() {
    // `push 9 ; copy` = `push 9 ; push 9` — the constant case of copy
    // naturality, reached through the staircases.
    let nine = || op(Prim::Push(Value::Int(9)));
    let lhs = Term::pad_compose(nine(), Term::copy(1));
    let rhs = Term::pad_compose(nine(), nine());
    assert!(provable(&lhs, &rhs));
}

#[test]
fn discarded_work_is_no_work() {
    // `equal ; drop` = `drop ; drop`.
    let lhs = Term::pad_compose(op(Prim::Equal), Term::drop(1));
    let rhs = Term::pad_compose(Term::drop(1), Term::drop(1));
    assert!(provable(&lhs, &rhs));
}

#[test]
fn a_frame_comes_off_as_rolls() {
    // `not * id(1)` = `swap ; id(1) * not ; swap`.
    let lhs = Term::par(op(Prim::Not), Term::id(1));
    let rhs = Term::pad_compose(
        Term::pad_compose(op(Prim::Swap), Term::par(Term::id(1), op(Prim::Not))),
        op(Prim::Swap),
    );
    assert!(provable(&lhs, &rhs));
}

#[test]
fn a_frame_beside_a_branch_opens_into_the_arms() {
    // `id(1) * branch { A } { B }` = `branch { id(1)*A } { id(1)*B }`.
    // Lowering emits the left whenever a branch's arms are narrower than
    // the stack, and every other branch law is stated about the right.
    let arm = |v| Term::pad_compose(Term::drop(1), op(Prim::Push(Value::Int(v))));
    let framed = Term::par(Term::id(1), Term::branch(arm(1), arm(2)).unwrap());
    let opened = Term::branch(
        Term::par(Term::id(1), arm(1)),
        Term::par(Term::id(1), arm(2)),
    )
    .unwrap();
    assert!(provable(&framed, &opened));
}

#[test]
fn an_unequal_pair_of_terms_does_not_meet() {
    let one = op(Prim::Push(Value::Int(1)));
    let two = op(Prim::Push(Value::Int(2)));
    assert!(!provable(&one, &two));
}

#[test]
fn the_block_counit_closes_alone() {
    // `copy(2) ; id(2) * drop(2)` = `id(2)`: the counit at block width,
    // which is what `discarded_work_on_copies` bottoms out in.
    let lhs = Term::compose(Term::copy(2), Term::par(Term::id(2), Term::drop(2))).unwrap();
    assert!(provable(&lhs, &Term::id(2)));
}

#[test]
fn every_rule_survives_the_corpus_smoke() {
    // The rules on a term with a call in it: nothing panics, nothing
    // unions across arities (the schema's `:no-merge` would refuse).
    let call = Term::call(bytecode::SentenceIndex::from(7), Arity::new(2, 1));
    let lhs = Term::pad_compose(call.clone(), Term::drop(1));
    let rhs = Term::drop(2);
    assert!(provable(&lhs, &rhs), "drop-nat reads a call's arity");
}
