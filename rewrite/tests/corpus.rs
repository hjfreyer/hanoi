//! The corpus's identities, proved.
//!
//! This is the regression net for the whole pipeline: every identity the
//! corpus states must close — by its written proof in the `.hant` beside it
//! where it has one, by the default `diagram` where it does not — and any
//! straggler is named exactly. An engine change that breaks a proof fails
//! here, and so does the happy surprise of a straggler starting to close,
//! which is the cue to shorten the list. The list is empty today.

use rewrite::corpus;
use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::Prover;

#[test]
fn the_corpus_identities_close() {
    let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits in the workspace")
        .join("tests");
    let mut corpus = corpus::load(&tests).unwrap();
    assert_eq!(corpus.problems, Vec::<String>::new());

    // Nothing is expected to stick. The path-condition claim in `types_test`
    // was the last one, and `inline diagram` discharges it: the engine
    // builds the case analysis the old proof wrote out by hand.
    let expected_stragglers: [&str; 0] = [];

    let prover = Prover::new(&corpus.library);
    let mut stragglers = Vec::new();
    for (idx, identity) in corpus.library.identities.iter_enumerated() {
        let goal = Goal::of_identity(&mut corpus.terms, &corpus.library, idx).unwrap();
        match prover
            .prove(&mut corpus.terms, goal, corpus.proofs.get(&idx))
            .unwrap()
        {
            Outcome::Closed(_) => {}
            Outcome::Stuck(_) => stragglers.push(identity.name.clone()),
        }
    }
    assert_eq!(
        stragglers, expected_stragglers,
        "the set of unproved identities moved; if one now closes, take it off the list"
    );
}
