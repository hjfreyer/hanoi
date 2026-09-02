//! The corpus's identities, proved.
//!
//! This is the regression net for the whole pipeline: every identity the
//! corpus states must close — by its written proof in the `.hant` beside it
//! where it has one, by the default `diagram` where it does not — and any
//! straggler is named exactly. An engine change that breaks a proof fails
//! here, and so does the happy surprise of a straggler starting to close,
//! which is the cue to shorten the list. The list is empty today.

use rewrite::corpus;
use rewrite::kernel::goal::Goal;
use rewrite::proof::Outcome;
use rewrite::strategy::Prover;

#[test]
fn the_corpus_identities_close() {
    let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("the crate sits in the workspace, beside the corpus")
        .join("hana");
    let mut corpus = corpus::load(&tests).unwrap();
    assert_eq!(corpus.problems, Vec::<String>::new());

    // Empty, and hard-won: `emit_does_pre_and_post_is_constant` — the
    // corpus's biggest goal, 351 boxes against 2 once `inline` opened it,
    // and the standing straggler while the report was being made readable —
    // closes now, by the structured `cases` tree its `.hant` writes.
    let expected_stragglers: [&str; 0] = [];

    // Dependency order: a proof that spends another identity with `by` needs
    // that one closed first, and a cycle is a load-time refusal.
    prove_them(&mut corpus, &expected_stragglers);
}

/// Every identity proved once through, in dependency order, each `by`
/// carrying the cited claim's own certified run in: nothing a proof leans
/// on is taken on trust, so the corpus adds up to exactly what each proof
/// says.
fn prove_them(corpus: &mut corpus::Corpus, expected: &[&str]) {
    let order = corpus.proving_order().unwrap();
    assert_eq!(order.len(), corpus.library.identities.len());
    let mut prover = Prover::new(&corpus.library);
    let mut stragglers = Vec::new();
    for idx in order {
        let name = corpus.library.identities[idx].name.clone();
        let goal = Goal::of_identity(&mut corpus.terms, &corpus.library, idx).unwrap();
        let stated = goal.clone();
        match prover
            .prove(&mut corpus.terms, goal, corpus.proofs.get(&idx))
            .unwrap()
        {
            Outcome::Closed { run, .. } => prover.learn(idx, &stated, &run),
            Outcome::Stuck(residual) => {
                eprintln!("{} stuck: {}", name, residual.stopped);
                stragglers.push(name)
            }
        }
    }
    stragglers.sort();
    assert_eq!(
        stragglers, expected,
        "the set of unproved identities moved; if one now closes, take it off the list"
    );
}
