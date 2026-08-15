//! The corpus's identities, proved.
//!
//! This is the regression net for the whole pipeline: every identity
//! `tests/identities.hana` states must close, and the one known straggler is
//! named exactly — so a rule change that breaks a proof fails here, and so
//! does the happy surprise of the straggler starting to close, which is the
//! cue to shorten the list.

use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::{Config, Prover};

#[test]
fn the_corpus_identities_close() {
    let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits in the workspace")
        .join("tests");
    let text = std::fs::read_to_string(tests.join("main.hana")).unwrap();

    let mut map = bytecode::SourceMap::new();
    let file = map.add("main.hana", text);
    let library = bytecode::assemble_source(&mut map, file, Some(&tests))
        .unwrap_or_else(|e| panic!("{}", map.render(&e)));

    // The path-condition claim in types_test needs a case split on the tested
    // value — a goal-level move the pipeline does not have yet. Its residual
    // is stable and its deadline is the case-split strategy, not a rule.
    let expected_stragglers = ["types_test::number_does_pre_and_post_is_constant"];

    let prover = Prover::new(&library, Config::default());
    let mut stragglers = Vec::new();
    for (idx, identity) in library.identities.iter_enumerated() {
        let goal = Goal::of_identity(&library, idx).unwrap();
        match prover.prove(&goal, &[]).unwrap() {
            Outcome::Closed(_) => {}
            Outcome::Stuck(_) => stragglers.push(identity.name.clone()),
        }
    }
    assert_eq!(
        stragglers, expected_stragglers,
        "the set of unproved identities moved; if one now closes, take it off the list"
    );
}
