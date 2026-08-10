// Working notes for `emit_does_pre_and_post_is_constant`, which is stated
// commented-out in `barista.hana` until there is a proof to put in a `.hant`.
//
//   rewrite tests emit_pre_and_post -t "$(cat tests/barista.tac)" --fuel 200000
//
// `emit_pre_and_post` in `probes.hana` is the reflexive address for the same
// term; the claim itself is the one in `barista.hana`.
//
// This used to be one `speculate { … }` per condition, written out by hand and
// aimed with `td(once(…))` — five of them, plus an `introduce` and three
// `inv(flatten)`s to reach the arm the last one was hiding in. `lifting` places
// all of it: twenty-three firings, ninety-two steps, and nothing named.

exact(unfold_all; lifting; cleanup)
