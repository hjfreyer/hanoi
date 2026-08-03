// The proof that `barista::customer_impl::emit_does_pre_and_post` is the
// constant-true program:
//
//     emit_does_pre_and_post  ==  drop; push true
//
// derived by nothing but the window-local rules of `bin/rewrite`, checked one
// firing at a time. Run it yourself:
//
//     cargo run --bin rewrite -- tests emit_does_pre_and_post \
//         --tactics emit_theorem.tac -t 'opened; endgame; qed' --check
//
// The stages: `opened` opens the checks and shares the caller's copy so
// `specialize_equal` refines the values `emit` actually destructures, which
// folds three of the four distributed panics. `endgame` expands one
// conjunction layer per round (`shortcut_and`), giving the union's branchless
// last variant an arm to learn in, and the fourth panic folds like the
// others; the decided guard skeletons drain. `qed` is the aimed endgame over
// what remains — the postcondition's re-checks of values whose copies the
// precondition checked. Deliveries walk each copy's creation down the tree to
// its consumer, the re-checks hoist out of their branches and fuse with the
// precondition's checks (`dup_probe_mixed`), `retain_condition` pays each
// fused answer off as a literal in the arms, and everything folds to
// `drop; push true`.
//
// An aimed step (`at`, `then_at`, `else_at`) that misses fails the whole
// script, so the proof is self-checking: it either replays exactly or fails
// loudly. The corpus test `emit_does_pre_and_post_reduces_to_constant_true`
// includes this file verbatim and asserts the final shape. The indices are
// written against the listing (`--positions`) at each intermediate state, and
// are deliberately frozen: this is a finished derivation, kept as a
// regression test.
//
// No rule was ever told a fact. Every hypothesis the proof needed travelled
// as a construction — a copy's creation, a check's answer, a retained
// literal — that the rewriter verified window by window.

tactic open = repeat_n(3, once(inline); distribute; cleanup);
tactic share = repeat(bu(each(copy_assoc); each(float); each(unfactor_branch);
                         each(flatten_call); each(rebuild_copy); each(cancel_tuple)));
tactic redirect = repeat(bu(each(copy_assoc); each(float); each(unfactor_branch);
                            each(flatten_call);
                            each(annihilate_drop, noop, pick_drop_to_roll)));
tactic deliver = repeat(bu(each(copy_assoc, copy_comm); each(rebuild_copy); each(float);
                           each(unfactor_branch); each(flatten_call);
                           each(annihilate_drop, noop, pick_drop_to_roll);
                           each(copy_const, cancel_tuple, probe_tuple, probe_length)));
tactic drain = repeat(bu(each(discharge_untuple); each(discharge_length);
                         each(merge_branch, merge_copied_branch, annihilate_equal,
                              annihilate_and, annihilate_drop, pick_drop_to_roll, noop);
                         each(commute_framed_lit); each(float_lit);
                         each(fold_const, fold_const_unary, bool_identity,
                              cancel_tuple, probe_tuple, probe_length)));
tactic opened = open; share; cleanup;
                then(then(once(inline); distribute; cleanup));
                then(then(redirect; bu(each(specialize_equal)); cleanup));
                repeat(bu(each(inline); each(flatten_call)));
                repeat(bu(each(sink); each(collapse); each(flatten_call))); cleanup;
                repeat_n(12, distribute; deliver; bu(each(specialize_equal)); cleanup);
tactic round = bu(each(shortcut_and));
               repeat_n(3, distribute; deliver; bu(each(specialize_equal)); cleanup);
               drain;
tactic splice = repeat(bu(each(sink); each(collapse); each(flatten_call);
                          each(fold_and_branch); each(distribute_drop); each(float_drop);
                          each(annihilate_and);
                          each(annihilate_drop, pick_drop_to_roll, noop,
                               fold_branch, merge_branch, annihilate_equal);
                          each(discharge_untuple); each(discharge_length);
                          each(fold_const, fold_const_unary, bool_identity,
                               cancel_tuple, probe_tuple, probe_length,
                               copy_const, copy_comm)));
tactic endgame = repeat_n(8, round); repeat_n(6, splice; drain; round);

// The whole proof of `emit_does_pre_and_post == drop; push true`, from the
// panic-free form. Deliveries walk each copy's creation to its consumer;
// the postcondition's re-checks hoist out of their branches and fuse with
// the precondition's checks (`dup_probe_mixed`); `retain_condition` pays
// each fused copy off as a literal in the arms; the sweeps fold what is
// decided and the guard skeleton discharges. Every `at` that misses fails
// the whole script, so this running at all is most of the theorem — and the
// final shape is the rest.
tactic qed =
  then_at(2, then_at(4, at(1, copy_comm_inv); at(2, copy_comm);
                        at(3, float); at(4, float)));
  then_at(2, then_at(4, at(5, unfactor_branch)));
  then_at(2, then_at(4, else_at(5,
    at(0, copy_comm); at(1, float); at(2, float); at(3, unfactor_branch);
    then_at(3, at(1, float)))));
  then_at(2, then_at(4, else_at(5, then_at(3,
    at(2, unfactor_branch);
    then_at(2, at(0, float); at(1, unfactor_branch);
               then_at(1, at(1, annihilate_drop));
               else_at(1, at(1, annihilate_drop)));
    else_at(2, at(0, float_drop); at(2, annihilate_drop))))));
  then_at(2, then_at(4,
    at(1, copy_swap); at(2, float); at(3, float); at(4, unfactor_branch);
    else_at(4,
      at(0, copy_swap); at(1, float); at(2, float); at(3, unfactor_branch);
      then_at(3, at(0, copy_comm); at(1, float); at(2, unfactor_branch);
                 else_at(2, at(0, annihilate_drop))))));
  then_at(2, then_at(4, else_at(4, then_at(3, then_at(2,
    at(2, factor_branch); at(3, hoist_probe);
    then_at(4, at(0, sink)); at(4, hoist_probe);
    at(2, sink); at(1, sink); at(0, sink_probe))))));
  then_at(2, then_at(4, else_at(4, then_at(3,
    at(2, hoist_probe); at(1, sink); at(0, sink_probe);
    at(0, dup_probe_mixed); at(1, retain_condition)))));
  then_at(2, then_at(4, else_at(4, then_at(3, then_at(2,
    at(3, sink); at(2, sink); at(1, sink_probe))))));
  then_at(2, then_at(4, else_at(4, then_at(3, then_at(2,
    at(1, dup_probe_mixed); at(3, unfactor_branch); at(2, retain_condition))))));
  repeat_n(6, repeat(bu(each(fission))); splice; drain; round); drain;
  then_at(2, then_at(4, else_at(4, then_at(3,
    at(3, retain_condition);
    then_at(3, at(4, retain_condition))))));
  repeat_n(6, repeat(bu(each(fission))); splice; drain; round); drain;
  then_at(2, then_at(4, else_at(4, then_at(3, then_at(3, then_at(3, at(2, sink)))))));
  repeat_n(4, splice; drain);
  then_at(2, then_at(4, else_at(4, then_at(3, then_at(3, then_at(3,
    at(0, float); at(1, float_drop)))))));
  repeat_n(4, splice; drain);
  then_at(2, then_at(4, else_at(4, else_at(3,
    then_at(5, at(0, float); at(1, float_drop); at(3, annihilate_drop));
    else_at(5, then_at(3, at(0, float); at(1, float_drop); at(3, annihilate_drop)))))));
  repeat_n(4, splice; drain);
