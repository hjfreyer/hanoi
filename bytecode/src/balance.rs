//! Phase 5a: give a branch's two arms one arity, by padding the narrower.
//!
//! [`check_arities`][crate::check_arities] holds the arms of a `branch` to the
//! same arity — not merely the same net stack change. That is the strict
//! reading, and it is the right one: the arms are alternatives for a single
//! position in the program, so whatever composes with the branch composes with
//! each of them, and an arm that asked for less than its sibling would be a
//! program whose demand on the stack depended on a value.
//!
//! It is also, written out longhand, a nuisance. `branch { } { drop 0 push
//! true }` is `(0 -> 0)` against `(1 -> 1)` and means exactly what it looks
//! like it means; making the user say
//!
//! ```text
//! branch { par { id 1 } { } } { drop 0 push true }
//! ```
//!
//! would be asking them to write down what the compiler can see. So this runs
//! first and writes it for them: the narrower arm becomes `par { id k } { arm
//! }`, which is the same program run in a frame `k` values wider.
//!
//! # Why the padding is materialized here and nowhere else
//!
//! A branch arm is the one place in the ISA where two programs meet and neither
//! has anywhere to put the difference. Everywhere else the padding is already
//! written down or does not need to be:
//!
//! * Along a sentence, an instruction applies to the top of whatever stack it
//!   finds, so `push 1 ; add` *is* `push 1 ; par { id 1 } { add }` — the wider
//!   frame is the sentence's own, and materializing it would say nothing new
//!   while tripling the instruction count.
//! * `dip k { X }` carries its padding in the operand: it is `par { X } { id k
//!   }`, and the `k` is the `id`.
//! * A `par`'s own arms are independent by construction. They have no shared
//!   width to agree on.
//!
//! # Termination
//!
//! Padding an arm widens the branch, which widens the sentence holding it,
//! which can uncover a mismatch one level further out — so this runs to a
//! fixpoint. Widths only ever grow and are bounded by the widest arity in the
//! program, and each round settles every mismatch currently visible, so the
//! number of rounds is bounded by the depth of the call tree.
//!
//! # The padding this pass inserts
//!
//! [`PADDED_ARM`] names the wrappers, and the name is load-bearing rather than
//! decorative: `bin/rewrite` opens `par { id k } { X }` back into plain `X`,
//! and it is sound to do that **only** for a wrapper from here.
//!
//! Dropping the `id k` drops a demand for `k` values, and a node sequence has
//! nowhere to put one — its nodes already have whatever they do not touch
//! beneath them. For a wrapper from this pass that costs nothing, because the
//! demand is guaranteed to survive elsewhere: padding goes to the *wider* of
//! the two arms, so the sibling still asks for every value the `id` was asking
//! for, and the rewriter reads a branch's arity off the hungrier arm. For a
//! `par` somebody wrote by hand there is no sibling and no such guarantee, so
//! the demand would simply vanish — and an understated arity is a soundness
//! bug rather than an imprecision.

use std::collections::HashMap;

use crate::arity::inferred_arities;
use crate::library::{Arity, Library, Sentence, SentenceIndex};
use crate::opcode::Instruction;

/// The name given to a `par` wrapper this pass inserts.
///
/// Distinct from `<inline>`, which is what phase 4 calls a block the user
/// wrote: nobody wrote this one, and a dump that called it `<inline>` would
/// send a reader looking for source that is not there.
///
/// Public because `bin/rewrite` reads the padding back off, and it is allowed
/// to do that **only** for a wrapper this pass inserted — see
/// [`the_padding_this_pass_inserts`](self#the-padding-this-pass-inserts).
pub const PADDED_ARM: &str = "<padded arm>";

/// The name given to the `id n` sentence that fills a wrapper's other arm.
const IDENTITY: &str = "<id>";

/// Pads branch arms until every branch's two arms have the same input count.
pub fn balance(library: &mut Library) {
    // One round per level the widening could have to climb. Reaching the bound
    // would mean widths that keep growing, which they cannot: every pad closes
    // a gap against a *fixed* sibling arity, so nothing here is a guess that
    // could be revised upward twice for the same reason.
    let rounds = library.sentences.len() + 1;
    for _ in 0..rounds {
        if !balance_round(library) {
            return;
        }
    }
    debug_assert!(false, "branch padding did not settle in {} rounds", rounds);
}

/// One sweep: pads every branch whose arms disagree. Returns whether it padded
/// anything.
fn balance_round(library: &mut Library) -> bool {
    let arities = inferred_arities(library);
    let edits = mismatches(library, &arities);
    if edits.is_empty() {
        return false;
    }
    for edit in edits {
        let then_t = pad(library, edit.then_t, edit.then_pad);
        let else_t = pad(library, edit.else_t, edit.else_pad);
        library.sentences[edit.at][edit.ip] = Instruction::Branch(then_t, else_t);
    }
    true
}

/// A branch whose arms want different amounts of stack, and by how much.
struct Mismatch {
    at: SentenceIndex,
    ip: usize,
    then_t: SentenceIndex,
    then_pad: i64,
    else_t: SentenceIndex,
    else_pad: i64,
}

fn mismatches(library: &Library, arities: &HashMap<SentenceIndex, Arity>) -> Vec<Mismatch> {
    let mut found = Vec::new();
    for (at, sentence) in library.sentences.iter_enumerated() {
        for (ip, inst) in sentence.iter().enumerate() {
            let Instruction::Branch(then_t, else_t) = inst else {
                continue;
            };
            // An arm whose arity is not knowable is one `check_arities` is
            // about to refuse by name. Padding it would only move the
            // complaint onto a sentence nobody wrote.
            let (Some(then_a), Some(else_a)) = (arities.get(then_t), arities.get(else_t)) else {
                continue;
            };
            let want = then_a.inputs().max(else_a.inputs());
            let then_pad = want - then_a.inputs();
            let else_pad = want - else_a.inputs();
            if then_pad == 0 && else_pad == 0 {
                continue;
            }
            found.push(Mismatch {
                at,
                ip,
                then_t: *then_t,
                then_pad,
                else_t: *else_t,
                else_pad,
            });
        }
    }
    found
}

/// `arm` widened by `width`, as `par { id width } { arm }`.
///
/// The `id` goes in the *first* arm because the first arm is the deepest: the
/// padding sits under the window the original program was written against, so
/// the program itself is untouched — it simply runs in a taller frame.
fn pad(library: &mut Library, arm: SentenceIndex, width: i64) -> SentenceIndex {
    if width == 0 {
        return arm;
    }
    let id = push(library, vec![Instruction::Id(width as usize)], IDENTITY);
    push(library, vec![Instruction::Par(vec![id, arm])], PADDED_ARM)
}

fn push(library: &mut Library, body: Sentence, name: &str) -> SentenceIndex {
    let idx = SentenceIndex::from(library.sentences.len());
    // `check_arities` rebuilds `instruction_arities` whole a moment later, so
    // whether it is in step here does not matter to it. Keeping it in step
    // anyway costs a line, and means nothing that reads a `Library` has to know
    // which order the two passes ran in.
    let in_step = library.instruction_arities.len() == library.sentences.len();
    library.sentences.push(body);
    library.names.push(name.to_string());
    // Nothing generated here makes a claim. In particular not `#[recursive]`:
    // an arm that could reach one is an arm with no knowable arity, which
    // `mismatches` has already declined to touch.
    library.annotations.push(Vec::new());
    if in_step {
        library.instruction_arities.push(None);
    }
    idx
}

#[cfg(test)]
mod tests {
    use crate::arity::sentence_arity;
    use crate::assemble;
    use crate::library::Arity;
    use crate::opcode::Instruction;

    /// Every branch in the library has arms of equal arity.
    fn arms_agree(code: &str) {
        let library = assemble(code).unwrap();
        for (s_idx, sentence) in library.sentences.iter_enumerated() {
            for inst in sentence {
                let Instruction::Branch(then_t, else_t) = inst else {
                    continue;
                };
                let (Some(t), Some(e)) = (
                    sentence_arity(&library, *then_t),
                    sentence_arity(&library, *else_t),
                ) else {
                    continue;
                };
                assert_eq!(
                    t.inputs(),
                    e.inputs(),
                    "arms of the branch in '{}' disagree: {:?} against {:?}",
                    library.names[s_idx],
                    t,
                    e
                );
            }
        }
    }

    fn arity_of(code: &str, name: &str) -> Option<Arity> {
        let library = assemble(code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(i, _)| i)
            .unwrap_or_else(|| panic!("no sentence named {}", name));
        sentence_arity(&library, idx)
    }

    #[test]
    fn a_narrower_arm_is_padded_up_to_its_sibling() {
        // `{ }` is (0 -> 0) and `{ drop 0 push true }` is (1 -> 1). The empty
        // arm is widened to match rather than the branch quietly reading its
        // input count off the hungrier of the two.
        let code = r#"
            sentence chooses {
                pick 0 is_bool branch { } { drop 0 push true }
            }
        "#;
        arms_agree(code);
        let library = assemble(code).unwrap();
        assert!(
            library.names.iter().any(|n| n == "<padded arm>"),
            "expected a padded arm: {:?}",
            library.names
        );
        // Padding is not a change of meaning: the sentence has the arity it
        // had when the wider arm was silently deciding for both.
        assert_eq!(
            arity_of(code, "chooses"),
            Some(Arity::Normal {
                inputs: 1,
                outputs: 1
            })
        );
    }

    #[test]
    fn arms_that_already_agree_are_left_alone() {
        let library = assemble(
            r#"
            #[arity(2, 2)]
            sentence chooses {
                pick 0 is_bool branch { drop 0 push 1 } { drop 0 push 2 }
            }
        "#,
        )
        .unwrap();
        assert!(
            !library.names.iter().any(|n| n == "<padded arm>"),
            "nothing to pad: {:?}",
            library.names
        );
    }

    #[test]
    fn a_panicking_arm_is_padded_like_any_other() {
        // A `panic` arm constrains its input count and nothing else, so it is
        // widened the same way — and the branch still takes its outputs from
        // the arm that returns.
        let code = r#"
            sentence risky {
                pick 0 is_int branch { panic } { drop 0 add }
            }
        "#;
        arms_agree(code);
        // `{ panic }` asks for nothing and `{ drop 0 add }` asks for three, so
        // the panicking arm is widened to three and the branch reads its
        // outputs off the arm that returns.
        assert_eq!(
            arity_of(code, "risky"),
            Some(Arity::Normal {
                inputs: 3,
                outputs: 2
            })
        );
    }

    #[test]
    fn padding_climbs_through_a_nested_branch() {
        // The inner branch is widened first, which widens its arm, which
        // uncovers a mismatch in the outer one. A single sweep would have
        // stopped after the inner fix.
        arms_agree(
            r#"
            sentence nested {
                pick 0 is_int branch {
                    drop 0
                    pick 0 is_bool branch { } { drop 0 push true }
                } {
                    drop 0
                }
            }
        "#,
        );
    }

    #[test]
    fn the_generated_type_checks_need_no_padding() {
        // Worth pinning: the `type` and `enum` lowerings emit both arms of
        // every branch themselves, so if one of them were unbalanced it would
        // be a bug in the lowering rather than something for this pass to
        // paper over.
        let library = assemble(
            r#"
            type Pair (int, bool);
            type Mixed int | bool | symbol;
            enum E { A(int, bool), B(symbol) }
        "#,
        )
        .unwrap();
        assert!(
            !library.names.iter().any(|n| n == "<padded arm>"),
            "generated checks should already balance: {:?}",
            library.names
        );
    }

    #[test]
    fn arms_that_leave_different_amounts_are_still_refused() {
        // Padding fixes a disagreement about inputs. A disagreement about the
        // net change is a real error and no amount of `id` will close it.
        let err = assemble(
            r#"
            #[arity(1, 1)]
            sentence bad {
                branch { push 1 } { push 1 push 2 }
            }
        "#,
        )
        .unwrap_err();
        assert!(err.contains("mismatched net stack changes"), "{}", err);
    }
}
