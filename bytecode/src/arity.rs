use crate::library::{Annotation, Arity, Library, SentenceIndex};
use crate::opcode::Instruction;
use crate::source::Error;
use std::collections::{HashMap, HashSet};

/// Checks whether all sentences in the library obey their declared arity,
/// and populates the instruction_arities field in Library.
pub fn check_arities(library: &mut Library) -> Result<(), String> {
    let mut memo = HashMap::new();
    let mut instruction_arities = HashMap::new();

    // 1. Check/infer every sentence. Inference is what refuses recursion: a
    // sentence that reaches itself has no arity to work out, and this is where
    // that is discovered.
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        let mut in_progress = HashSet::new();
        let inferred = get_or_infer_arity(
            s_idx,
            library,
            &mut memo,
            &mut in_progress,
            &mut instruction_arities,
        )?;

        // Verify matches for #[arity(n, m)] annotations
        for ann in &library.annotations[s_idx] {
            if let Annotation::Arity(n, m) = ann {
                let name = &library.names[s_idx];
                if inferred.inputs > *n {
                    return Err(format!(
                        "Sentence '{}' (index {:?}) requires {} inputs, which exceeds its annotated arity {}",
                        name, s_idx, inferred.inputs, n
                    ));
                }
                if inferred.net() != m - n {
                    return Err(format!(
                        "Sentence '{}' (index {:?}) has net stack change of {}, but annotated arity {} -> {} expects net change of {}",
                        name,
                        s_idx,
                        inferred.net(),
                        n,
                        m,
                        m - n
                    ));
                }
            }
        }
    }

    // 2. Store final instruction arities into library.instruction_arities.
    // Step 1 inferred every sentence, so every one of them has an entry.
    let mut final_arities = typed_index_collections::TiVec::with_capacity(library.sentences.len());
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        final_arities.push(
            instruction_arities
                .remove(&s_idx)
                .expect("step 1 infers every sentence, or fails"),
        );
    }
    library.instruction_arities = final_arities;

    Ok(())
}

/// The two arms a `?` left behind: the rest of the block, and the early return.
///
/// Recorded by the compiler, which builds both but cannot finish the second —
/// see [`balance_early_returns`].
#[derive(Debug, Clone)]
pub(crate) struct EarlyReturn {
    /// The arm holding everything written after the `?`.
    pub(crate) rest: SentenceIndex,
    /// The arm that rebuilds the error and leaves, still short its drops.
    pub(crate) fail: SentenceIndex,
    /// The sentence the `?` was written in. Both arms are `<inline>` blocks,
    /// which is no help to a reader looking for the `?` that went wrong.
    pub(crate) in_sentence: String,
}

/// Makes an early return leave the stack the way finishing the block would.
///
/// A branch's two arms must agree on their net stack change, and `?`'s do not
/// on their own. The rest arm consumes whatever the block was holding — the
/// values below the one that was unwrapped — and the failure arm consumes only
/// the unwrapped value itself. So the failure arm drops the difference: with
/// the rest arm `(inputs -> outputs)`, it drops `inputs - outputs` values from
/// under the error it is carrying out.
///
/// That is *only* the count the arities demand, which is the honest amount. A
/// rest arm that passes a value through rather than consuming it asks for no
/// drop, and the early return passes the same value through.
///
/// This runs before [`check_arities`] and after every sentence has been
/// emitted, because the rest arm's arity is not knowable any earlier: it can
/// call sentences that had not been compiled when the `?` was met. Sites come
/// in an order that puts a nested `?` before the one enclosing it, so each rest
/// arm is already balanced by the time it is measured.
pub(crate) fn balance_early_returns(
    library: &mut Library,
    sites: &[EarlyReturn],
) -> Result<(), String> {
    // One `drop`, shared by every early return that needs one: the arm reaches
    // under its own result with `dip 1`, and what it runs there is the same
    // instruction every time.
    let mut deep_drop: Option<SentenceIndex> = None;

    for site in sites {
        let Some(arity) = sentence_arity(library, site.rest) else {
            // The rest arm does not reckon, and saying why is `check_arities`'
            // job a moment from now. Anything added here would only bury it.
            continue;
        };
        let drops = -arity.net();
        if drops < 0 {
            return Err(format!(
                "the code after a `?` in '{}' leaves {} more values than it takes, \
                 so an early return there cannot match it: it would have to invent them",
                site.in_sentence, -drops
            ));
        }
        if drops > 0 && deep_drop.is_none() {
            let idx = SentenceIndex::from(library.sentences.len());
            library.sentences.push(vec![Instruction::Drop]);
            library.names.push("<inline>".to_string());
            library.annotations.push(Vec::new());
            deep_drop = Some(idx);
        }
        for _ in 0..drops {
            library.sentences[site.fail].push(Instruction::Dip(deep_drop.unwrap()));
        }
    }
    Ok(())
}

/// Every identity's two sides must have the same *net* stack effect.
///
/// Phase 5, after `check_arities` has settled every inference and verified
/// every `#[arity]`. This is the one property of an identity that is a fact
/// about the *statement* rather than about its proof: two programs that leave
/// the stack differently are not two spellings of one thing, whatever a tactic
/// does to them.
///
/// **Net change, not full arity**, and the distinction is not a loosening for
/// convenience — it is what the interesting laws need. `pick 1 ; drop` = ε is
/// `(2 -> 2)` against `(0 -> 0)`: both leave the stack exactly as they found
/// it, but the left needs a value to look at where the right does not. Every
/// counit reads this way, and so does every annihilation, which lowers the
/// input requirement on purpose — dropping `pick 2 ; drop` drops the demand for
/// three values that only the `pick` made. `--check` in the rewriter allows the
/// same asymmetry for the same reason (`applier::net`), and refusing it here
/// would refuse exactly the equations the rewriter is built out of.
///
/// What it does still catch is a claim that leaves a different amount behind,
/// which no proof could ever discharge.
///
pub fn check_identities(library: &Library) -> Result<(), Error> {
    for identity in &library.identities {
        let effect = |side: SentenceIndex, which: &str| -> Result<(i64, i64), Error> {
            match sentence_arity(library, side) {
                Some(arity) => Ok((arity.inputs, arity.outputs)),
                // A side whose arity is unknowable says nothing at all.
                None => Err(Error::at(
                    format!(
                        "identity `{}`: the {} side has no stack effect",
                        identity.name, which
                    ),
                    identity.span,
                )
                .with_help("its arity could not be inferred; give it an `#[arity(n, m)]`")),
            }
        };

        let (li, lo) = effect(identity.lhs, "left-hand")?;
        let (ri, ro) = effect(identity.rhs, "right-hand")?;
        if lo - li != ro - ri {
            return Err(Error::at(
                format!(
                    "identity `{}`: the two sides leave the stack differently \
                     ({} -> {} against {} -> {})",
                    identity.name, li, lo, ri, ro
                ),
                identity.span,
            )
            .with_help(
                "an identity claims two programs are interchangeable, so they must \
                 leave the same amount behind — the net change, not the arity, since \
                 `pick 1 ; drop` = nothing is (2 -> 2) against (0 -> 0)",
            ));
        }
    }
    Ok(())
}

fn get_or_infer_arity(
    s_idx: SentenceIndex,
    library: &Library,
    memo: &mut HashMap<SentenceIndex, Arity>,
    in_progress: &mut HashSet<SentenceIndex>,
    instruction_arities: &mut HashMap<SentenceIndex, Vec<Arity>>,
) -> Result<Arity, String> {
    if let Some(&arity) = memo.get(&s_idx) {
        return Ok(arity);
    }

    let name = &library.names[s_idx];

    if in_progress.contains(&s_idx) {
        return Err(format!(
            "Sentence '{}' (index {:?}) reaches itself, and recursion is forbidden: \
             a sentence must have a finite expansion, so a loop has to be written out \
             as the steps it takes",
            name, s_idx
        ));
    }

    in_progress.insert(s_idx);
    let (result, arities) =
        infer_arity_of_instructions(s_idx, library, memo, in_progress, instruction_arities)?;
    in_progress.remove(&s_idx);
    memo.insert(s_idx, result);
    instruction_arities.insert(s_idx, arities);
    Ok(result)
}

/// What a whole sentence takes off the stack and leaves on it.
///
/// Inference first, which is what [`check_arities`] itself uses when it meets a
/// `Dip` — a sentence's declared `#[arity]` may ask for more inputs than it
/// touches, and a caller cares about what is actually consumed.
///
/// Public for `bin/rewrite`, whose `Call` nodes need their target's arity to
/// decide whether a dip may move past them.
pub fn sentence_arity(library: &Library, s_idx: SentenceIndex) -> Option<Arity> {
    let mut memo = HashMap::new();
    let mut in_progress = HashSet::new();
    let mut instruction_arities = HashMap::new();
    get_or_infer_arity(
        s_idx,
        library,
        &mut memo,
        &mut in_progress,
        &mut instruction_arities,
    )
    .ok()
}

/// What one instruction takes off the top of the stack and leaves there.
///
/// `None` where the effect is not local to the instruction: `Dip` and `Branch`
/// depend on the sentences they call.
///
/// This is the single source of truth for per-instruction stack effects, and it
/// is deliberately public: `bin/rewrite` needs the same numbers to decide
/// whether a dip may move past an instruction. A second copy over there is a
/// silent hazard rather than a duplication — the interchange rule's side
/// condition is computed from `m`, so one wrong entry permits an unsound
/// rewrite with nothing to catch it.
pub fn op_arity(inst: &Instruction) -> Option<(i64, i64)> {
    Some(match inst {
        Instruction::Push(_) => (0, 1),
        Instruction::Drop => (1, 0),
        Instruction::Copy => (1, 2),
        Instruction::Swap => (2, 2),
        Instruction::Equal | Instruction::And | Instruction::Or => (2, 1),
        Instruction::Not
        | Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsConstString
        | Instruction::IsSymbol
        | Instruction::IsTuple => (1, 1),
        // The fallible instructions, each one output wider than the value it
        // computes because the extra slot holds the success flag. See
        // [`is_fallible`].
        Instruction::Greater
        | Instruction::Less
        | Instruction::Add
        | Instruction::Subtract
        | Instruction::Multiply
        | Instruction::Divide
        | Instruction::Modulo
        | Instruction::ConstStringCharAt => (2, 2),
        Instruction::Negate | Instruction::ConstStringLen | Instruction::TupleLength => (1, 2),
        Instruction::Untuple(n) => (1, *n as i64 + 1),
        Instruction::Tuple(n) => (*n as i64, 1),
        Instruction::Jump(..) | Instruction::Dip(..) | Instruction::Branch(..) => return None,
    })
}

/// Whether this instruction reports success with a flag on top of its result.
///
/// A fallible instruction is still **total** — it answers on every input (see
/// `docs/totality.md`). What the flag adds is that the answer says whether it
/// was computed or invented: `add` on two symbols leaves `0` and `false`, and
/// on two numbers leaves the sum and `true`.
///
/// The arity is fixed either way, which is the point. A caller's stack does not
/// depend on data, so the arity checker still works on shape alone and every
/// rule that moves code past an instruction reads one pair of numbers rather
/// than reasoning about which branch it took.
///
/// Kept beside [`op_arity`] because the two must agree: a fallible instruction
/// is exactly one whose output count includes a slot the value does not need.
/// The VM produces the flag, `assemble` decides whether to drop it, and
/// `bin/rewrite` folds it — three readers, one table.
pub fn is_fallible(inst: &Instruction) -> bool {
    matches!(
        inst,
        Instruction::Greater
            | Instruction::Less
            | Instruction::Add
            | Instruction::Subtract
            | Instruction::Multiply
            | Instruction::Divide
            | Instruction::Modulo
            | Instruction::Negate
            | Instruction::Untuple(_)
            | Instruction::TupleLength
            | Instruction::ConstStringLen
            | Instruction::ConstStringCharAt
    )
}

fn infer_arity_of_instructions(
    s_idx: SentenceIndex,
    library: &Library,
    memo: &mut HashMap<SentenceIndex, Arity>,
    in_progress: &mut HashSet<SentenceIndex>,
    instruction_arities: &mut HashMap<SentenceIndex, Vec<Arity>>,
) -> Result<(Arity, Vec<Arity>), String> {
    let sentence = &library.sentences[s_idx];
    let mut initial_req = 0i64;
    let mut current_size = 0i64;
    let mut depths = Vec::new();

    for inst in sentence {
        depths.push(current_size);
        match inst {
            // Both call instructions, reached through the accessor so that
            // neither can be walked past: `jump` hides nothing and `dip` hides
            // one, and that is the whole of what separates them here.
            call if call.callee().is_some() => {
                let target = call.callee().expect("guarded by the arm");
                let depth = call.hidden().expect("a call hides a known amount");
                let target_arity =
                    get_or_infer_arity(target, library, memo, in_progress, instruction_arities)?;
                let (n_target, m_target) = (target_arity.inputs, target_arity.outputs);
                // The hidden value sits above the callee's window, so it counts
                // towards the requirement but not towards the net change.
                let req = depth as i64 + n_target;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - n_target + m_target;
            }
            Instruction::Branch(then_t, else_t) => {
                let req_cond = 1;
                if current_size < req_cond {
                    let diff = req_cond - current_size;
                    initial_req += diff;
                    current_size = req_cond;
                }
                current_size -= 1;

                let arity_then =
                    get_or_infer_arity(*then_t, library, memo, in_progress, instruction_arities)?;
                let arity_else =
                    get_or_infer_arity(*else_t, library, memo, in_progress, instruction_arities)?;

                let combined = combine_branch_arities(arity_then, arity_else)
                    .map_err(|e| format!(
                        "Branch targets have mismatched net stack changes: {} (then target '{}', else target '{}')",
                        e, library.names[*then_t], library.names[*else_t]
                    ))?;

                let (n_branch, m_branch) = (combined.inputs, combined.outputs);

                let req_branch = n_branch;
                if current_size < req_branch {
                    let diff = req_branch - current_size;
                    initial_req += diff;
                    current_size = req_branch;
                }
                current_size = current_size - n_branch + m_branch;
            }
            // Everything else has a local effect, taken from the shared table.
            // A requirement discovered here grows the sentence's input count
            // retroactively, which is why `depths` records the size *before*
            // the growth rather than the true stack depth.
            local => {
                let (n, m) = op_arity(local).expect("Dip and Branch are handled above");
                if current_size < n {
                    initial_req += n - current_size;
                    current_size = n;
                }
                current_size = current_size - n + m;
            }
        }
    }

    let sentence_arity = Arity {
        inputs: initial_req,
        outputs: current_size,
    };
    let n = sentence_arity.inputs;
    let arities = depths
        .into_iter()
        .map(|d| Arity {
            inputs: n,
            outputs: d,
        })
        .collect();
    Ok((sentence_arity, arities))
}

/// What a branch takes and leaves, given what its two arms do.
///
/// The arms must agree on their *net* change — one that leaves a value where
/// the other leaves none is not a branch anything can reckon — and the inputs
/// are the deeper of the two demands, since the branch has to satisfy whichever
/// arm runs.
fn combine_branch_arities(then: Arity, el: Arity) -> Result<Arity, String> {
    if then.net() != el.net() {
        return Err(format!(
            "then has net change {}, else has net change {}",
            then.net(),
            el.net()
        ));
    }
    let inputs = std::cmp::max(then.inputs, el.inputs);
    Ok(Arity {
        inputs,
        outputs: inputs + then.net(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assemble;

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
    fn an_ordinary_sentence_is_inferred() {
        // Two operands in, the sum and its success flag out.
        let got = arity_of("sentence probe { add }", "probe");
        assert_eq!(
            got,
            Some(Arity {
                inputs: 2,
                outputs: 2
            })
        );
    }

    #[test]
    fn inference_wins_over_a_wider_annotation() {
        // The checker permits an annotation that asks for more than the body
        // touches, but a caller only loses what is actually consumed — which is
        // what `check_arities` itself uses when it meets a Dip.
        let got = arity_of(
            r#"
            #[arity(5, 5)]
            sentence probe { add }
        "#,
            "probe",
        );
        assert_eq!(
            got,
            Some(Arity {
                inputs: 2,
                outputs: 2
            })
        );
    }

    /// The `type` sugar's checks compile, and nothing in them can fail.
    #[test]
    fn the_type_sugar_generates_checks_that_compile() {
        assert!(assemble("type Pair (int, int);").is_ok());
        assert!(assemble("enum E { A(int), B(symbol) }").is_ok());
    }
}
