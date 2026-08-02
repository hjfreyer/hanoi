use std::collections::{HashMap, HashSet};
use crate::library::{Library, SentenceIndex, Annotation, Arity};
use crate::opcode::Instruction;

/// Checks whether all sentences in the library obey their declared arity,
/// and populates the instruction_arities field in Library.
pub fn check_arities(library: &mut Library) -> Result<(), String> {
    let mut memo = HashMap::new();
    let mut instruction_arities = HashMap::new();

    // 1. Check/infer all non-recursive sentences
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        if is_recursive(s_idx, library) {
            continue;
        }
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
                match inferred {
                    Arity::Panic { inputs: inferred_n } => {
                        if inferred_n > *n {
                            return Err(format!(
                                "Sentence '{}' (index {:?}) requires {} inputs, which exceeds its annotated arity {}",
                                name, s_idx, inferred_n, n
                            ));
                        }
                    }
                    Arity::Normal { inputs: inferred_n, outputs: inferred_m } => {
                        if inferred_n > *n {
                            return Err(format!(
                                "Sentence '{}' (index {:?}) requires {} inputs, which exceeds its annotated arity {}",
                                name, s_idx, inferred_n, n
                            ));
                        }

                        let net_change = inferred_m - inferred_n;
                        let expected_net_change = m - n;
                        if net_change != expected_net_change {
                            return Err(format!(
                                "Sentence '{}' (index {:?}) has net stack change of {}, but annotated arity {} -> {} expects net change of {}",
                                name, s_idx, net_change, n, m, expected_net_change
                            ));
                        }
                    }
                }
            }
        }
    }

    // 2. Store final instruction arities into library.instruction_arities.
    // Recursive/opted-out sentences receive None, while checked ones receive Some(vec).
    let mut final_arities = typed_index_collections::TiVec::with_capacity(library.sentences.len());
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        if is_recursive(s_idx, library) {
            final_arities.push(None);
        } else {
            let arities = instruction_arities.remove(&s_idx);
            final_arities.push(arities);
        }
    }
    library.instruction_arities = final_arities;

    Ok(())
}

fn is_recursive(s_idx: SentenceIndex, library: &Library) -> bool {
    library.annotations[s_idx]
        .iter()
        .any(|ann| matches!(ann, Annotation::Recursive))
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
        return Err(format!("Recursion/cycle detected at sentence index {:?} ({})", s_idx, name));
    }

    in_progress.insert(s_idx);
    let (result, arities) = infer_arity_of_instructions(
        s_idx,
        library,
        memo,
        in_progress,
        instruction_arities,
    )?;
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
/// A `#[recursive]` sentence is skipped by inference entirely, so there the
/// annotation is the only thing that can answer; without one the arity is
/// genuinely unknown and this returns `None`.
///
/// Public for `bin/rewrite`, whose `Call` nodes need their target's arity to
/// decide whether a dip may move past them.
pub fn sentence_arity(library: &Library, s_idx: SentenceIndex) -> Option<Arity> {
    if is_recursive(s_idx, library) {
        return declared_arity(library, s_idx);
    }
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

fn declared_arity(library: &Library, s_idx: SentenceIndex) -> Option<Arity> {
    library.annotations[s_idx].iter().find_map(|ann| match ann {
        Annotation::Arity(inputs, outputs) => Some(Arity::Normal {
            inputs: *inputs,
            outputs: *outputs,
        }),
        _ => None,
    })
}

/// What one instruction takes off the top of the stack and leaves there.
///
/// `None` where the effect is not local to the instruction: `Panic` ends
/// execution, and `Dip`/`Branch` depend on the sentences they call.
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
        Instruction::Drop | Instruction::Assert => (1, 0),
        // Pick reads at `d` and copies it to the top, so it touches everything
        // down to that depth even though it consumes nothing.
        Instruction::Pick(d) => (*d as i64 + 1, *d as i64 + 2),
        Instruction::Roll(d) => (*d as i64 + 1, *d as i64 + 1),
        Instruction::Equal
        | Instruction::Greater
        | Instruction::Less
        | Instruction::Add
        | Instruction::Subtract
        | Instruction::Multiply
        | Instruction::Divide
        | Instruction::Modulo
        | Instruction::And
        | Instruction::Or
        | Instruction::SymbolCharAt => (2, 1),
        Instruction::Not
        | Instruction::Negate
        | Instruction::Print
        | Instruction::SymbolLen
        | Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
        | Instruction::IsSymbol
        | Instruction::IsTuple
        | Instruction::TupleLength => (1, 1),
        Instruction::AssertEqual => (2, 0),
        Instruction::Tuple(n) => (*n as i64, 1),
        Instruction::Untuple(n) => (1, *n as i64),
        Instruction::Panic | Instruction::Dip(..) | Instruction::Branch(..) => return None,
    })
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
            Instruction::Panic => {
                let mut annotated_arity = None;
                for ann in &library.annotations[s_idx] {
                    if let Annotation::Arity(n, _) = ann {
                        annotated_arity = Some(*n);
                        break;
                    }
                }
                let sentence_arity = if let Some(n) = annotated_arity {
                    if initial_req <= n {
                        Arity::Panic { inputs: n }
                    } else {
                        return Err(format!(
                            "Sentence '{}' (index {:?}) requires {} inputs up to panic, which exceeds annotated arity {}",
                            library.names[s_idx], s_idx, initial_req, n
                        ));
                    }
                } else {
                    Arity::Panic { inputs: initial_req }
                };
                let n = sentence_arity.inputs();
                let mut arities: Vec<Arity> = depths.into_iter().map(|d| Arity::Normal { inputs: n, outputs: d }).collect();
                if !arities.is_empty() {
                    let last_idx = arities.len() - 1;
                    arities[last_idx] = Arity::Panic { inputs: n };
                }
                return Ok((sentence_arity, arities));
            }
            Instruction::Dip(depth, target) => {
                if is_recursive(*target, library) {
                    return Err(format!(
                        "Sentence '{}' calls recursive sentence '{}' but is not annotated with #[recursive]",
                        library.names[s_idx], library.names[*target]
                    ));
                }
                let target_arity = get_or_infer_arity(
                    *target,
                    library,
                    memo,
                    in_progress,
                    instruction_arities,
                )?;
                let (n_target, m_target, is_panic_target) = match target_arity {
                    Arity::Normal { inputs, outputs } => (inputs, outputs, false),
                    Arity::Panic { inputs } => (inputs, 0, true),
                };
                // The hidden values sit above the callee's window, so they count
                // towards the requirement but not towards the net change.
                let req = *depth as i64 + n_target;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - n_target + m_target;
                if is_panic_target {
                    let sentence_arity = Arity::Panic { inputs: initial_req };
                    let n = sentence_arity.inputs();
                    let arities = depths.into_iter().map(|d| Arity::Normal { inputs: n, outputs: d }).collect();
                    return Ok((sentence_arity, arities));
                }
            }
            Instruction::Branch(then_t, else_t) => {
                if is_recursive(*then_t, library) {
                    return Err(format!(
                        "Sentence '{}' calls recursive sentence '{}' but is not annotated with #[recursive]",
                        library.names[s_idx], library.names[*then_t]
                    ));
                }
                if is_recursive(*else_t, library) {
                    return Err(format!(
                        "Sentence '{}' calls recursive sentence '{}' but is not annotated with #[recursive]",
                        library.names[s_idx], library.names[*else_t]
                    ));
                }
                let req_cond = 1;
                if current_size < req_cond {
                    let diff = req_cond - current_size;
                    initial_req += diff;
                    current_size = req_cond;
                }
                current_size -= 1;

                let arity_then = get_or_infer_arity(
                    *then_t,
                    library,
                    memo,
                    in_progress,
                    instruction_arities,
                )?;
                let arity_else = get_or_infer_arity(
                    *else_t,
                    library,
                    memo,
                    in_progress,
                    instruction_arities,
                )?;

                let combined = combine_branch_arities(arity_then, arity_else)
                    .map_err(|e| format!(
                        "Branch targets have mismatched net stack changes: {} (then target '{}', else target '{}')",
                        e, library.names[*then_t], library.names[*else_t]
                    ))?;

                let (n_branch, m_branch, is_panic_branch) = match combined {
                    Arity::Normal { inputs, outputs } => (inputs, outputs, false),
                    Arity::Panic { inputs } => (inputs, 0, true),
                };

                let req_branch = n_branch;
                if current_size < req_branch {
                    let diff = req_branch - current_size;
                    initial_req += diff;
                    current_size = req_branch;
                }
                current_size = current_size - n_branch + m_branch;
                if is_panic_branch {
                    let sentence_arity = Arity::Panic { inputs: initial_req };
                    let n = sentence_arity.inputs();
                    let arities = depths.into_iter().map(|d| Arity::Normal { inputs: n, outputs: d }).collect();
                    return Ok((sentence_arity, arities));
                }
            }
            // Everything else has a local effect, taken from the shared table.
            // A requirement discovered here grows the sentence's input count
            // retroactively, which is why `depths` records the size *before*
            // the growth rather than the true stack depth.
            local => {
                let (n, m) = op_arity(local)
                    .expect("Panic, Dip and Branch are handled above");
                if current_size < n {
                    initial_req += n - current_size;
                    current_size = n;
                }
                current_size = current_size - n + m;
            }
        }
    }

    let sentence_arity = Arity::Normal { inputs: initial_req, outputs: current_size };
    let n = sentence_arity.inputs();
    let arities = depths.into_iter().map(|d| Arity::Normal { inputs: n, outputs: d }).collect();
    Ok((sentence_arity, arities))
}

fn combine_branch_arities(then: Arity, el: Arity) -> Result<Arity, String> {
    match (then, el) {
        (Arity::Panic { inputs: n_then }, Arity::Panic { inputs: n_else }) => {
            Ok(Arity::Panic { inputs: std::cmp::max(n_then, n_else) })
        }
        (Arity::Panic { inputs: n_then }, Arity::Normal { inputs: n_else, outputs: m_else }) => {
            let net_else = m_else - n_else;
            let n_b = std::cmp::max(n_then, n_else);
            Ok(Arity::Normal { inputs: n_b, outputs: n_b + net_else })
        }
        (Arity::Normal { inputs: n_then, outputs: m_then }, Arity::Panic { inputs: n_else }) => {
            let net_then = m_then - n_then;
            let n_b = std::cmp::max(n_then, n_else);
            Ok(Arity::Normal { inputs: n_b, outputs: n_b + net_then })
        }
        (Arity::Normal { inputs: n_then, outputs: m_then }, Arity::Normal { inputs: n_else, outputs: m_else }) => {
            let net_then = m_then - n_then;
            let net_else = m_else - n_else;
            if net_then != net_else {
                return Err(format!(
                    "then has net change {}, else has net change {}",
                    net_then, net_else
                ));
            }
            let n_b = std::cmp::max(n_then, n_else);
            Ok(Arity::Normal { inputs: n_b, outputs: n_b + net_then })
        }
    }
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
        let got = arity_of("sentence probe { add }", "probe");
        assert_eq!(
            got,
            Some(Arity::Normal {
                inputs: 2,
                outputs: 1
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
            #[arity(5, 4)]
            sentence probe { add }
        "#,
            "probe",
        );
        assert_eq!(
            got,
            Some(Arity::Normal {
                inputs: 2,
                outputs: 1
            })
        );
    }

    #[test]
    fn a_recursive_sentence_falls_back_to_its_annotation() {
        // Inference skips #[recursive] entirely, so the annotation is the only
        // thing left that can answer.
        let got = arity_of(
            r#"
            #[recursive]
            #[arity(1, 1)]
            sentence loops { jump loops }
        "#,
            "loops",
        );
        assert_eq!(
            got,
            Some(Arity::Normal {
                inputs: 1,
                outputs: 1
            })
        );
    }

    #[test]
    fn an_unannotated_recursive_sentence_has_no_knowable_arity() {
        let got = arity_of(
            r#"
            #[recursive]
            sentence loops { jump loops }
        "#,
            "loops",
        );
        assert_eq!(got, None);
    }
}
