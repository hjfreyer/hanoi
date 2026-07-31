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
            Instruction::Push(_) => {
                current_size += 1;
            }
            Instruction::Drop(depth) => {
                let depth = *depth as i64;
                let req = depth + 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 1;
            }
            Instruction::Pick(depth) => {
                let depth = *depth as i64;
                let req = depth + 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size += 1;
            }
            Instruction::Roll(depth) => {
                let depth = *depth as i64;
                let req = depth + 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
            }
            Instruction::Equal | Instruction::Greater | Instruction::Less |
            Instruction::Add | Instruction::Subtract | Instruction::Multiply |
            Instruction::Divide | Instruction::Modulo | Instruction::And | Instruction::Or |
            Instruction::SymbolCharAt => {
                let req = 2;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 1;
            }
            Instruction::Not | Instruction::Negate | Instruction::Print |
            Instruction::SymbolLen | Instruction::IsInt | Instruction::IsBool |
            Instruction::IsFloat | Instruction::IsSymbol | Instruction::IsTuple |
            Instruction::TupleLength => {
                let req = 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
            }
            Instruction::Assert => {
                let req = 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 1;
            }
            Instruction::AssertEqual => {
                let req = 2;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 2;
            }
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
            Instruction::Tuple(len) => {
                let len = *len as i64;
                let req = len;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - len + 1;
            }
            Instruction::Untuple(len) => {
                let len = *len as i64;
                let req = 1;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - 1 + len;
            }
            Instruction::Jump(target) => {
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
                let req = n_target;
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
