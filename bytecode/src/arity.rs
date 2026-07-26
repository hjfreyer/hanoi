use std::collections::{HashMap, HashSet};
use crate::library::{Library, SentenceIndex, Annotation};
use crate::opcode::Instruction;

/// Checks whether all annotated sentences in the library obey their declared arity.
pub fn check_arities(library: &Library) -> Result<(), String> {
    let mut memo = HashMap::new();

    for (s_idx_raw, annotations) in library.annotations.iter().enumerate() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        for ann in annotations {
            let Annotation::Arity(n, m) = ann;
            let name = &library.names[s_idx];
            let mut in_progress = HashSet::new();
            let (inferred_n, inferred_m, is_panic) = get_or_infer_arity(s_idx, library, &mut memo, &mut in_progress)
                .map_err(|e| format!("Error checking arity for sentence '{}': {}", name, e))?;

            if inferred_n > *n {
                return Err(format!(
                    "Sentence '{}' (index {:?}) requires {} inputs, which exceeds its annotated arity {}",
                    name, s_idx, inferred_n, n
                ));
            }

            if !is_panic {
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

    Ok(())
}

fn get_or_infer_arity(
    s_idx: SentenceIndex,
    library: &Library,
    memo: &mut HashMap<SentenceIndex, (i64, i64, bool)>,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Result<(i64, i64, bool), String> {
    if let Some(&arity) = memo.get(&s_idx) {
        return Ok(arity);
    }

    let name = &library.names[s_idx];

    if in_progress.contains(&s_idx) {
        return Err(format!("Recursion/cycle detected at sentence index {:?} ({})", s_idx, name));
    }

    in_progress.insert(s_idx);
    let result = infer_arity_of_instructions(s_idx, library, memo, in_progress)?;
    in_progress.remove(&s_idx);
    memo.insert(s_idx, result);
    Ok(result)
}

fn infer_arity_of_instructions(
    s_idx: SentenceIndex,
    library: &Library,
    memo: &mut HashMap<SentenceIndex, (i64, i64, bool)>,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Result<(i64, i64, bool), String> {
    let sentence = &library.sentences[s_idx];
    let mut initial_req = 0i64;
    let mut current_size = 0i64;

    for inst in sentence {
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
            Instruction::SetContains | Instruction::SetUnion | Instruction::SetIntersection |
            Instruction::SetDifference | Instruction::SymbolCharAt => {
                let req = 2;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 1;
            }
            Instruction::Not | Instruction::Negate | Instruction::Print |
            Instruction::SetComplement | Instruction::SetSingleton | Instruction::SymbolLen |
            Instruction::SetChoose => {
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
                // If annotated, check if initial_req <= N. If so, return annotated arity.
                if let Some(Annotation::Arity(n, m)) = library.annotations[s_idx].first() {
                    if initial_req <= *n {
                        return Ok((*n, *m, true));
                    } else {
                        return Err(format!(
                            "Sentence '{}' (index {:?}) requires {} inputs up to panic, which exceeds annotated arity {}",
                            library.names[s_idx], s_idx, initial_req, n
                        ));
                    }
                }
                return Ok((initial_req, current_size, true));
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
            Instruction::SetTuple(len) => {
                let len = *len as i64;
                let req = len;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - len + 1;
            }
            Instruction::SetRenamePrefix => {
                let req = 3;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size -= 2;
            }
            Instruction::Jump(target) => {
                let (n_target, m_target, target_panic) = get_or_infer_arity(*target, library, memo, in_progress)?;
                let req = n_target;
                if current_size < req {
                    let diff = req - current_size;
                    initial_req += diff;
                    current_size = req;
                }
                current_size = current_size - n_target + m_target;
                if target_panic {
                    return Ok((initial_req, current_size, true));
                }
            }
            Instruction::Branch(then_t, else_t) => {
                let req_cond = 1;
                if current_size < req_cond {
                    let diff = req_cond - current_size;
                    initial_req += diff;
                    current_size = req_cond;
                }
                current_size -= 1;

                let (n_then, m_then, panic_then) = get_or_infer_arity(*then_t, library, memo, in_progress)?;
                let (n_else, m_else, panic_else) = get_or_infer_arity(*else_t, library, memo, in_progress)?;

                let (n_branch, m_branch, panic_branch) = match (panic_then, panic_else) {
                    (true, true) => {
                        (std::cmp::max(n_then, n_else), 0, true)
                    }
                    (true, false) => {
                        let net_else = m_else - n_else;
                        let n_b = std::cmp::max(n_then, n_else);
                        (n_b, n_b + net_else, false)
                    }
                    (false, true) => {
                        let net_then = m_then - n_then;
                        let n_b = std::cmp::max(n_then, n_else);
                        (n_b, n_b + net_then, false)
                    }
                    (false, false) => {
                        let net_then = m_then - n_then;
                        let net_else = m_else - n_else;
                        if net_then != net_else {
                            return Err(format!(
                                "Branch targets have mismatched net stack changes: '{}' (index {:?}) has net change {}, '{}' (index {:?}) has net change {}",
                                library.names[*then_t], then_t, net_then, library.names[*else_t], else_t, net_else
                            ));
                        }
                        let n_b = std::cmp::max(n_then, n_else);
                        (n_b, n_b + net_then, false)
                    }
                };

                let req_branch = n_branch;
                if current_size < req_branch {
                    let diff = req_branch - current_size;
                    initial_req += diff;
                    current_size = req_branch;
                }
                current_size = current_size - n_branch + m_branch;
                if panic_branch {
                    return Ok((initial_req, current_size, true));
                }
            }
        }
    }

    Ok((initial_req, current_size, false))
}
