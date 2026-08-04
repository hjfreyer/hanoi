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

fn is_total(s_idx: SentenceIndex, library: &Library) -> bool {
    library.annotations[s_idx]
        .iter()
        .any(|ann| matches!(ann, Annotation::Total))
}

/// The three instructions that can still fail for a reason about values.
///
/// Everything else is total (see `docs/totality.md`) — a fallible instruction
/// reports failure with a flag and carries on, which is a value rather than an
/// outcome. Underflow, a bad sentence index and the gas limit are structural
/// and are not what this judgment is about.
fn can_fail(inst: &Instruction) -> bool {
    matches!(
        inst,
        Instruction::Panic | Instruction::Assert | Instruction::AssertEqual
    )
}

/// The sentences an instruction can transfer control to.
fn callees(inst: &Instruction) -> Vec<SentenceIndex> {
    match inst {
        Instruction::Dip(_, target) => vec![*target],
        Instruction::Branch(then_t, else_t) => vec![*then_t, *else_t],
        _ => Vec::new(),
    }
}

/// Which sentences can fail: directly, or by reaching one that does.
///
/// A least fixpoint over the call graph, so a cycle that never reaches a
/// failing instruction comes out total rather than unknown. Unlike arity
/// inference this is a reachability question, and needs no annotation to
/// terminate.
///
/// Public because it is the useful half of [`check_totality`], and it answers
/// for *every* sentence rather than only the ones somebody annotated:
/// `bin/rewrite` wants to know whether a `Call` can fail, and the answer is the
/// same whether or not the callee says so.
pub fn failure_reachability(library: &Library) -> Vec<bool> {
    let mut can: Vec<bool> = library
        .sentences
        .iter()
        .map(|sentence| sentence.iter().any(can_fail))
        .collect();
    loop {
        let mut changed = false;
        for (s_idx, sentence) in library.sentences.iter_enumerated() {
            let i: usize = s_idx.into();
            if can[i] {
                continue;
            }
            if sentence.iter().flat_map(callees).any(|c| can[usize::from(c)]) {
                can[i] = true;
                changed = true;
            }
        }
        if !changed {
            return can;
        }
    }
}

/// Checks that every sentence claiming `#[total]` really cannot fail.
///
/// A sentence can fail if it executes `panic`, `assert` or `assert_eq`, or if
/// it can reach one that does through a `jump`, a `dip`, or either branch arm.
/// `#[total]` says it cannot, and this is what holds it to that.
///
/// **The claim is opt-in, and that is the whole design.** Requiring the
/// opposite annotation — `#[partial]` on anything that can fail — was tried and
/// collapsed under its own coverage. It needed an exemption for branch arms,
/// which have no source to annotate; another for `test` declarations, where
/// asserting is the point; and worst of all one for composer templates, which
/// are generic over the machine they wrap and so are partial exactly when their
/// argument is. Marking those partial would have made *every* composed machine
/// partial, which in a corpus where nearly everything is composed is enough to
/// make the annotation say nothing.
///
/// Turning it around removes all three cases at once. Nothing is obliged to
/// carry an annotation, so generated code, inline blocks and tests need no
/// special treatment — they simply make no claim. What gets checked is exactly
/// what somebody asserted, and [`failure_reachability`] still says what is true
/// of everything else.
///
/// The check is syntactic and therefore conservative: an `assert` on a branch
/// that cannot be taken still counts against the claim. That is the same
/// bargain the `#[recursive]` rule makes, and what keeps this a reachability
/// question rather than a proof obligation.
pub fn check_totality(library: &Library) -> Result<(), String> {
    let can = failure_reachability(library);
    for (s_idx, _) in library.sentences.iter_enumerated() {
        if !is_total(s_idx, library) || !can[usize::from(s_idx)] {
            continue;
        }
        return Err(format!(
            "Sentence '{}' is annotated #[total] but {}",
            library.names[s_idx],
            explain_failure(library, &can, s_idx)
        ));
    }
    Ok(())
}

/// Why a sentence can fail, as a route down to the instruction responsible.
///
/// Naming the immediate callee is not enough when it is an `<inline>` block or
/// a composer's sentence: what the reader needs is the `panic` at the bottom
/// and the way down to it.
fn explain_failure(library: &Library, can: &[bool], start: SentenceIndex) -> String {
    let mut route: Vec<String> = Vec::new();
    let mut seen = HashSet::new();
    let mut at = start;
    loop {
        if !seen.insert(at) {
            return format!("can fail, via {}", route.join(" -> "));
        }
        if let Some(inst) = library.sentences[at].iter().find(|i| can_fail(i)) {
            return if route.is_empty() {
                format!("executes '{}'", inst)
            } else {
                format!("reaches '{}' via {}", inst, route.join(" -> "))
            };
        }
        let Some(next) = library.sentences[at]
            .iter()
            .flat_map(callees)
            .find(|c| can[usize::from(*c)])
        else {
            return "can fail".to_string();
        };
        route.push(library.names[next].clone());
        at = next;
    }
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
        Instruction::Equal | Instruction::And | Instruction::Or => (2, 1),
        Instruction::Not
        | Instruction::Print
        | Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
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
        | Instruction::SymbolCharAt => (2, 2),
        Instruction::Negate | Instruction::SymbolLen | Instruction::TupleLength => (1, 2),
        Instruction::Untuple(n) => (1, *n as i64 + 1),
        Instruction::AssertEqual => (2, 0),
        Instruction::Tuple(n) => (*n as i64, 1),
        Instruction::Panic | Instruction::Dip(..) | Instruction::Branch(..) => return None,
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
            | Instruction::SymbolLen
            | Instruction::SymbolCharAt
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

    // -----------------------------------------------------------------------
    // #[total]
    // -----------------------------------------------------------------------

    fn totality_error(code: &str) -> String {
        assemble(code)
            .err()
            .unwrap_or_else(|| panic!("expected `{}` to be rejected", code))
    }

    #[test]
    fn claiming_totality_while_able_to_fail_is_refused() {
        for inst in ["panic", "assert", "assert_eq"] {
            let code = format!("#[total] sentence claims {{ {} }}", inst);
            let msg = totality_error(&code);
            assert!(msg.contains("#[total]"), "{}", msg);
            assert!(msg.contains(inst), "should name the instruction: {}", msg);
        }
        // Without the claim there is nothing to check, which is the point of
        // the polarity: failing is ordinary and needs no ceremony.
        for inst in ["panic", "assert", "assert_eq"] {
            assert!(
                assemble(&format!("sentence quiet {{ {} }}", inst)).is_ok(),
                "an unannotated sentence makes no claim"
            );
        }
    }

    #[test]
    fn the_claim_is_checked_through_the_call_graph() {
        // Reaching a failure counts, however far down, and the error names the
        // route rather than only the immediate callee.
        let code = r#"
            #[arity(1, 0)]
            sentence deep { assert }
            #[arity(1, 0)]
            sentence middle { jump deep }
            #[total]
            #[arity(1, 0)]
            sentence claims { jump middle }
        "#;
        let msg = totality_error(code);
        assert!(msg.contains("claims"), "{}", msg);
        assert!(msg.contains("middle") && msg.contains("deep"), "route: {}", msg);
        assert!(msg.contains("assert"), "the instruction: {}", msg);
    }

    #[test]
    fn a_branch_arm_counts_against_the_claim_that_encloses_it() {
        // The case the opposite polarity needed an exemption for. Here it needs
        // none: the arm makes no claim, the sentence that wrote it does, and
        // reachability connects the two.
        for body in [
            "pick 0 is_int branch { assert } { drop 0 }",
            "pick 0 is_int branch { drop 0 } { assert }",
            "dip 1 { drop 0 assert }",
        ] {
            let code = format!("#[total] #[recursive] sentence claims {{ {} }}", body);
            let msg = totality_error(&code);
            assert!(msg.contains("claims"), "should name the sentence: {}", msg);
            assert!(msg.contains("assert"), "should name the instruction: {}", msg);
        }
    }

    #[test]
    fn ordinary_total_code_satisfies_the_claim() {
        // Nothing here can fail, the fallible instructions included: they
        // report rather than raise.
        assert!(assemble(
            r#"
            #[total]
            #[arity(2, 1)]
            sentence arith { add }
            #[total]
            #[arity(1, 2)]
            sentence apart { untuple 2 }
            #[total]
            #[arity(2, 1)]
            sentence caller { jump arith }
            #[total]
            #[arity(1, 1)]
            sentence chooses { pick 0 is_int branch { drop 0 push 1 } { drop 0 push 2 } }
        "#
        )
        .is_ok());
    }

    #[test]
    fn a_cycle_that_never_fails_is_total() {
        // Reachability, not a fixpoint over arities: a loop with no failing
        // instruction anywhere in it satisfies the claim.
        assert!(assemble(
            r#"
            #[total]
            #[recursive]
            #[arity(1, 1)]
            sentence loops { pick 0 is_int branch { } { jump loops } }
        "#
        )
        .is_ok());
        // And one that can reach a failure does not, however deep the cycle.
        let msg = totality_error(
            r#"
            #[total]
            #[recursive]
            #[arity(1, 1)]
            sentence loops { pick 0 is_int branch { assert push 1 } { jump loops } }
        "#,
        );
        assert!(msg.contains("#[total]"), "{}", msg);
    }

    #[test]
    fn the_type_sugar_generates_claims_that_hold() {
        // `type` annotates its checks `#[total]`, which used to be an
        // unverified assertion and is now checked like any other.
        assert!(assemble("type Pair (int, int);").is_ok());
        assert!(assemble("enum E { A(int), B(symbol) }").is_ok());
    }

    #[test]
    fn reachability_answers_for_every_sentence_not_only_the_annotated() {
        // What `bin/rewrite` needs: the fact is available whether or not the
        // callee bothered to claim it.
        let library = assemble(
            r#"
            #[arity(1, 0)]
            sentence risky { assert }
            #[arity(1, 0)]
            sentence caller { jump risky }
            #[arity(2, 1)]
            sentence safe { add }
        "#,
        )
        .unwrap();
        let can = failure_reachability(&library);
        let of = |name: &str| {
            let idx = library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(i, _)| usize::from(i))
                .unwrap();
            can[idx]
        };
        assert!(of("risky"));
        assert!(of("caller"), "reachability propagates without any annotation");
        assert!(!of("safe"));
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
