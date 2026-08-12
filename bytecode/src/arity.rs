use crate::library::{Annotation, Arity, Library, SentenceIndex};
use crate::opcode::Instruction;
use crate::source::Error;
use std::collections::{HashMap, HashSet};

/// Checks whether all sentences in the library obey their declared arity,
/// and populates the instruction_arities field in Library.
pub fn check_arities(library: &mut Library) -> Result<(), String> {
    check_par_arms(library)?;

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
                    Arity::Normal {
                        inputs: inferred_n,
                        outputs: inferred_m,
                    } => {
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

/// What a `par` arm takes off the stack: the number the cut is made by.
///
/// Unlike [`sentence_arity`] this does not give up the moment it sees a
/// `#[recursive]` marker. A `par` arm is an inline block, and an inline block
/// inherits that marker from the sentence that wrote it whether or not the
/// block itself recurses — so the arms of `par { add } { drop 0 }` inside a
/// recursive sentence are wearing a marker that is not about them. Inference is
/// tried first and answers for those; a declaration answers where inference
/// cannot; an arm that really does recurse and declares nothing has no answer
/// at all, and [`check_par_arms`] refuses it.
///
/// Public because the VM asks the same question for the same reason: the cut
/// has to be the one the checker signed off on.
pub fn arm_arity(library: &Library, s_idx: SentenceIndex) -> Option<Arity> {
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
    .or_else(|| declared_arity(library, s_idx))
}

/// Every `par` arm's arity must be knowable, because it is the cut.
///
/// A `par` decides how much stack each arm gets from the arm's own arity, so an
/// arm whose arity nobody can work out is a cut nobody can make. Everywhere
/// else an unknown arity only costs precision; here it costs the instruction
/// its meaning.
///
/// Swept over **every** sentence, `#[recursive]` ones included. Those are the
/// only place the problem can survive: inference skips them, so a `par` inside
/// one is never looked at by the pass below, and without this the failure would
/// wait until the machine tried to run it.
fn check_par_arms(library: &Library) -> Result<(), String> {
    for (s_idx, sentence) in library.sentences.iter_enumerated() {
        for inst in sentence {
            let Instruction::Par(arms) = inst else {
                continue;
            };
            for arm in arms {
                if arm_arity(library, *arm).is_none() {
                    return Err(format!(
                        "Sentence '{}' runs a `par` over '{}', whose arity is not knowable, \
                         so there is no way to say how much stack that arm gets. \
                         A `par` arm may not recurse without saying what it takes and leaves.",
                        library.names[s_idx], library.names[*arm]
                    ));
                }
            }
        }
    }
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
        Instruction::Par(arms) => arms.clone(),
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
            if sentence
                .iter()
                .flat_map(callees)
                .any(|c| can[usize::from(c)])
            {
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
/// The preconditions the rewriter's equations are stated under — non-recursive,
/// and unable to fail — are deliberately *not* checked here. They are
/// conditions on provability rather than on well-formedness, and asking for
/// them in the compiler would tie the language to a particular rule set.
/// `bin/prove` asks, and refuses in the same words `rewrite` does.
pub fn check_identities(library: &Library) -> Result<(), Error> {
    for identity in &library.identities {
        let effect = |side: SentenceIndex, which: &str| -> Result<(i64, i64), Error> {
            match sentence_arity(library, side) {
                Some(Arity::Normal { inputs, outputs }) => Ok((inputs, outputs)),
                // A side that always fails cannot stand in for one that does
                // not, and one whose arity is unknowable says nothing at all.
                other => Err(Error::at(
                    format!(
                        "identity `{}`: the {} side has no stack effect",
                        identity.name, which
                    ),
                    identity.span,
                )
                .with_help(match other {
                    Some(Arity::Panic { .. }) => {
                        "it always fails, so there is nothing for the other side to equal"
                    }
                    _ => "its arity could not be inferred; give it an `#[arity(n, m)]`",
                })),
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
        return Err(format!(
            "Recursion/cycle detected at sentence index {:?} ({})",
            s_idx, name
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

/// Every sentence's *inferred* arity, in one memoized sweep of the library.
///
/// [`sentence_arity`] answers for one sentence and starts from nothing each
/// time, which is quadratic when the question is asked about all of them —
/// which is exactly what [`crate::balance`] asks, once per round.
///
/// A sentence whose arity inference cannot settle is simply absent: a
/// `#[recursive]` one, which inference skips by construction, and one whose
/// inference failed. **Recursive sentences are left out rather than falling
/// back to their `#[arity]`**, which is the difference from `sentence_arity`
/// and is deliberate: a caller of one is an error that [`check_arities`]
/// reports against the sentence the user wrote, and `balance` inserting a
/// wrapper first would move that error onto a sentence they did not write.
pub fn inferred_arities(library: &Library) -> HashMap<SentenceIndex, Arity> {
    let mut memo = HashMap::new();
    let mut instruction_arities = HashMap::new();
    for s_idx_raw in 0..library.sentences.len() {
        let s_idx = SentenceIndex::from(s_idx_raw);
        if is_recursive(s_idx, library) {
            continue;
        }
        let mut in_progress = HashSet::new();
        // An error here is a cycle or a call into one, and `check_arities`
        // reports it properly a moment later; what matters here is that the
        // sentences that *do* have an arity are in the map.
        let _ = get_or_infer_arity(
            s_idx,
            library,
            &mut memo,
            &mut in_progress,
            &mut instruction_arities,
        );
    }
    memo
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
        Instruction::AssertEqual => (2, 0),
        Instruction::Tuple(n) => (*n as i64, 1),
        // The identity's whole purpose: a demand for stack that nothing
        // consumes, so that a narrower program can be padded up to a wider one.
        Instruction::Id(n) => (*n as i64, *n as i64),
        Instruction::Panic
        | Instruction::Dip(..)
        | Instruction::Branch(..)
        | Instruction::Par(..) => return None,
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
                    Arity::Panic {
                        inputs: initial_req,
                    }
                };
                let n = sentence_arity.inputs();
                let mut arities: Vec<Arity> = depths
                    .into_iter()
                    .map(|d| Arity::Normal {
                        inputs: n,
                        outputs: d,
                    })
                    .collect();
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
                let target_arity =
                    get_or_infer_arity(*target, library, memo, in_progress, instruction_arities)?;
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
                    let sentence_arity = Arity::Panic {
                        inputs: initial_req,
                    };
                    let n = sentence_arity.inputs();
                    let arities = depths
                        .into_iter()
                        .map(|d| Arity::Normal {
                            inputs: n,
                            outputs: d,
                        })
                        .collect();
                    return Ok((sentence_arity, arities));
                }
            }
            Instruction::Par(arms) => {
                // Each arm gets its own window, so the arities add: the par
                // asks for what all of them together ask for, and leaves what
                // all of them together leave. Nothing here has to reason about
                // *where* the cuts fall, which is the point of the instruction.
                let mut inputs = 0i64;
                let mut outputs = 0i64;
                let mut panics = false;
                for arm in arms {
                    if is_recursive(*arm, library) {
                        return Err(format!(
                            "Sentence '{}' calls recursive sentence '{}' but is not annotated with #[recursive]",
                            library.names[s_idx], library.names[*arm]
                        ));
                    }
                    let arm_arity =
                        get_or_infer_arity(*arm, library, memo, in_progress, instruction_arities)?;
                    inputs += arm_arity.inputs();
                    match arm_arity {
                        // An arm that always fails takes the whole `par` with
                        // it — the arms run side by side, not one after the
                        // other, so there is no "after" for the rest to reach.
                        Arity::Panic { .. } => panics = true,
                        Arity::Normal { outputs: m, .. } => outputs += m,
                    }
                }

                if current_size < inputs {
                    initial_req += inputs - current_size;
                    current_size = inputs;
                }
                if panics {
                    let sentence_arity = Arity::Panic {
                        inputs: initial_req,
                    };
                    let n = sentence_arity.inputs();
                    let arities = depths
                        .into_iter()
                        .map(|d| Arity::Normal {
                            inputs: n,
                            outputs: d,
                        })
                        .collect();
                    return Ok((sentence_arity, arities));
                }
                current_size = current_size - inputs + outputs;
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

                let arity_then =
                    get_or_infer_arity(*then_t, library, memo, in_progress, instruction_arities)?;
                let arity_else =
                    get_or_infer_arity(*else_t, library, memo, in_progress, instruction_arities)?;

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
                    let sentence_arity = Arity::Panic {
                        inputs: initial_req,
                    };
                    let n = sentence_arity.inputs();
                    let arities = depths
                        .into_iter()
                        .map(|d| Arity::Normal {
                            inputs: n,
                            outputs: d,
                        })
                        .collect();
                    return Ok((sentence_arity, arities));
                }
            }
            // Everything else has a local effect, taken from the shared table.
            // A requirement discovered here grows the sentence's input count
            // retroactively, which is why `depths` records the size *before*
            // the growth rather than the true stack depth.
            local => {
                let (n, m) = op_arity(local).expect("Panic, Dip and Branch are handled above");
                if current_size < n {
                    initial_req += n - current_size;
                    current_size = n;
                }
                current_size = current_size - n + m;
            }
        }
    }

    let sentence_arity = Arity::Normal {
        inputs: initial_req,
        outputs: current_size,
    };
    let n = sentence_arity.inputs();
    let arities = depths
        .into_iter()
        .map(|d| Arity::Normal {
            inputs: n,
            outputs: d,
        })
        .collect();
    Ok((sentence_arity, arities))
}

/// The arity of a branch, from two arms that must already agree on it.
///
/// **Both arms must have the same arity, not merely the same net change.** The
/// two are alternatives for one position in the program, so anything that
/// composes with the branch composes with each arm; an arm that asked for less
/// than its sibling would be a program whose demand on the stack depended on a
/// value. [`crate::balance`] is what makes this hold without the user writing
/// it out: it pads the narrower arm with `par { id k } { arm }` before this
/// ever runs, so by the time inference gets here the widths already match.
///
/// A `panic` arm still constrains only its input count, since it has no outputs
/// to agree about — an arm that does not return says nothing about what the
/// branch leaves. Its input count is padded like any other.
fn combine_branch_arities(then: Arity, el: Arity) -> Result<Arity, String> {
    let (n_then, n_else) = (then.inputs(), el.inputs());
    if n_then != n_else {
        // Unreachable for anything `balance` could reach — it pads exactly this
        // gap — so getting here means an arm's arity was not knowable then.
        return Err(format!(
            "then requires {} inputs, else requires {}",
            n_then, n_else
        ));
    }
    match (then, el) {
        (Arity::Panic { inputs }, Arity::Panic { .. }) => Ok(Arity::Panic { inputs }),
        (Arity::Panic { .. }, normal) | (normal, Arity::Panic { .. }) => Ok(normal),
        (
            Arity::Normal {
                inputs,
                outputs: m_then,
            },
            Arity::Normal {
                outputs: m_else, ..
            },
        ) => {
            if m_then != m_else {
                return Err(format!(
                    "then has net change {}, else has net change {}",
                    m_then - inputs,
                    m_else - inputs
                ));
            }
            Ok(Arity::Normal {
                inputs,
                outputs: m_then,
            })
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
        // Two operands in, the sum and its success flag out.
        let got = arity_of("sentence probe { add }", "probe");
        assert_eq!(
            got,
            Some(Arity::Normal {
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
            Some(Arity::Normal {
                inputs: 2,
                outputs: 2
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
    // `id` and `par`
    // -----------------------------------------------------------------------

    #[test]
    fn the_identity_asks_for_what_it_leaves() {
        for width in 0..4 {
            assert_eq!(
                arity_of(&format!("sentence probe {{ id {} }}", width), "probe"),
                Some(Arity::Normal {
                    inputs: width,
                    outputs: width
                })
            );
        }
    }

    #[test]
    fn the_identity_is_a_demand_a_body_cannot_otherwise_state() {
        // The whole reason it exists: `id` is the only way to make a sentence
        // require values it does not touch, which is what padding needs.
        let got = arity_of("sentence probe { id 3 push 1 }", "probe");
        assert_eq!(
            got,
            Some(Arity::Normal {
                inputs: 3,
                outputs: 4
            })
        );
    }

    #[test]
    fn a_par_adds_up_its_arms() {
        // Each arm has its own window, so nothing here reasons about where the
        // cuts fall — the arities simply add.
        let got = arity_of("sentence probe { par { add } { untuple 2 } }", "probe");
        assert_eq!(
            got,
            Some(Arity::Normal {
                inputs: 3,
                outputs: 5
            })
        );
    }

    #[test]
    fn a_dip_is_a_par_with_a_trailing_identity() {
        // The equivalence the design turns on, as an equation between arities.
        for depth in 0..4 {
            let dipped = arity_of(
                &format!("sentence probe {{ dip {} {{ add }} }}", depth),
                "probe",
            );
            let paired = arity_of(
                &format!("sentence probe {{ par {{ add }} {{ id {} }} }}", depth),
                "probe",
            );
            assert_eq!(dipped, paired, "at depth {}", depth);
        }
    }

    #[test]
    fn an_arm_that_always_fails_takes_the_whole_par_with_it() {
        // The arms run side by side rather than one after another, so there is
        // no "after" for the surviving arms to reach — but the failing arm
        // still asks for its window.
        let got = arity_of("sentence probe { par { add } { panic } }", "probe");
        assert_eq!(got, Some(Arity::Panic { inputs: 2 }));
    }

    #[test]
    fn a_par_arm_counts_towards_reachable_failure() {
        // `#[total]` is a claim about everything a sentence can reach, and an
        // arm is reachable.
        let msg = totality_error("#[total] sentence claims { par { drop 0 } { assert } }");
        assert!(msg.contains("#[total]"), "{}", msg);
        assert!(msg.contains("assert"), "{}", msg);
    }

    #[test]
    fn a_par_arm_must_have_a_knowable_arity() {
        // The one thing that is fatal rather than merely imprecise: the arity
        // *is* the cut. A `#[recursive]` sentence is where it can hide, since
        // inference skips those entirely and nothing else would look.
        for code in [
            "#[recursive] sentence loops { par { jump loops } }",
            "#[recursive] #[arity(1, 1)] sentence loops { par { jump loops } }",
        ] {
            let err = assemble(code).unwrap_err();
            assert!(err.contains("arity is not knowable"), "{}", err);
            assert!(err.contains("may not recurse"), "{}", err);
        }
    }

    #[test]
    fn an_ordinary_par_inside_a_recursive_sentence_is_fine() {
        // An inline block wears the `#[recursive]` marker of whoever wrote it,
        // which says nothing about the block. These arms are ordinary and are
        // inferred as such — refusing them would make `par` unusable inside
        // every loop in a program.
        assert!(
            assemble(
                r#"
            #[recursive]
            #[arity(3, 3)]
            sentence loops {
                par { add } { drop 0 push 1 }
                pick 0 is_int branch { } { jump loops }
            }
        "#
            )
            .is_ok()
        );
    }

    #[test]
    fn a_par_needs_at_least_one_arm() {
        // Otherwise `par add` would parse as a zero-arm `par` followed by an
        // `add`, which is a silent misreading of a typo.
        let err = assemble("sentence probe { par add }").unwrap_err();
        assert!(err.contains("the first arm of the `par`"), "{}", err);
        assert!(err.contains("par { jump a } { jump b }"), "{}", err);
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
        assert!(
            msg.contains("middle") && msg.contains("deep"),
            "route: {}",
            msg
        );
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
            assert!(
                msg.contains("assert"),
                "should name the instruction: {}",
                msg
            );
        }
    }

    #[test]
    fn ordinary_total_code_satisfies_the_claim() {
        // Nothing here can fail, the fallible instructions included: they
        // report rather than raise.
        assert!(
            assemble(
                r#"
            #[total]
            #[arity(2, 2)]
            sentence arith { add }
            #[total]
            #[arity(1, 3)]
            sentence apart { untuple 2 }
            #[total]
            #[arity(2, 2)]
            sentence caller { jump arith }
            #[total]
            #[arity(1, 1)]
            sentence chooses { pick 0 is_int branch { drop 0 push 1 } { drop 0 push 2 } }
        "#
            )
            .is_ok()
        );
    }

    #[test]
    fn a_cycle_that_never_fails_is_total() {
        // Reachability, not a fixpoint over arities: a loop with no failing
        // instruction anywhere in it satisfies the claim.
        assert!(
            assemble(
                r#"
            #[total]
            #[recursive]
            #[arity(1, 1)]
            sentence loops { pick 0 is_int branch { } { jump loops } }
        "#
            )
            .is_ok()
        );
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
            #[arity(2, 2)]
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
        assert!(
            of("caller"),
            "reachability propagates without any annotation"
        );
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
