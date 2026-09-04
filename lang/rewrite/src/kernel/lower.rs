//! A sentence, as the graph it computes.
//!
//! A [`bytecode::Sentence`] is a `Vec<Instruction>` over a stack; a
//! [`Graph`] is boxes reading values. The distance between the two is one
//! walk, and this is it: carry a stack of [`Source`]s, and let each
//! instruction take from it and put back.
//!
//! **Four instructions never build a box.** `copy` names a source twice,
//! `drop` names one nowhere, `swap` names two in the other order, and the
//! passing-through a sentence leaves implicit is the sources nobody
//! touched, still sitting where they were. None of them is an operation,
//! so none of them has a box to be — which is why `id-elim`, `swap-elim`,
//! `copy-elim` and `dead-node` are not laws that fire but things the
//! representation cannot say.
//!
//! **The stack never underflows.** [`sentence_arity`] has already worked
//! out what a sentence demands, growing that demand retroactively wherever
//! an instruction turned out to want more than the prefix had left; the
//! walk starts from the count it settled on, so by the time an instruction
//! asks for its operands they are there. Nothing here re-derives that, and
//! nothing here has a padding step: `id(k) * A` is what a stack program
//! has to write to say "and these went past untouched", and a stack of
//! sources says it by not mentioning them.
//!
//! **A block is spliced, not called.** Branch arms, `dip` bodies and the
//! shared expansions of `pick`, `roll` and a deep `drop` all get a
//! [`SentenceIndex`] because the compiler needs somewhere to put them, and
//! nothing can reach one by name. A [`NodeKind::Call`] to one would name a
//! compiler artifact and every rule wanting to look inside would have to
//! open it first, so the walk descends into the block instead, on the
//! stack it already holds.
//!
//! **A branch is a `select` per answer, and both arms run.** The condition
//! comes off the top and the *same* sources — not a copy of them — go to
//! each arm, so an operation both arms do is one box, and an arm that is
//! the value the condition tested is that value outright. Whatever each
//! answers with is paired off, answer by answer, into a `select` that
//! keeps one. The arms may demand different depths; each simply takes what
//! it takes off the top, and what the shallower one left untouched lines
//! up with what the deeper one consumed, because the compiler has already
//! refused arms whose *net* effects differ.
//!
//! Both arms being computed is the single-arm hoist of
//! [docs/totality.md](../../../../docs/totality.md), and the hoist is what
//! makes the walk honest: every prim is total and has no effect but the
//! stack, so work on the path not taken costs an answer nobody reads
//! rather than a failure.
//!
//! The walk runs one way only. A graph is *read* by [`crate::render`], as
//! a graph; it is never turned back into a list of instructions. It could
//! not be the list it came from anyway — the arms are in the graph beside
//! the `select`, scheduled like any other work, so anything reimposing a
//! stack would answer with both arms run flat and a choice at the end.

use std::collections::HashMap;
use std::fmt;

use bytecode::arity::sentence_arity;
use bytecode::{Instruction, Library, SentenceIndex};

use crate::kernel::graph::{Graph, NodeKind, Source};
use crate::kernel::prim::{Arity, Prim};

/// The name phase 4 gives a block that was written inline rather than
/// called. Nothing can reach one by name, so a call to one would name a
/// compiler artifact; the walk splices them instead.
const INLINE_BLOCK: &str = "<inline>";

/// A sentence that could not be read as a graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// A sentence whose stack effect could not be worked out. A library
    /// that compiled has none of these: inference is what refuses
    /// recursion, so a sentence with no arity never got this far.
    NoArity(SentenceIndex),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NoArity(idx) => write!(f, "sentence {:?} has no stack effect", idx),
        }
    }
}

impl std::error::Error for Error {}

/// The graph a sentence computes: one box per operation, and nothing else.
pub fn lower(library: &Library, sentence: SentenceIndex) -> Result<Graph, Error> {
    Lowering::new(library).sentence(sentence)
}

/// What a call to this sentence does to the stack: its *inferred* arity,
/// which is what the machine consumes and what a
/// [`NodeKind::Call`] carries. A wider `#[arity]` annotation
/// is a claim about the sentence, not about what a call to it does.
pub fn call_arity(library: &Library, idx: SentenceIndex) -> Result<Arity, Error> {
    let inferred = sentence_arity(library, idx).ok_or(Error::NoArity(idx))?;
    Ok(Arity::new(
        usize::try_from(inferred.inputs).expect("an inferred arity counts up from zero"),
        usize::try_from(inferred.outputs).expect("an inferred arity counts up from zero"),
    ))
}

/// One pass over a library, remembering the arities it has worked out.
///
/// The memo is not an optimization of a slow thing but of a repeated one:
/// a callee's arity is re-derived from scratch by every [`sentence_arity`]
/// call, and a sentence called ten times would pay for it ten times.
struct Lowering<'a> {
    library: &'a Library,
    arities: HashMap<SentenceIndex, Arity>,
}

impl<'a> Lowering<'a> {
    fn new(library: &'a Library) -> Self {
        Self {
            library,
            arities: HashMap::new(),
        }
    }

    /// A whole sentence as a graph, boundary and all.
    fn sentence(&mut self, idx: SentenceIndex) -> Result<Graph, Error> {
        let arity = self.arity_of(idx)?;
        let mut graph = Graph::empty(arity.inputs);
        let stack: Vec<Source> = (0..arity.inputs).map(Source::Input).collect();
        let stack = self.block(&mut graph, idx, stack)?;
        debug_assert_eq!(
            stack.len(),
            arity.outputs,
            "the walk leaves what the checker inferred"
        );
        graph.close(stack);
        Ok(graph)
    }

    /// One sentence's instructions on the stack given, answering with the
    /// stack they leave.
    ///
    /// This terminates because recursion is forbidden — `check_arities`
    /// refuses a sentence that reaches itself, so the call graph of a
    /// library that compiled is acyclic and splicing blocks bottoms out.
    fn block(
        &mut self,
        graph: &mut Graph,
        idx: SentenceIndex,
        mut stack: Vec<Source>,
    ) -> Result<Vec<Source>, Error> {
        for inst in &self.library.sentences[idx] {
            stack = self.instruction(graph, inst, stack)?;
        }
        Ok(stack)
    }

    fn instruction(
        &mut self,
        graph: &mut Graph,
        inst: &Instruction,
        mut stack: Vec<Source>,
    ) -> Result<Vec<Source>, Error> {
        Ok(match inst {
            // The four with no box to be. A value read twice is two
            // references to one source; a value read never is a source the
            // boundary stops reaching; a crossing is two names in the other
            // order.
            Instruction::Copy => {
                let top = *stack.last().expect("the checker left an operand here");
                stack.push(top);
                stack
            }
            Instruction::Drop => {
                stack.pop().expect("the checker left an operand here");
                stack
            }
            Instruction::Swap => {
                let n = stack.len();
                stack.swap(n - 1, n - 2);
                stack
            }

            Instruction::Jump(target) => self.target(graph, *target, stack)?,

            // The hidden value is the top of the stack, so the callee runs
            // on everything under it and the value goes back on top. There
            // is no second way of putting two programs together here: a
            // `dip` is which sources the callee was handed.
            Instruction::Dip(target) => {
                let hidden = stack.pop().expect("a dip hides the top of the stack");
                let mut stack = self.target(graph, *target, stack)?;
                stack.push(hidden);
                stack
            }

            // Both arms on the same sources, and a `select` per answer.
            // The `n` selects are peers: none is upstream of another, and
            // no box records that they came from one `branch`. Nothing
            // needs to — a branch means a choice per answer, so `n` choices
            // is what it *is*, and the grouping a wider box would have
            // carried is the listing's to read back off the condition.
            //
            // The stack is cut by what the **hungrier** arm demands, and
            // only that much is offered a choice. What sits below is what
            // neither arm could have reached, so it is the same value
            // whichever way the condition goes and a `select` on it would
            // be a box asking a settled question.
            Instruction::Branch(if_true, if_false) => {
                let cond = stack.pop().expect("a branch reads its condition");
                let deep = self
                    .arity_of(*if_true)?
                    .inputs
                    .max(self.arity_of(*if_false)?.inputs);
                let offered = stack.split_off(stack.len() - deep);
                let then = self.target(graph, *if_true, offered.clone())?;
                let els = self.target(graph, *if_false, offered)?;
                debug_assert_eq!(
                    then.len(),
                    els.len(),
                    "the checker refused arms whose net effects differ"
                );
                stack.extend(
                    then.into_iter()
                        .zip(els)
                        .map(|(t, e)| graph.add(NodeKind::Select, vec![cond, t, e])[0]),
                );
                stack
            }

            local => {
                let prim = Prim::from_instruction(local)
                    .expect("the instructions without a prim are matched above");
                let arity = prim.arity();
                let operands = stack.split_off(stack.len() - arity.inputs);
                stack.extend(graph.add(NodeKind::Op(prim), operands));
                stack
            }
        })
    }

    /// A called sentence: spliced in if it is a block, one `call` box if it
    /// is not.
    fn target(
        &mut self,
        graph: &mut Graph,
        idx: SentenceIndex,
        mut stack: Vec<Source>,
    ) -> Result<Vec<Source>, Error> {
        if self.library.names[idx] == INLINE_BLOCK {
            return self.block(graph, idx, stack);
        }
        let arity = self.arity_of(idx)?;
        let operands = stack.split_off(stack.len() - arity.inputs);
        stack.extend(graph.add(NodeKind::Call { target: idx, arity }, operands));
        Ok(stack)
    }

    fn arity_of(&mut self, idx: SentenceIndex) -> Result<Arity, Error> {
        if let Some(arity) = self.arities.get(&idx) {
            return Ok(*arity);
        }
        let arity = call_arity(self.library, idx)?;
        self.arities.insert(idx, arity);
        Ok(arity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::graph::Source;
    use crate::kernel::tests::corpus;
    use bytecode::assemble;

    fn sentence_named(library: &Library, name: &str) -> SentenceIndex {
        library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(idx, _)| idx)
            .unwrap_or_else(|| panic!("no sentence named {}", name))
    }

    /// The graph a sentence written inline computes, checked.
    fn graph_of(code: &str, name: &str) -> (Library, Graph) {
        let library = assemble(code).unwrap();
        let graph = lower(&library, sentence_named(&library, name)).unwrap();
        graph.check().unwrap_or_else(|e| panic!("{}\n{}", e, graph));
        (library, graph)
    }

    fn kinds(graph: &Graph) -> Vec<NodeKind> {
        graph.live().map(|(_, kind)| kind.clone()).collect()
    }

    #[test]
    fn one_box_per_operation_and_nothing_for_the_rest() {
        // Three instructions, three boxes — and the fourth value the `add`
        // reads is the sentence's own input, which is no box either.
        let (_, graph) = graph_of("sentence probe { push 1 push 2 add }", "probe");
        assert_eq!(graph.live_count(), 3, "\n{}", graph);

        // A value said twice is said once: the two literals are one box,
        // read twice, before anything has had a chance to rewrite.
        let (_, shared) = graph_of("sentence probe { push 1 push 1 add }", "probe");
        assert_eq!(shared.live_count(), 2, "\n{}", shared);
        let (lit, _) = shared
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(_))))
            .expect("the literal");
        assert_eq!(
            shared.sinks(Source::Port { node: lit, port: 0 }).len(),
            2,
            "one literal, read twice:\n{}",
            shared
        );
    }

    #[test]
    fn the_four_that_are_not_boxes_build_nothing() {
        // `copy` names a source twice, `drop` names one nowhere, `swap`
        // names two in the other order — and a sentence of nothing but
        // those has no box in it at all.
        let (_, graph) = graph_of("sentence probe { copy drop 0 swap }", "probe");
        assert_eq!(graph.live_count(), 0, "\n{}", graph);
        assert_eq!(graph.arity(), Arity::new(2, 2));
        // Swapped: the boundary leaves its inputs in the other order.
        assert_eq!(
            graph.outputs(),
            [Source::Input(1), Source::Input(0)],
            "\n{}",
            graph
        );
    }

    #[test]
    fn a_dip_is_which_sources_the_callee_was_handed() {
        // `dip { add }` adds the two *under* the top, and the hidden value
        // goes back on top. No box records that it was hidden: the `add`
        // simply never read it.
        let (_, graph) = graph_of("sentence probe { dip { add } }", "probe");
        assert_eq!(kinds(&graph), vec![NodeKind::Op(Prim::Add)]);
        let (add, _) = graph.live().next().expect("the add");
        assert_eq!(graph.sources(add), [Source::Input(0), Source::Input(1)]);
        assert_eq!(
            graph.outputs(),
            [Source::Port { node: add, port: 0 }, Source::Input(2)],
            "the hidden value is back on top"
        );

        // Depth is nesting, since the instruction set has no width — and
        // it is still one box, three values further down.
        let (_, deep) = graph_of("sentence probe { dip 3 { add } }", "probe");
        assert_eq!(kinds(&deep), vec![NodeKind::Op(Prim::Add)]);
        assert_eq!(deep.arity(), Arity::new(5, 4));
    }

    #[test]
    fn a_named_call_stays_closed_and_a_block_is_spliced() {
        // `helper` is reachable by name, so each use is a `call` box left
        // shut. The `dip` body is not: nothing can name one, so its
        // instructions are walked here and no box records that it was a
        // frame.
        let (library, graph) = graph_of(
            r#"
            sentence helper { add }
            sentence probe { jump crate::helper dip { jump crate::helper } }
        "#,
            "probe",
        );
        let call = NodeKind::Call {
            target: sentence_named(&library, "helper"),
            arity: Arity::new(2, 1),
        };
        assert_eq!(
            kinds(&graph),
            vec![call.clone(), call],
            "two calls, on different operands, and no box for the dip:\n{}",
            graph
        );

        // And a call whose answer is thrown away is a box the boundary
        // stops reaching, which is the whole of what discarding means: the
        // same sentence with the second answer dropped has one live call.
        let (_, dropped) = graph_of(
            r#"
            sentence helper { add }
            sentence probe { jump crate::helper dip { jump crate::helper } dip { drop 0 } }
        "#,
            "probe",
        );
        assert_eq!(dropped.live_count(), 1, "\n{}", dropped);
    }

    #[test]
    fn a_reach_expands_into_the_frames_it_compiles_to() {
        // `pick 1` is `dip { copy } ; swap`, and neither half is a box:
        // the graph is the two inputs with the deeper one said twice.
        let (_, graph) = graph_of("sentence probe { pick 1 }", "probe");
        assert_eq!(graph.live_count(), 0, "\n{}", graph);
        assert_eq!(
            graph.outputs(),
            [Source::Input(0), Source::Input(1), Source::Input(0)],
            "\n{}",
            graph
        );
    }

    #[test]
    fn a_branch_is_its_arms_and_a_select_per_answer() {
        // The arms are not inside anything: the `then` arm's boxes sit in
        // this graph beside the `select` that picks between the answers.
        // `push 2` is one box, written once and read by both the `add` and
        // the `else` block.
        let (_, graph) = graph_of(
            "sentence probe { branch { push 1 push 2 add } { push 2 } }",
            "probe",
        );
        assert_eq!(graph.live_count(), 4, "\n{}", graph);

        let (id, _) = graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Select))
            .expect("the branch ends in a select");
        let inputs = graph.sources(id).to_vec();
        assert_eq!(inputs.len(), 3);
        assert_eq!(
            inputs[0],
            Source::Input(0),
            "the condition is the sentence's own input"
        );
        assert!(
            matches!(
                (inputs[1], inputs[2]),
                (Source::Port { .. }, Source::Port { .. })
            ),
            "each block is an arm's answer"
        );
    }

    #[test]
    fn only_what_an_arm_could_reach_is_offered_a_choice() {
        // The arms take one value each and leave one, so the branch is
        // offered the top value alone. The two beneath it are the same
        // whichever way the condition goes, and a `select` on one would be
        // a box asking a settled question — so there is exactly one.
        let (_, graph) = graph_of(
            "sentence probe { dip 2 { branch { not } { as_bool } } }",
            "probe",
        );
        let selects = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .count();
        assert_eq!(selects, 1, "one answer, one choice:\n{}", graph);
        assert_eq!(
            graph.outputs()[1..],
            [Source::Input(2), Source::Input(3)],
            "what the dip hid is back on top, untouched and unchosen:\n{}",
            graph
        );
    }

    #[test]
    fn the_hungrier_arm_sets_how_deep_the_branch_reaches() {
        // The `then` arm reads two values, the `else` arm one. Both are
        // offered two, and what the shallower one left untouched lines up
        // with what the deeper one consumed — the branch leaves one value
        // either way.
        let (_, graph) = graph_of("sentence probe { branch { add } { drop 0 } }", "probe");
        assert_eq!(
            graph.arity(),
            Arity::new(3, 1),
            "two operands and the condition:\n{}",
            graph
        );
        let selects = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select))
            .count();
        assert_eq!(selects, 1, "\n{}", graph);
    }

    /// Every sentence the integration suite compiles, lowered.
    ///
    /// A smoke test rather than a proof: it says that lowering survives
    /// real programs and agrees with the arity checker about all of them.
    #[test]
    fn the_whole_corpus_lowers() {
        let (library, graphs) = corpus();
        assert!(graphs.len() > 100, "the corpus should be a real one");
        for (idx, graph) in graphs {
            graph
                .check()
                .unwrap_or_else(|e| panic!("sentence {}: {}\n{}", library.names[idx], e, graph));
            assert_eq!(
                graph.arity(),
                call_arity(&library, idx).unwrap(),
                "sentence {} is not the shape the checker inferred",
                library.names[idx]
            );
        }
    }

    #[test]
    fn a_lowered_sentence_has_the_arity_the_checker_inferred() {
        let library = assemble(
            r#"
            sentence helper { add drop 0 }
            sentence probe {
                push 1
                copy
                jump crate::helper
                dip 2 { swap }
                // Both arms leave one more than they take, but the else arm
                // asks for a value where the then arm asks for none, so the
                // branch reaches as deep as the hungrier one.
                branch { push 1 } { copy }
            }
        "#,
        )
        .unwrap();
        for (idx, _) in library.sentences.iter_enumerated() {
            let graph = lower(&library, idx).unwrap();
            graph.check().unwrap();
            assert_eq!(
                graph.arity(),
                call_arity(&library, idx).unwrap(),
                "sentence {:?} ({})",
                idx,
                library.names[idx]
            );
        }
    }
}
