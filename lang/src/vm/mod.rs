use crate::bytecode::{Library, SentenceIndex, Word};

mod stack;
mod value;

pub use stack::*;
pub use value::*;

pub struct Vm {
    pub lib: Library,
    pub call_stack: Vec<ProgramCounter>,
    pub stack: stack::Stack,
    pub main_symbol: SentenceIndex,
}

pub struct VmState {
    pub call_stack: Vec<ProgramCounter>,
    pub stack: stack::Stack,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProgramCounter {
    pub sentence_idx: SentenceIndex,
    pub word_idx: usize,
}

pub enum StepResult {
    Exit,
    Continue,
}

enum EvalResult {
    Continue,
    Call(SentenceIndex),
}

impl Vm {
    pub fn new(lib: Library, main_symbol: SentenceIndex) -> Self {
        Vm {
            lib,
            call_stack: vec![],
            stack: Stack::default(),
            main_symbol,
        }
    }

    pub fn save_state(&self) -> VmState {
        VmState {
            call_stack: self.call_stack.clone(),
            stack: self.stack.clone(),
        }
    }

    pub fn restore_state(&mut self, state: VmState) {
        self.call_stack = state.call_stack;
        self.stack = state.stack;
    }

    fn jump_to(&mut self, sentence_idx: SentenceIndex) {
        self.call_stack.push(ProgramCounter {
            sentence_idx,
            word_idx: 0,
        });
    }

    pub fn run_sentence(&mut self) -> Result<(), EvalError> {
        self.reset_call_stack();
        while let StepResult::Continue = self.step()? {}
        Ok(())
    }

    pub fn reset_call_stack(&mut self) {
        if !self.call_stack.is_empty() {
            panic!("call stack is not empty");
        }
        self.jump_to(self.main_symbol);
    }

    pub fn step(&mut self) -> Result<StepResult, EvalError> {
        let Some(pc) = self.call_stack.last_mut() else {
            return Ok(StepResult::Exit);
        };
        let word = &self.lib.sentences[pc.sentence_idx].words[pc.word_idx];
        pc.word_idx += 1;

        let res = Self::eval_word(&mut self.stack, word)?;
        match res {
            EvalResult::Call(sentence_idx) => {
                self.jump_to(sentence_idx);
            }
            EvalResult::Continue => {
                // We already advanced the PC above, but now we ensure that
                // it points to a real word, if there's any left.
                while let Some(pc) = self.call_stack.last()
                    && pc.word_idx == self.lib.sentences[pc.sentence_idx].words.len()
                {
                    self.call_stack.pop();
                }
            }
        }
        Ok(StepResult::Continue)
    }

    fn eval_word(stack: &mut Stack, word: &Word) -> Result<EvalResult, EvalError> {
        match word {
            Word::StackOperation(op) => {
                stack.inner_eval(*op)?;
                Ok(EvalResult::Continue)
            }
            Word::Call(sentence_idx) => Ok(EvalResult::Call(*sentence_idx)),
            Word::Branch(true_case, false_case) => {
                stack.check_size(1).map_err(|_| EvalError::EmptyStack)?;
                let cond: bool = stack
                    .pop()
                    .unwrap()
                    .try_into()
                    .map_err(|e| EvalError::InvalidBranchCondition { source: e })?;
                if cond {
                    Ok(EvalResult::Call(*true_case))
                } else {
                    Ok(EvalResult::Call(*false_case))
                }
            }
            Word::JumpTable(targets) => {
                stack.check_size(1).map_err(|_| EvalError::EmptyStack)?;
                let cond: usize = stack
                    .pop()
                    .unwrap()
                    .try_into()
                    .map_err(|e| EvalError::JumpTableInvalidIndex { source: e })?;
                if cond >= targets.len() {
                    return Err(EvalError::JumpTableIndexOutOfBounds {
                        index: cond,
                        size: targets.len(),
                    });
                } else {
                    Ok(EvalResult::Call(targets[cond]))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use typed_index_collections::TiVec;

    use crate::bytecode::{Builtin, PrimitiveValue, Sentence, StackOperation};

    use super::*;

    #[test]
    fn test_run_sentence() {
        let lib = Library {
            debuginfo: Default::default(),
            symbols: vec![].into(),
            sentences: vec![Sentence {
                words: vec![
                    Word::StackOperation(StackOperation::Push(PrimitiveValue::Usize(1))),
                    Word::StackOperation(StackOperation::Builtin(Builtin::Add)),
                ],
            }]
            .into(),
            exports: BTreeMap::new(),
        };
        let mut vm = Vm::new(lib, SentenceIndex::from(0));
        vm.stack.push(Value::Usize(1));
        vm.run_sentence().unwrap();
        assert_eq!(vm.stack.get(0).unwrap(), &Value::Usize(2));
        vm.run_sentence().unwrap();
        assert_eq!(vm.stack.get(0).unwrap(), &Value::Usize(3));
    }

    #[test]
    fn test_run_sentence_call() {
        let lib = Library {
            debuginfo: Default::default(),
            symbols: vec![].into(),
            sentences: vec![
                Sentence {
                    words: vec![
                        Word::StackOperation(StackOperation::Push(PrimitiveValue::Usize(1))),
                        Word::Call(SentenceIndex::from(1)),
                    ],
                },
                Sentence {
                    words: vec![
                        Word::StackOperation(StackOperation::Drop(0)),
                        Word::StackOperation(StackOperation::Push(PrimitiveValue::Usize(2))),
                        Word::StackOperation(StackOperation::Builtin(Builtin::Add)),
                    ],
                },
            ]
            .into(),
            exports: BTreeMap::new(),
        };
        let mut vm = Vm::new(lib, SentenceIndex::from(0));
        vm.stack.push(Value::Usize(1));
        vm.run_sentence().unwrap();
        assert_eq!(vm.stack.get(0).unwrap(), &Value::Usize(3));
    }
}
