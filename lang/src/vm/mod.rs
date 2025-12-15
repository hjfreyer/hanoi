use std::io::{stdin, stdout, Read, Write};

use anyhow::{anyhow, Context};
use itertools::Itertools;

use crate::{
    bytecode::{Library, SentenceIndex, Word}, runtime::{self, Runtime}, source::{self, FileSpan}, 
};

mod stack;
mod value;

pub use stack::*;
pub use value::*;

pub struct Vm {
    pub lib: Library,
    pub call_stack: Vec<ProgramCounter>,
    pub stack: stack::Stack,

    pub runtime: Runtime,
    pub main_symbol: SentenceIndex,

    pub stdin: Box<dyn Read>,
    pub stdout: Box<dyn Write>,
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
    pub fn new(lib: Library, runtime: Runtime, main_symbol: SentenceIndex) -> Self {
        Vm {
            lib,
            call_stack: vec![],
            stack: Stack::default(),
            main_symbol,
            runtime,
            stdin: Box::new(stdin()),
            stdout: Box::new(stdout()),
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

    pub fn with_stdin(mut self, stdin: impl Read + 'static) -> Self {
        self.stdin = Box::new(stdin);
        self
    }

    pub fn _with_stdout(mut self, stdout: impl Write + 'static) -> Self {
        self.stdout = Box::new(stdout);
        self
    }

    pub fn current_word(&self) -> Option<&Word> {
        let Some(pc) = self.call_stack.last() else {
            return None;
        };
        Some(&self.lib.sentences[pc.sentence_idx].words[pc.word_idx])
    }

    pub fn jump_to(&mut self, sentence_idx: SentenceIndex) {
        self.call_stack.push(ProgramCounter {
            sentence_idx,
            word_idx: 0,
        });
    }

    // pub fn run_to_trap(&mut self) -> Result<(), EvalError> {
    //     while self.call_stack.sentence_idx != SentenceIndex::TRAP {
    //         self.step()?;
    //     }
    //     Ok(())
    // }

    pub fn init(&mut self) {
        self.stack.push(tuple![tagged![start {}], tagged![in {}]]);
        self.call_stack = vec![ProgramCounter {
            sentence_idx: self.main_symbol,
            word_idx: 0,
        }]
    }

    pub fn step(&mut self) -> Result<StepResult, EvalError> {
        let pc = loop {
            let Some(pc) = self.call_stack.last_mut() else {
                return Ok(StepResult::Exit);
            };
            break pc;
        };
        let word = &self.lib.sentences[pc.sentence_idx].words[pc.word_idx];
     
        let res = Self::eval_word(&mut self.stack, word)?;
        pc.word_idx += 1;
        if pc.word_idx == self.lib.sentences[pc.sentence_idx].words.len() {
            self.call_stack.pop();
        }
        match res {
            EvalResult::Call(sentence_idx) => {
                if !self.lib.sentences[sentence_idx].words.is_empty() {
                    self.call_stack.push(ProgramCounter {
                        sentence_idx,
                        word_idx: 0,
                    });
                }
            }
            EvalResult::Continue => {}
        }
        Ok(StepResult::Continue)
    }

    fn eval_word(stack: &mut Stack, word: &Word) -> Result<EvalResult, EvalError> {
        match word {
            Word::StackOperation(op) => {
                stack.inner_eval(*op)?;
                Ok(EvalResult::Continue)
            } 
            Word::Call(sentence_idx) => {
                Ok(EvalResult::Call(*sentence_idx))
            }
            Word::Branch(true_case, false_case) => {
                stack
                    .check_size(1)
                    .map_err(|_| EvalError::EmptyStack)?;
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
                stack
                    .check_size(1)
                    .map_err(|_| EvalError::EmptyStack)?;
                let cond: usize = 
                    stack.pop()
                    .unwrap()
                    .try_into()
                    .map_err(|e| EvalError::JumpTableInvalidIndex { source: e })?;
                if cond >= targets.len() {
                    return Err(EvalError::JumpTableIndexOutOfBounds {
                        index: cond,
                        size: targets.len(),
                    })
                } else {
                    Ok(EvalResult::Call(targets[cond]))
                }
            }
        }
    }
}
