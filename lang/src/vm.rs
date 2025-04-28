use std::{
    any,
    collections::VecDeque,
    io::{stdin, stdout, ErrorKind, Read, Write},
    os::fd::FromRawFd,
    str::from_utf8,
};

use anyhow::{bail, ensure, Context};
use thiserror::Error;
use typed_index_collections::TiSliceIndex;

use crate::{
    flat::{
        Builtin, Closure, Entry, InnerWord, Library, LoadError, Namespace2, SentenceIndex, Value,
        Word,
    },
    source::{self, FileSpan, Sources, Span},
};

#[derive(Debug)]
pub struct EvalError {
    pub location: Option<FileSpan>,
    pub inner: InnerEvalError,
}

impl EvalError {
    pub fn into_user(self, sources: &source::Sources) -> UserEvalError {
        UserEvalError {
            location: self.location.map(|s| s.location(sources)),
            inner: self.inner,
        }
    }
}

impl<'t> std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(location) = &self.location {
            write!(f, "at {:?}: ", location)?;
        } else {
            write!(f, "at <unknown location>: ")?;
        }
        write!(f, "{}", self.inner)
    }
}

impl<'t> std::error::Error for EvalError {}

#[derive(Debug)]
pub struct UserEvalError {
    pub location: Option<source::Location>,
    pub inner: InnerEvalError,
}

impl<'t> std::fmt::Display for UserEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(location) = &self.location {
            write!(f, "at {}: ", location)?;
        } else {
            write!(f, "at <unknown location>: ")?;
        }
        write!(f, "{}", self.inner)
    }
}

impl<'t> std::error::Error for UserEvalError {}

macro_rules! ebail {
    ($fmt:expr) => {
       return Err(InnerEvalError::Other(anyhow::anyhow!($fmt)))
    };

    ($fmt:expr, $($arg:tt)*) => {
        return Err(InnerEvalError::Other(anyhow::anyhow!($fmt, $($arg)*)))
    };
}

pub enum EvalResult {
    Continue,
    Call(SentenceIndex),
}

fn eval<'t>(lib: &Library, stack: &mut Stack, w: &Word) -> Result<EvalResult, EvalError> {
    inner_eval(lib, stack, &w.inner).map_err(|inner| EvalError {
        location: Some(w.span),
        inner,
    })
}

fn inner_eval(
    lib: &Library,
    stack: &mut Stack,
    w: &InnerWord,
) -> Result<EvalResult, InnerEvalError> {
    match w {
        InnerWord::Builtin(Builtin::Panic) => {
            ebail!("explicit panic")
        }
        InnerWord::Builtin(Builtin::Add) => {
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Usize(a + b));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Sub) => {
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Usize(a - b));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Prod) => {
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Usize(a * b));
            Ok(EvalResult::Continue)
        }

        InnerWord::Builtin(Builtin::Ord) => {
            let Some(Value::Char(c)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Usize(c as usize));
            Ok(EvalResult::Continue)
        }
        InnerWord::Tuple(idx) => {
            stack.tuple(*idx)?;
            Ok(EvalResult::Continue)
        }
        InnerWord::Untuple(idx) => {
            stack.untuple(*idx)?;
            Ok(EvalResult::Continue)
        }
        InnerWord::Copy(idx) => {
            stack.copy(*idx);
            Ok(EvalResult::Continue)
        }
        InnerWord::Move(idx) => {
            stack.mv(*idx);
            Ok(EvalResult::Continue)
        }
        &InnerWord::Send(idx) => {
            stack.sd(idx);
            Ok(EvalResult::Continue)
        }
        &InnerWord::Drop(idx) => {
            stack.drop(idx);
            Ok(EvalResult::Continue)
        }
        InnerWord::Push(v) => {
            stack.push(v.clone());
            Ok(EvalResult::Continue)
        }
        InnerWord::Call(sentence_idx) => Ok(EvalResult::Call(*sentence_idx)),
        InnerWord::Branch(true_case, false_case) => {
            let Some(Value::Bool(cond)) = stack.pop() else {
                ebail!("bad value")
            };
            if cond {
                Ok(EvalResult::Call(*true_case))
            } else {
                Ok(EvalResult::Call(*false_case))
            }
        }
        InnerWord::Builtin(Builtin::Eq) => {
            let Some(a) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(b) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a == b));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::AssertEq) => {
            let Some(a) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(b) = stack.pop() else {
                ebail!("bad value")
            };
            if a != b {
                ebail!("assertion failed: {:?} != {:?}", a, b)
            }
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Curry) => {
            let Some(Value::Pointer(Closure(mut closure, code))) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(val) = stack.pop() else {
                ebail!("bad value")
            };
            closure.insert(0, val);
            stack.push(Value::Pointer(Closure(closure, code)));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::And) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Bool(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a && b));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Or) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Bool(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a || b));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Not) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(!a));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Get) => {
            let ns_idx = match stack.pop() {
                Some(Value::Namespace(ns_idx)) => ns_idx,
                other => {
                    ebail!("attempted to get from non-namespace: {:?}", other)
                }
            };
            let name = match stack.pop() {
                Some(Value::Symbol(name)) => name,
                other => {
                    ebail!(
                        "attempted to index into namespace with non-symbol: {:?}",
                        other
                    )
                }
            };
            let ns = &lib.namespaces[ns_idx];

            let Some(entry) = ns.get(&name) else {
                ebail!("unknown symbol: {}", name)
            };

            stack.push(match entry {
                crate::flat::Entry::Value(v) => v.clone(),
                crate::flat::Entry::Namespace(ns) => Value::Namespace(*ns),
            });
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::SymbolCharAt) => {
            let Some(Value::Usize(idx)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Symbol(sym)) = stack.pop() else {
                ebail!("bad value")
            };

            stack.push(sym.chars().nth(idx).unwrap().into());
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::SymbolLen) => {
            let Some(Value::Symbol(sym)) = stack.pop() else {
                ebail!("bad value")
            };

            stack.push(sym.chars().count().into());
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::NsEmpty) => {
            stack.push(Value::Namespace2(Namespace2 { items: vec![] }));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::NsInsert) => {
            let Some(val) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Symbol(symbol)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Namespace2(mut ns)) = stack.pop() else {
                ebail!("bad value")
            };
            assert!(!ns.items.iter().any(|(k, v)| *k == symbol));
            ns.items.push((symbol, val));

            stack.push(Value::Namespace2(ns));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::NsRemove) => {
            let Some(Value::Symbol(symbol)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Namespace2(mut ns)) = stack.pop() else {
                ebail!("bad value")
            };
            let pos = ns.items.iter().position(|(k, v)| *k == symbol).unwrap();
            let (_, val) = ns.items.remove(pos);

            stack.push(Value::Namespace2(ns));
            stack.push(val);
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::NsGet) => {
            let Some(Value::Symbol(symbol)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Namespace2(ns)) = stack.pop() else {
                ebail!("bad value")
            };
            let pos = ns.items.iter().position(|(k, v)| *k == symbol).unwrap();
            let (_, val) = ns.items[pos].clone();

            stack.push(Value::Namespace2(ns));
            stack.push(val);
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Cons) => {
            let Some(cdr) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(car) = stack.pop() else {
                ebail!("bad value")
            };

            // ensure!(cdr.is_small(), "bad cdr type: {:?}", cdr);
            // ensure!(car.is_small(), "bad car type: {:?}", car);

            stack.push(Value::Cons(Box::new(car), Box::new(cdr)));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Snoc) => {
            let Some(Value::Cons(car, cdr)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(*car);
            stack.push(*cdr);
            Ok(EvalResult::Continue)
        }

        InnerWord::Ref(idx) => {
            stack.push(Value::Ref(stack.back_idx(*idx)?));
            Ok(EvalResult::Continue)
        }
        InnerWord::Builtin(Builtin::Deref) => {
            let Some(Value::Ref(idx)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(value) = stack.inner.get(idx) else {
                ebail!("undefined ref")
            };

            stack.push(value.clone());
            Ok(EvalResult::Continue)
        }

        InnerWord::Builtin(Builtin::Lt) => {
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("lt can only compare ints")
            };
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("lt can only compare ints")
            };
            stack.push(Value::Bool(a < b));
            Ok(EvalResult::Continue)
        }

        InnerWord::Builtin(Builtin::If) => {
            let Some(b) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(a) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Bool(cond)) = stack.pop() else {
                ebail!("bad value")
            };
            if cond {
                stack.push(a);
            } else {
                stack.push(b);
            }
            Ok(EvalResult::Continue)
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum InnerEvalError {
    #[error("Stack empty at end of sentence")]
    EmptyStack,
    #[error("Unexpected value used as control flow: {value:?}")]
    UnexpectedControlFlow { value: Value },
    #[error("Tried to exec non-closure value: {value:?}")]
    ExecNonClosure { value: Value },
    #[error("Tried to exec empty stack")]
    ExecEmptyStack,

    #[error("other error: {0}")]
    Other(#[from] anyhow::Error),
}

pub struct Vm {
    pub lib: Library,
    pub call_stack: Vec<ProgramCounter>,
    pub stack: Stack,

    pub stdin: Box<dyn Read>,
    pub stdout: Box<dyn Write>,
}

pub struct VmState {
    pub call_stack: Vec<ProgramCounter>,
    pub stack: Stack,
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

impl Vm {
    pub fn new(lib: Library) -> Self {
        Vm {
            lib,
            call_stack: vec![],
            stack: Stack::default(),
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

    pub fn with_stdout(mut self, stdout: impl Write + 'static) -> Self {
        self.stdout = Box::new(stdout);
        self
    }

    pub fn current_word(&self) -> Option<&Word> {
        let Some(pc) = self.call_stack.last() else {
            return None;
        };
        Some(&self.lib.sentences[pc.sentence_idx].words[pc.word_idx])
    }

    // pub fn jump_to(&mut self, Closure(closure, sentence_idx): Closure) {
    //     for v in closure {
    //         self.stack.push(v);
    //     }
    //     self.call_stack = ProgramCounter {
    //         sentence_idx,
    //         word_idx: 0,
    //     };
    // }

    // pub fn run_to_trap(&mut self) -> Result<(), EvalError> {
    //     while self.call_stack.sentence_idx != SentenceIndex::TRAP {
    //         self.step()?;
    //     }
    //     Ok(())
    // }

    pub fn step(&mut self) -> Result<StepResult, EvalError> {
        let pc = loop {
            let Some(pc) = self.call_stack.last_mut() else {
                return Ok(StepResult::Exit);
            };
            break pc;
        };
        let word = &self.lib.sentences[pc.sentence_idx].words[pc.word_idx];
        let res = eval(&self.lib, &mut self.stack, &word)?;
        pc.word_idx += 1;
        if pc.word_idx == self.lib.sentences[pc.sentence_idx].words.len() {
            self.call_stack.pop();
        }
        match res {
            EvalResult::Call(sentence_idx) => {
                self.call_stack.push(ProgramCounter {
                    sentence_idx,
                    word_idx: 0,
                });
            }
            EvalResult::Continue => {}
        }
        // if pc.word_idx < self.lib.sentences[pc.sentence_idx].words.len() - 1 {
        //     pc.word_idx += 1;
        // } else {
        //     let op = match self.stack.pop() {
        //         Some(Value::Symbol(op)) => op,
        //         Some(value) => {
        //             return Err(EvalError {
        //                 location: Some(word.location()),
        //                 inner: InnerEvalError::UnexpectedControlFlow { value },
        //             })
        //         }
        //         None => {
        //             return Err(EvalError {
        //                 location: Some(word.location()),
        //                 inner: InnerEvalError::EmptyStack,
        //             })
        //         }
        //     };
        //     if op != "exec" {
        //         return Err(EvalError {
        //             location: Some(word.location()),
        //             inner: InnerEvalError::UnexpectedControlFlow {
        //                 value: Value::Symbol(op),
        //             },
        //         });
        //     }

        //     let next = match self.stack.pop() {
        //         Some(Value::Pointer(next)) => next,
        //         Some(value) => {
        //             return Err(EvalError {
        //                 location: Some(word.location()),
        //                 inner: InnerEvalError::ExecNonClosure { value },
        //             })
        //         }
        //         None => {
        //             return Err(EvalError {
        //                 location: Some(word.location()),
        //                 inner: InnerEvalError::ExecEmptyStack,
        //             })
        //         }
        //     };

        //     for v in next.0 {
        //         self.stack.push(v);
        //     }

        //     self.call_stack = ProgramCounter {
        //         sentence_idx: next.1,
        //         word_idx: 0,
        //     };
        // }
        Ok(StepResult::Continue)
    }

    // pub fn trap(&mut self) -> Result<StepResult, EvalError> {
    //     self.trap_inner().map_err(|inner| EvalError {
    //         location: None,
    //         inner,
    //     })
    // }

    // fn trap_inner(&mut self) -> Result<StepResult, InnerEvalError> {
    //     let Some(Value::Symbol(symbol)) = self.stack.pop() else {
    //         ebail!("symbol not specified")
    //     };

    //     if symbol == "err" {
    //         println!("Error: {:?}", self.stack.pop());
    //         return Ok(StepResult::Exit);
    //     }

    //     if symbol != "req" {
    //         ebail!("must be req")
    //     }
    //     let Some(Value::Pointer(caller)) = self.stack.pop() else {
    //         ebail!("caller not specified")
    //     };

    //     let Some(Value::Symbol(method)) = self.stack.pop() else {
    //         ebail!("method not specified")
    //     };

    //     match method.as_str() {
    //         "stdout" => {
    //             let Some(Value::Char(c)) = self.stack.pop() else {
    //                 ebail!("char not specified")
    //             };
    //             write!(self.stdout, "{}", c);
    //             self.stack
    //                 .push(Value::Pointer(Closure(vec![], SentenceIndex::TRAP)));
    //             self.load_main();
    //             Ok(StepResult::Continue)
    //         }
    //         "stdin" => {
    //             let mut buf = [0; 1];
    //             match self.stdin.read_exact(&mut buf) {
    //                 Ok(()) => {
    //                     let nextchar = char::from_u32(buf[0] as u32).unwrap();

    //                     self.stack.push(Value::Char(nextchar));
    //                     self.stack.push(Value::Symbol("ok".to_owned()));
    //                     self.stack
    //                         .push(Value::Pointer(Closure(vec![], SentenceIndex::TRAP)));
    //                     self.load_main();
    //                 }
    //                 Err(e) if e.kind() == ErrorKind::UnexpectedEof => {
    //                     self.stack.push(Value::Symbol("eof".to_owned()));
    //                     self.stack
    //                         .push(Value::Pointer(Closure(vec![], SentenceIndex::TRAP)));
    //                     self.load_main();
    //                 }
    //                 Err(e) => panic!("unexpected io fail: {}", e),
    //             }

    //             Ok(StepResult::Continue)
    //         }
    //         "print" => {
    //             let Some(v) = self.stack.pop() else {
    //                 ebail!("value not specified")
    //             };
    //             write!(self.stdout, "{:?}\n", v);
    //             self.stack
    //                 .push(Value::Pointer(Closure(vec![], SentenceIndex::TRAP)));
    //             self.load_main();
    //             Ok(StepResult::Continue)
    //         }
    //         "halt" => Ok(StepResult::Exit),
    //         req => {
    //             ebail!("unknown method: {}", req)
    //         }
    //     }
    // }

    pub fn run(&mut self) -> Result<(), EvalError> {
        while let StepResult::Continue = self.step()? {}
        Ok(())
    }

    pub fn load_label(&mut self, label: &str) {
        assert!(self.call_stack.is_empty());
        let main = self.lib.export(label).unwrap();
        self.call_stack = vec![ProgramCounter {
            sentence_idx: main,
            word_idx: 0,
        }]
    }

    pub fn push_value(&mut self, value: Value) {
        self.stack.push(value)
    }
}

#[derive(Debug, Default, Clone)]
pub struct Stack {
    inner: Vec<Value>,
}

impl Stack {
    pub fn pop(&mut self) -> Option<Value> {
        self.inner.pop()
    }

    pub fn push(&mut self, value: Value) {
        self.inner.push(value)
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn copy(&mut self, back_idx: usize) -> Result<(), InnerEvalError> {
        let Some(v) = self.inner.iter().rev().nth(back_idx) else {
            ebail!("out of range: {}", back_idx)
        };

        self.push(v.clone());
        Ok(())
    }

    pub fn mv(&mut self, back_idx: usize) -> Result<(), InnerEvalError> {
        let val = self.inner.remove(self.back_idx(back_idx)?);
        self.inner.push(val);
        Ok(())
    }

    pub fn sd(&mut self, back_idx: usize) -> Result<(), InnerEvalError> {
        let new_idx = self.back_idx(back_idx)?;
        let Some(val) = self.inner.pop() else {
            ebail!("bad value")
        };
        if self.inner.len() < new_idx {
            ebail!("bad value")
        }
        self.inner.insert(new_idx, val);
        Ok(())
    }

    pub fn drop(&mut self, back_idx: usize) -> Result<(), InnerEvalError> {
        self.inner.remove(self.back_idx(back_idx)?);
        Ok(())
    }

    pub fn tuple(&mut self, size: usize) -> Result<(), InnerEvalError> {
        let vals = self.inner.split_off(self.inner.len() - size);
        self.push(Value::Tuple(vals));
        Ok(())
    }

    pub fn untuple(&mut self, size: usize) -> Result<(), InnerEvalError> {
        let Some(Value::Tuple(val)) = self.inner.pop() else {
            ebail!("bad value")
        };
        if val.len() != size {
            ebail!("wrong size")
        }
        self.inner.extend(val);
        Ok(())
    }

    fn back_idx(&self, back_idx: usize) -> anyhow::Result<usize> {
        self.inner
            .len()
            .checked_sub(1 + back_idx)
            .context("index out of range")
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Value> {
        self.inner.iter()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn get(&self, idx: usize) -> Option<&Value> {
        let Ok(idx) = self.back_idx(idx) else {
            return None;
        };
        self.inner.get(idx)
    }
}
