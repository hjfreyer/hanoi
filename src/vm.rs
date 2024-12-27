use std::{any, collections::VecDeque};

use anyhow::{bail, ensure, Context};
use pest::Span;
use thiserror::Error;
use typed_index_collections::TiSliceIndex;

use crate::{
    ast,
    flat::{
        Builtin, Closure, Entry, InnerWord, Library, LoadError, Namespace2, SentenceIndex,
        SourceLocation, Value, Word,
    },
};

#[derive(Debug)]
pub struct EvalError {
    pub location: Option<SourceLocation>,
    pub inner: InnerEvalError,
}

impl<'t> std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(location) = &self.location {
            write!(f, "at {}: ", location)?;
        } else {
            write!(f, "at <unknown location>: ")?;
        }
        write!(f, "{}", self.inner)
    }
}

impl<'t> std::error::Error for EvalError {}

macro_rules! ebail {
    ($fmt:expr) => {
       return Err(InnerEvalError::Other(anyhow::anyhow!($fmt)))
    };

    ($fmt:expr, $($arg:tt)*) => {
        return Err(InnerEvalError::Other(anyhow::anyhow!($fmt, $($arg)*)))
    };
}

fn eval<'t>(lib: &Library, stack: &mut Stack, w: &Word<'t>) -> Result<(), EvalError> {
    inner_eval(lib, stack, &w.inner).map_err(|inner| EvalError {
        location: Some(w.location()),
        inner,
    })
}

fn inner_eval(lib: &Library, stack: &mut Stack, w: &InnerWord) -> Result<(), InnerEvalError> {
    match w {
        InnerWord::Builtin(Builtin::Add) => {
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Usize(a + b));
            Ok(())
        }
        InnerWord::Tuple(idx) => todo!(),
        InnerWord::Untuple(idx) => todo!(),
        InnerWord::Copy(idx) => stack.copy(*idx),
        InnerWord::Move(idx) => stack.mv(*idx),
        &InnerWord::Send(idx) => stack.sd(idx),
        &InnerWord::Drop(idx) => stack.drop(idx),
        InnerWord::Push(v) => {
            stack.push(v.clone());
            Ok(())
        }
        InnerWord::Builtin(Builtin::Eq) => {
            let Some(a) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(b) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a == b));
            Ok(())
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
            Ok(())
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
            Ok(())
        }
        InnerWord::Builtin(Builtin::And) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Bool(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a && b));
            Ok(())
        }
        InnerWord::Builtin(Builtin::Or) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Bool(b)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(a || b));
            Ok(())
        }
        InnerWord::Builtin(Builtin::Not) => {
            let Some(Value::Bool(a)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(Value::Bool(!a));
            Ok(())
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
            Ok(())
        }
        InnerWord::Builtin(Builtin::SymbolCharAt) => {
            let Some(Value::Usize(idx)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(Value::Symbol(sym)) = stack.pop() else {
                ebail!("bad value")
            };

            stack.push(sym.chars().nth(idx).unwrap().into());
            Ok(())
        }
        InnerWord::Builtin(Builtin::SymbolLen) => {
            let Some(Value::Symbol(sym)) = stack.pop() else {
                ebail!("bad value")
            };

            stack.push(sym.chars().count().into());
            Ok(())
        }
        InnerWord::Builtin(Builtin::NsEmpty) => {
            stack.push(Value::Namespace2(Namespace2 { items: vec![] }));
            Ok(())
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
            Ok(())
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
            Ok(())
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
            Ok(())
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
            Ok(())
        }
        InnerWord::Builtin(Builtin::Snoc) => {
            let Some(Value::Cons(car, cdr)) = stack.pop() else {
                ebail!("bad value")
            };
            stack.push(*car);
            stack.push(*cdr);
            Ok(())
        }

        InnerWord::Ref(idx) => {
            stack.push(Value::Ref(stack.back_idx(*idx)?));
            Ok(())
        }
        InnerWord::Builtin(Builtin::Deref) => {
            let Some(Value::Ref(idx)) = stack.pop() else {
                ebail!("bad value")
            };
            let Some(value) = stack.inner.get(idx) else {
                ebail!("undefined ref")
            };

            stack.push(value.clone());
            Ok(())
        }

        InnerWord::Builtin(Builtin::Lt) => {
            let Some(Value::Usize(b)) = stack.pop() else {
                ebail!("lt can only compare ints")
            };
            let Some(Value::Usize(a)) = stack.pop() else {
                ebail!("lt can only compare ints")
            };
            stack.push(Value::Bool(a < b));
            Ok(())
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
            Ok(())
        }

        InnerWord::Builtin(Builtin::Stash) => stack.stash(),
        InnerWord::Builtin(Builtin::Unstash) => stack.unstash(),
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

fn control_flow<'t>(lib: &Library<'t>, stack: &mut Stack) -> Result<Closure, InnerEvalError> {
    let op = match stack.pop() {
        Some(Value::Symbol(op)) => op,
        Some(value) => return Err(InnerEvalError::UnexpectedControlFlow { value }),
        None => return Err(InnerEvalError::EmptyStack),
    };
    match op.as_str() {
        "exec" => {
            let next = match stack.pop() {
                Some(Value::Pointer(next)) => next,
                Some(value) => return Err(InnerEvalError::ExecNonClosure { value }),
                None => return Err(InnerEvalError::ExecEmptyStack),
            };

            Ok(next)
        }
        unk => Err(InnerEvalError::UnexpectedControlFlow {
            value: Value::Symbol(unk.to_owned()),
        }),
    }
}

pub struct Vm<'t> {
    pub lib: Library<'t>,
    pub pc: ProgramCounter,
    pub stack: Stack,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProgramCounter {
    pub sentence_idx: SentenceIndex,
    pub word_idx: usize,
}

pub enum StepResult {
    Trap,
    Continue,
}

impl<'t> Vm<'t> {
    pub fn new(lib: Library<'t>) -> Result<Self, LoadError> {
        let &Entry::Value(Value::Pointer(Closure(_, main))) =
            lib.root_namespace().get("main").unwrap()
        else {
            panic!("not code")
        };

        Ok(Vm {
            lib,
            pc: ProgramCounter {
                sentence_idx: main,
                word_idx: 0,
            },
            stack: Stack::default(),
        })
    }

    pub fn current_word(&self) -> Option<&Word<'t>> {
        self.lib.sentences[self.pc.sentence_idx]
            .words
            .get(self.pc.word_idx)
    }

    pub fn prev_word(&self) -> Option<&Word<'t>> {
        self.lib.sentences[self.pc.sentence_idx]
            .words
            .get(self.pc.word_idx - 1)
    }

    pub fn jump_to(&mut self, Closure(closure, sentence_idx): Closure) {
        for v in closure {
            self.stack.push(v);
        }
        self.pc.sentence_idx = sentence_idx;
        self.pc.word_idx = 0;
    }

    pub fn run_to_trap(&mut self) -> Result<(), EvalError> {
        loop {
            match self.step()? {
                StepResult::Continue => {}
                StepResult::Trap => return Ok(()),
            }
        }
    }

    pub fn step(&mut self) -> Result<StepResult, EvalError> {
        let sentence = &self.lib.sentences[self.pc.sentence_idx];

        if let Some(word) = sentence.words.get(self.pc.word_idx) {
            eval(&self.lib, &mut self.stack, &word)?;
            self.pc.word_idx += 1;
            Ok(StepResult::Continue)
        } else {
            let next = control_flow(&self.lib, &mut self.stack).map_err(|inner| EvalError {
                location: sentence.words.last().map(|w| w.location()),
                inner,
            })?;

            if next.1 == SentenceIndex::TRAP {
                for v in next.0 {
                    self.stack.push(v);
                }
                Ok(StepResult::Trap)
            } else {
                self.jump_to(next);
                Ok(StepResult::Continue)
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Stack {
    inner: Vec<Value>,
    stash: Vec<Value>,
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

    pub fn tuple(&mut self, back_idx: usize) -> Result<(), InnerEvalError> {
        let Some(v) = self.inner.iter().rev().nth(back_idx) else {
            ebail!("out of range: {}", back_idx)
        };

        self.push(v.clone());
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

    pub fn stash(&mut self) -> Result<(), InnerEvalError> {
        self.stash
            .push(self.inner.pop().context("stashed from empty stack")?);
        Ok(())
    }

    pub fn unstash(&mut self) -> Result<(), InnerEvalError> {
        self.inner
            .push(self.stash.pop().context("unstashed from empty stash")?);
        Ok(())
    }

    pub fn get(&self, idx: usize) -> Option<&Value> {
        let Ok(idx) = self.back_idx(idx) else {
            return None;
        };
        self.inner.get(idx)
    }
}
