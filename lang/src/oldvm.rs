use std::io::{stdin, stdout, Read, Write};

use anyhow::{anyhow, Context};
use itertools::Itertools;

use crate::{
    flat::{self, Builtin, InnerWord, Library, SentenceIndex, Value, ValueType, Word},
    runtime::{self, Runtime},
    source::{self, FileSpan},
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

fn eval<'t>(stack: &mut Stack, w: &Word) -> Result<EvalResult, EvalError> {
    inner_eval(stack, &w.inner).map_err(|inner| EvalError {
        location: Some(w.span),
        inner,
    })
}

#[derive(Debug, thiserror::Error)]
#[error("could not convert to {r#type}: {value:?}")]
pub struct ConversionError {
    pub value: Value,
    pub r#type: ValueType,
}

impl TryInto<bool> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<bool, Self::Error> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Bool,
            }),
        }
    }
}

impl TryInto<usize> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<usize, Self::Error> {
        match self {
            Value::Usize(u) => Ok(u),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Usize,
            }),
        }
    }
}

impl TryInto<char> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<char, Self::Error> {
        match self {
            Value::Char(c) => Ok(c),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Char,
            }),
        }
    }
}

impl TryInto<String> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<String, Self::Error> {
        match self {
            Value::Symbol(s) => Ok(s),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Symbol,
            }),
        }
    }
}

impl TryInto<Vec<Value>> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<Vec<Value>, Self::Error> {
        match self {
            Value::Tuple(b) => Ok(b),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Bool,
            }),
        }
    }
}
impl TryInto<Vec<Option<Value>>> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<Vec<Option<Value>>, Self::Error> {
        match self {
            Value::Array(b) => Ok(b),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Array,
            }),
        }
    }
}
trait BuiltinArgumentResult<T>: Sized {
    fn into_result(self) -> Result<T, ConversionError>;

    fn at_index(self, index: usize) -> Result<T, BuiltinError> {
        self.into_result()
            .map_err(|e| BuiltinError::InvalidArgument {
                index,
                conversion_error: e,
            })
    }
}

impl<T, U> BuiltinArgumentResult<T> for U
where
    U: TryInto<T, Error = ConversionError>,
{
    fn into_result(self) -> Result<T, ConversionError> {
        self.try_into()
    }
}

fn inner_eval(stack: &mut Stack, w: &InnerWord) -> Result<EvalResult, InnerEvalError> {
    match w {
        InnerWord::Builtin(b) => {
            eval_builtin(stack, *b).map_err(|e| InnerEvalError::BuiltinError {
                builtin: *b,
                source: e,
            })
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
            stack.copy(*idx)?;
            Ok(EvalResult::Continue)
        }
        InnerWord::Move(idx) => {
            stack.mv(*idx)?;
            Ok(EvalResult::Continue)
        }
        &InnerWord::_Send(idx) => {
            stack.sd(idx)?;
            Ok(EvalResult::Continue)
        }
        &InnerWord::Drop(idx) => {
            stack.drop(idx)?;
            Ok(EvalResult::Continue)
        }
        InnerWord::Push(v) => {
            stack.push(v.clone());
            Ok(EvalResult::Continue)
        }
        InnerWord::Call(sentence_idx) => Ok(EvalResult::Call(*sentence_idx)),
        InnerWord::Branch(true_case, false_case) => {
            stack
                .check_size(1)
                .map_err(|_| InnerEvalError::EmptyStack)?;
            let cond: bool = stack
                .pop()
                .unwrap()
                .try_into()
                .map_err(|e| InnerEvalError::InvalidBranchCondition { source: e })?;
            if cond {
                Ok(EvalResult::Call(*true_case))
            } else {
                Ok(EvalResult::Call(*false_case))
            }
        }
        InnerWord::JumpTable(targets) => {
            stack
                .check_size(1)
                .map_err(|_| InnerEvalError::EmptyStack)?;
            let cond: usize = stack
                .pop()
                .unwrap()
                .try_into()
                .map_err(|e| InnerEvalError::JumpTableInvalidIndex { source: e })?;
            if cond >= targets.len() {
                Err(InnerEvalError::JumpTableIndexOutOfBounds {
                    index: cond,
                    size: targets.len(),
                })
            } else {
                Ok(EvalResult::Call(targets[cond]))
            }
        }
    }
}

fn eval_builtin(stack: &mut Stack, b: Builtin) -> Result<EvalResult, BuiltinError> {
    match b {
        Builtin::Panic => {
            if stack.is_empty() {
                Err(BuiltinError::ExplicitPanic(Value::Tuple(vec![])))
            } else {
                let v = stack.pop().unwrap();
                Err(BuiltinError::ExplicitPanic(v))
            }
        }
        Builtin::Add => {
            stack.check_size(2)?;
            let a: usize = stack.pop().unwrap().at_index(1)?;
            let b: usize = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Usize(a + b));
            Ok(EvalResult::Continue)
        }
        Builtin::Sub => {
            stack.check_size(2)?;
            let b: usize = stack.pop().unwrap().at_index(1)?;
            let a: usize = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Usize(a - b));
            Ok(EvalResult::Continue)
        }
        Builtin::Prod => {
            stack.check_size(2)?;
            let a: usize = stack.pop().unwrap().at_index(1)?;
            let b: usize = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Usize(a * b));
            Ok(EvalResult::Continue)
        }

        Builtin::Ord => {
            stack.check_size(1)?;
            let c: char = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Usize(c as usize));
            Ok(EvalResult::Continue)
        }
        Builtin::Eq => {
            stack.check_size(2)?;
            let a = stack.pop().unwrap();
            let b = stack.pop().unwrap();
            stack.push(Value::Bool(a == b));
            Ok(EvalResult::Continue)
        }
        Builtin::AssertEq => {
            stack.check_size(2)?;
            let a = stack.pop().unwrap();
            let b = stack.pop().unwrap();
            if a != b {
                Err(BuiltinError::Assertion(anyhow!("{:?} != {:?}", a, b)))
            } else {
                Ok(EvalResult::Continue)
            }
        }
        Builtin::And => {
            stack.check_size(2)?;
            let a: bool = stack.pop().unwrap().at_index(1)?;
            let b: bool = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Bool(a && b));
            Ok(EvalResult::Continue)
        }
        Builtin::Or => {
            stack.check_size(2)?;
            let a: bool = stack.pop().unwrap().at_index(1)?;
            let b: bool = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Bool(a || b));
            Ok(EvalResult::Continue)
        }
        Builtin::Not => {
            stack.check_size(1)?;
            let a: bool = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Bool(!a));
            Ok(EvalResult::Continue)
        }
        Builtin::SymbolCharAt => {
            stack.check_size(2)?;
            let idx: usize = stack.pop().unwrap().at_index(1)?;
            let sym: String = stack.pop().unwrap().at_index(0)?;
            stack.push(sym.chars().nth(idx).unwrap().into());
            Ok(EvalResult::Continue)
        }
        Builtin::SymbolLen => {
            stack.check_size(1)?;
            let sym: String = stack.pop().unwrap().at_index(0)?;
            stack.push(sym.chars().count().into());
            Ok(EvalResult::Continue)
        }
        Builtin::Lt => {
            stack.check_size(2)?;
            let b: usize = stack.pop().unwrap().at_index(1)?;
            let a: usize = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Bool(a < b));
            Ok(EvalResult::Continue)
        }

        Builtin::If => {
            stack.check_size(3)?;
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            let cond: bool = stack.pop().unwrap().at_index(0)?;
            if cond {
                stack.push(a);
            } else {
                stack.push(b);
            }
            Ok(EvalResult::Continue)
        }
        Builtin::ArrayCreate => {
            stack.check_size(1)?;
            let size: usize = stack.pop().unwrap().at_index(0)?;
            stack.push(Value::Array(vec![None; size]));
            Ok(EvalResult::Continue)
        }
        Builtin::ArrayFree => {
            stack.check_size(1)?;
            let _: Vec<Option<Value>> = stack.pop().unwrap().at_index(0)?;
            Ok(EvalResult::Continue)
        }
        Builtin::ArraySet => {
            stack.check_size(3)?;
            let value = stack.pop().unwrap();
            let idx: usize = stack.pop().unwrap().at_index(1)?;
            let mut arr: Vec<Option<Value>> = stack.pop().unwrap().at_index(0)?;
            if idx >= arr.len() {
                Err(BuiltinError::IndexOutOfBounds {
                    index: idx,
                    size: arr.len(),
                })
            } else {
                arr[idx] = Some(value);
                stack.push(Value::Array(arr));
                Ok(EvalResult::Continue)
            }
        }
        Builtin::ArrayGet => {
            stack.check_size(2)?;
            let idx: usize = stack.pop().unwrap().at_index(1)?;
            let mut arr: Vec<Option<Value>> = stack.pop().unwrap().at_index(0)?;
            if idx >= arr.len() {
                Err(BuiltinError::IndexOutOfBounds {
                    index: idx,
                    size: arr.len(),
                })
            } else {
                let Some(value) = std::mem::take(&mut arr[idx]) else {
                    return Err(BuiltinError::UninitializedArrayElement { index: idx });
                };
                stack.push(Value::Array(arr));
                stack.push(value);
                Ok(EvalResult::Continue)
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum InnerEvalError {
    #[error("Stack empty at end of sentence")]
    EmptyStack,

    #[error("branch condition must be a boolean: {source:?}")]
    InvalidBranchCondition { source: ConversionError },

    #[error("jump table index must be a usize: {source:?}")]
    JumpTableInvalidIndex { source: ConversionError },

    #[error("jump table index out of bounds. size: {size}; index: {index}")]
    JumpTableIndexOutOfBounds { index: usize, size: usize },

    #[error("in builtin {builtin:?}, {source}")]
    BuiltinError {
        builtin: Builtin,
        source: BuiltinError,
    },

    #[error("Attempted to untuple a non-tuple: {value:?}")]
    UntupleNonTuple { value: Value },

    #[error("runtime error: {0}")]
    Runtime(#[from] runtime::Error),

    #[error("other error: {0}")]
    Other(#[from] anyhow::Error),
}

#[derive(Debug, thiserror::Error)]
pub enum BuiltinError {
    #[error("Not enough arguments. Need {needed}, found {found}")]
    InsufficientArguments { needed: usize, found: usize },

    #[error("While converting arg {index}: {conversion_error:?}")]
    InvalidArgument {
        index: usize,
        conversion_error: ConversionError,
    },

    #[error("Assertion failed: {0}")]
    Assertion(#[from] anyhow::Error),

    #[error("Explicit panic: {0:?}")]
    ExplicitPanic(Value),

    #[error("Array index out of bounds: {index}, size: {size}")]
    IndexOutOfBounds { index: usize, size: usize },

    #[error("Array element uninitialized: {index}")]
    UninitializedArrayElement { index: usize },
}

pub struct Vm {
    pub lib: Library,
    pub call_stack: Vec<ProgramCounter>,
    pub stack: Stack,

    pub runtime: Runtime,
    pub main_symbol: SentenceIndex,

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

    pub fn init(&mut self) {
        self.stack.push(tuple![tagged![start {}], tagged![in {}]]);
        self.call_stack = vec![ProgramCounter {
            sentence_idx: self.main_symbol,
            word_idx: 0,
        }]
    }

    pub fn step(&mut self) -> Result<Option<flat::Value>, EvalError> {
        match self.inner_step()? {
            StepResult::Continue => Ok(None),
            StepResult::Exit => {
                let Value::Tuple(result) = self.stack.pop().expect("nothing on stack") else {
                    panic!("not a tuple")
                };
                let (state, msg) = result
                    .into_iter()
                    .collect_tuple()
                    .expect("Must return pair");

                let (tag, args) = msg.into_tagged().expect("Should be tagged");
                match tag.as_str() {
                    "pass" => {
                        self.stack.push(tuple![state, tagged![pass {}]]);
                        self.call_stack = vec![ProgramCounter {
                            sentence_idx: self.main_symbol,
                            word_idx: 0,
                        }];
                        Ok(None)
                    }
                    "exit" => {
                        let Value::Usize(status) = args
                            .into_iter()
                            .exactly_one()
                            .expect("must exit with a usize status code")
                        else {
                            panic!("return value must be a usize")
                        };
                        self.runtime.handle_exit(status);
                        Ok(None)
                    }
                    "req" => {
                        let (state, msg) =
                            args.into_iter().collect_tuple().expect("req has two args");
                        let reply = self.runtime.handle_request(msg).map_err(|e| EvalError {
                            location: None,
                            inner: e.into(),
                        })?;
                        self.stack.push(tagged![reply { state, reply }]);
                        Ok(None)
                    }
                    _ => panic!("unknown tag: {}", tag),
                }
            }
        }
    }

    fn inner_step(&mut self) -> Result<StepResult, EvalError> {
        let pc = loop {
            let Some(pc) = self.call_stack.last_mut() else {
                return Ok(StepResult::Exit);
            };
            break pc;
        };
        let word = &self.lib.sentences[pc.sentence_idx].words[pc.word_idx];
        let res = eval(&mut self.stack, &word)?;
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

    pub fn run(&mut self) -> Result<(), EvalError> {
        while let None = self.step()? {}
        Ok(())
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
        if self.inner.is_empty() {
            return Err(InnerEvalError::EmptyStack);
        }
        let val: Vec<Value> = self
            .inner
            .pop()
            .unwrap()
            .try_into()
            .map_err(|ConversionError { value, .. }| InnerEvalError::UntupleNonTuple { value })?;
        if val.len() != size {
            ebail!("wrong size")
        }
        self.inner.extend(val);
        Ok(())
    }

    pub fn check_size(&self, size: usize) -> Result<(), BuiltinError> {
        if self.len() < size {
            Err(BuiltinError::InsufficientArguments {
                needed: size,
                found: self.len(),
            })
        } else {
            Ok(())
        }
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
