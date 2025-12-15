use crate::{
    bytecode::{Builtin, StackOperation, Word},
    vm::value::{self, ConversionError, Value},
};

#[derive(Debug, Default, Clone)]
pub struct Stack {
    inner: Vec<Value>,
}

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
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

    #[error("tuple wrong size: expected {expected}, got {got}")]
    UntupleWrongSize { expected: usize, got: usize },

    #[error("index out of range: {idx}")]
    IndexOutOfRange { idx: usize },
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

    pub fn copy(&mut self, back_idx: usize) -> Result<(), EvalError> {
        let Some(v) = self.inner.iter().rev().nth(back_idx) else {
            return Err(EvalError::IndexOutOfRange { idx: back_idx });
        };

        self.push(v.clone());
        Ok(())
    }

    pub fn mv(&mut self, back_idx: usize) -> Result<(), EvalError> {
        let val = self.inner.remove(self.back_idx(back_idx)?);
        self.inner.push(val);
        Ok(())
    }

    pub fn sd(&mut self, back_idx: usize) -> Result<(), EvalError> {
        let new_idx = self.back_idx(back_idx)?;
        let Some(val) = self.inner.pop() else {
            return Err(EvalError::EmptyStack);
        };
        if self.inner.len() < new_idx {
            return Err(EvalError::IndexOutOfRange { idx: new_idx });
        }
        self.inner.insert(new_idx, val);
        Ok(())
    }

    pub fn drop(&mut self, back_idx: usize) -> Result<(), EvalError> {
        self.inner.remove(self.back_idx(back_idx)?);
        Ok(())
    }

    pub fn tuple(&mut self, size: usize) -> Result<(), EvalError> {
        let vals = self.inner.split_off(self.inner.len() - size);
        self.push(Value::Tuple(vals));
        Ok(())
    }

    pub fn untuple(&mut self, size: usize) -> Result<(), EvalError> {
        if self.inner.is_empty() {
            return Err(EvalError::EmptyStack);
        }
        let val: Vec<Value> = self
            .inner
            .pop()
            .ok_or(EvalError::EmptyStack)?
            .try_into()
            .map_err(|e: ConversionError| EvalError::UntupleNonTuple { value: e.value })?;
        if val.len() != size {
            return Err(EvalError::UntupleWrongSize {
                expected: size,
                got: val.len(),
            });
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

    fn back_idx(&self, back_idx: usize) -> Result<usize, EvalError> {
        self.inner
            .len()
            .checked_sub(1 + back_idx)
            .ok_or(EvalError::IndexOutOfRange { idx: back_idx })
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

    pub fn inner_eval(&mut self, w: StackOperation) -> Result<(), EvalError> {
        match w {
            StackOperation::Builtin(b) => {
                self.eval_builtin(b).map_err(|e| EvalError::BuiltinError {
                    builtin: b,
                    source: e,
                })
            }
            StackOperation::Tuple(idx) => {
                self.tuple(idx)?;
                Ok(())
            }
            StackOperation::Untuple(idx) => {
                self.untuple(idx)?;
                Ok(())
            }
            StackOperation::Copy(idx) => {
                self.copy(idx)?;
                Ok(())
            }
            StackOperation::Move(idx) => {
                self.mv(idx)?;
                Ok(())
            }
            StackOperation::Drop(idx) => {
                self.drop(idx)?;
                Ok(())
            }
            StackOperation::Push(v) => {
                self.push(v.into());
                Ok(())
            }
        }
    }

    fn eval_builtin(&mut self, b: Builtin) -> Result<(), BuiltinError> {
        match b {
            Builtin::Panic => {
                if self.is_empty() {
                    Err(BuiltinError::ExplicitPanic(Value::Tuple(vec![])))
                } else {
                    let v = self.pop().unwrap();
                    Err(BuiltinError::ExplicitPanic(v))
                }
            }
            Builtin::Add => {
                self.check_size(2)?;
                let a: usize = self.pop().unwrap().at_index(1)?;
                let b: usize = self.pop().unwrap().at_index(0)?;
                self.push(Value::Usize(a + b));
                Ok(())
            }
            Builtin::Sub => {
                self.check_size(2)?;
                let b: usize = self.pop().unwrap().at_index(1)?;
                let a: usize = self.pop().unwrap().at_index(0)?;
                self.push(Value::Usize(a - b));
                Ok(())
            }
            Builtin::Prod => {
                self.check_size(2)?;
                let a: usize = self.pop().unwrap().at_index(1)?;
                let b: usize = self.pop().unwrap().at_index(0)?;
                self.push(Value::Usize(a * b));
                Ok(())
            }

            Builtin::Ord => {
                self.check_size(1)?;
                let c: char = self.pop().unwrap().at_index(0)?;
                self.push(Value::Usize(c as usize));
                Ok(())
            }
            Builtin::Eq => {
                self.check_size(2)?;
                let a = self.pop().unwrap();
                let b = self.pop().unwrap();
                self.push(Value::Bool(a == b));
                Ok(())
            }
            Builtin::AssertEq => {
                self.check_size(2)?;
                let a = self.pop().unwrap();
                let b = self.pop().unwrap();
                if a != b {
                    Err(BuiltinError::Assertion(AssertionError::ValuesNotEqual {
                        a,
                        b,
                    }))
                } else {
                    Ok(())
                }
            }
            Builtin::And => {
                self.check_size(2)?;
                let a: bool = self.pop().unwrap().at_index(1)?;
                let b: bool = self.pop().unwrap().at_index(0)?;
                self.push(Value::Bool(a && b));
                Ok(())
            }
            Builtin::Or => {
                self.check_size(2)?;
                let a: bool = self.pop().unwrap().at_index(1)?;
                let b: bool = self.pop().unwrap().at_index(0)?;
                self.push(Value::Bool(a || b));
                Ok(())
            }
            Builtin::Not => {
                self.check_size(1)?;
                let a: bool = self.pop().unwrap().at_index(0)?;
                self.push(Value::Bool(!a));
                Ok(())
            }
            Builtin::Lt => {
                self.check_size(2)?;
                let b: usize = self.pop().unwrap().at_index(1)?;
                let a: usize = self.pop().unwrap().at_index(0)?;
                self.push(Value::Bool(a < b));
                Ok(())
            }

            Builtin::If => {
                self.check_size(3)?;
                let b = self.pop().unwrap();
                let a = self.pop().unwrap();
                let cond: bool = self.pop().unwrap().at_index(0)?;
                if cond {
                    self.push(a);
                } else {
                    self.push(b);
                }
                Ok(())
            }
            Builtin::ArrayCreate => {
                self.check_size(1)?;
                let size: usize = self.pop().unwrap().at_index(0)?;
                self.push(Value::Array(vec![None; size]));
                Ok(())
            }
            Builtin::ArrayFree => {
                self.check_size(1)?;
                let _: Vec<Option<Value>> = self.pop().unwrap().at_index(0)?;
                Ok(())
            }
            Builtin::ArraySet => {
                self.check_size(3)?;
                let value = self.pop().unwrap();
                let idx: usize = self.pop().unwrap().at_index(1)?;
                let mut arr: Vec<Option<Value>> = self.pop().unwrap().at_index(0)?;
                if idx >= arr.len() {
                    Err(BuiltinError::IndexOutOfBounds {
                        index: idx,
                        size: arr.len(),
                    })
                } else {
                    arr[idx] = Some(value);
                    self.push(Value::Array(arr));
                    Ok(())
                }
            }
            Builtin::ArrayGet => {
                self.check_size(2)?;
                let idx: usize = self.pop().unwrap().at_index(1)?;
                let mut arr: Vec<Option<Value>> = self.pop().unwrap().at_index(0)?;
                if idx >= arr.len() {
                    Err(BuiltinError::IndexOutOfBounds {
                        index: idx,
                        size: arr.len(),
                    })
                } else {
                    let Some(value) = std::mem::take(&mut arr[idx]) else {
                        return Err(BuiltinError::UninitializedArrayElement { index: idx });
                    };
                    self.push(Value::Array(arr));
                    self.push(value);
                    Ok(())
                }
            }
        }
    }
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
    Assertion(#[from] AssertionError),

    #[error("Explicit panic: {0:?}")]
    ExplicitPanic(Value),

    #[error("Array index out of bounds: {index}, size: {size}")]
    IndexOutOfBounds { index: usize, size: usize },

    #[error("Array element uninitialized: {index}")]
    UninitializedArrayElement { index: usize },
}

#[derive(Debug, thiserror::Error)]
pub enum AssertionError {
    #[error("values not equal: {a:?} != {b:?}")]
    ValuesNotEqual { a: Value, b: Value },
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
