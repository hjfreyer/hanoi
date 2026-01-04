use std::collections::BTreeMap;

use crate::bytecode::{PrimitiveValue, SymbolIndex};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Value {
    Symbol(SymbolIndex),
    Usize(usize),
    Tuple(Vec<Value>),
    Bool(bool),
    Char(char),
    Array(Vec<Option<Value>>),
    Map(BTreeMap<SymbolIndex, Value>),
}

impl Value {
    pub fn r#type(&self) -> ValueType {
        match self {
            Value::Symbol(_) => ValueType::Symbol,
            Value::Usize(_) => ValueType::Usize,
            Value::Tuple(_) => ValueType::Tuple,
            Value::Bool(_) => ValueType::Bool,
            Value::Char(_) => ValueType::Char,
            Value::Array(_) => ValueType::Array,
            Value::Map(_) => ValueType::Map,
        }
    }

    pub fn into_tagged(self) -> Option<(SymbolIndex, Vec<Value>)> {
        let Value::Tuple(mut values) = self else {
            return None;
        };
        if values.len() != 2 {
            return None;
        }
        let Value::Tuple(args) = values.pop().unwrap() else {
            return None;
        };
        let Value::Symbol(tag) = values.pop().unwrap() else {
            return None;
        };
        Some((tag, args))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ValueType {
    Symbol,
    Usize,
    Tuple,
    Bool,
    Char,
    Array,
    Map,
}

impl std::fmt::Display for ValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Symbol => write!(f, "symbol"),
            ValueType::Usize => write!(f, "usize"),
            ValueType::Tuple => write!(f, "tuple"),
            ValueType::Bool => write!(f, "bool"),
            ValueType::Char => write!(f, "char"),
            ValueType::Array => write!(f, "array"),
            ValueType::Map => write!(f, "map"),
        }
    }
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

impl TryInto<BTreeMap<SymbolIndex, Value>> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<BTreeMap<SymbolIndex, Value>, Self::Error> {
        match self {
            Value::Map(b) => Ok(b),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Map,
            }),
        }
    }
}

impl TryInto<SymbolIndex> for Value {
    type Error = ConversionError;
    fn try_into(self) -> Result<SymbolIndex, Self::Error> {
        match self {
            Value::Symbol(s) => Ok(s),
            _ => Err(ConversionError {
                value: self,
                r#type: ValueType::Symbol,
            }),
        }
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Self::Usize(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<char> for Value {
    fn from(value: char) -> Self {
        Self::Char(value)
    }
}

impl From<PrimitiveValue> for Value {
    fn from(value: PrimitiveValue) -> Self {
        match value {
            PrimitiveValue::Usize(u) => Self::Usize(u),
            PrimitiveValue::Bool(b) => Self::Bool(b),
            PrimitiveValue::Char(c) => Self::Char(c),
            PrimitiveValue::Symbol(s) => Self::Symbol(s),
        }
    }
}
