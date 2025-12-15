use std::{
    collections::{BTreeMap, VecDeque},
    fmt::Display,
    path::PathBuf,
    usize,
};

use derive_more::derive::{From, Into};
use itertools::Itertools;
use thiserror::Error;
use typed_index_collections::TiVec;

use crate::{
    ast,
    source::{self, FileSpan},
};

macro_rules! tuple {
    [$($x:expr),* $(,)?] => {crate::flat::Value::Tuple(vec![$($x),*])};
}
macro_rules! symbol {
    ($x:expr) => {
        crate::flat::Value::Symbol($x.to_owned())
    };
}
macro_rules! tagged {
    ($tag:ident {$($x:expr),* $(,)?}) => {crate::flat::tuple![symbol!(stringify!($tag)), crate::flat::tuple![$($x),*]]};
}

pub(crate) use symbol;
pub(crate) use tagged;
pub(crate) use tuple;

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SentenceIndex(usize);

impl SentenceIndex {
    pub const TRAP: Self = SentenceIndex(usize::MAX);
}

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NamespaceIndex(usize);

#[derive(Debug, Clone, Default)]
pub struct Library {
    pub sentences: TiVec<SentenceIndex, Sentence>,

    pub exports: BTreeMap<String, SentenceIndex>,
}

#[derive(Debug, Error)]

pub struct LoadError {
    pub path: PathBuf,
    pub error: LoadErrorInner,
}

impl Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "In file {}, error: {}", self.path.display(), self.error)
    }
}

#[derive(Debug, Error)]

pub enum LoadErrorInner {
    #[error("error reading file")]
    IO(#[from] anyhow::Error),
    #[error("duplicate path")]
    DuplicatePath,
    #[error("error parsing file:\n{0}")]
    Parse(#[from] pest::error::Error<ast::Rule>),
}

impl Library {
    pub fn export(&self, label: &str) -> Option<SentenceIndex> {
        self.exports.get(label).cloned()
    }
}

#[derive(Debug, Clone)]
pub struct Sentence {
    pub words: Vec<Word>,
}

macro_rules! builtins {
    {
        $(($ident:ident, $name:literal),)*
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Builtin {
            $($ident,)*
        }

        impl Builtin {
            pub const ALL: &'static [Builtin] = &[
                $(Builtin::$ident,)*
            ];

            pub fn name(self) -> &'static str {
                match self {
                    $(Builtin::$ident => $name,)*
                }
            }
        }
    };
}

builtins! {
    (Panic, "panic"),

    (Add, "add"),
    (Sub, "sub"),
    (Prod, "prod"),
    (Eq, "eq"),
    (AssertEq, "assert_eq"),
    (Or, "or"),
    (And, "and"),
    (Not, "not"),
    (SymbolCharAt, "symbol_char_at"),
    (SymbolLen, "symbol_len"),

    (Lt, "lt"),

    (If, "if"),

    (Ord, "ord"),

    (ArrayCreate, "array_create"),
    (ArrayFree, "array_free"),
    (ArrayGet, "array_get"),
    (ArraySet, "array_set"),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Word {
    pub inner: InnerWord,
    pub span: FileSpan,
    pub names: Option<VecDeque<Option<String>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InnerWord {
    Push(Value),
    Copy(usize),
    Drop(usize),
    Move(usize),
    _Send(usize),
    Builtin(Builtin),
    Tuple(usize),
    Untuple(usize),
    Call(SentenceIndex),
    Branch(SentenceIndex, SentenceIndex),
    JumpTable(Vec<SentenceIndex>),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Value {
    Symbol(String),
    Usize(usize),
    Tuple(Vec<Value>),
    Bool(bool),
    Char(char),
    Array(Vec<Option<Value>>),
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
        }
    }

    pub fn into_tagged(self) -> Option<(String, Vec<Value>)> {
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
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Closure(pub Vec<Value>, pub SentenceIndex);

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Namespace2 {
    pub items: Vec<(String, Value)>,
}

pub struct ValueView<'a> {
    pub sources: &'a source::Sources,
    pub value: &'a Value,
}

impl<'a> std::fmt::Display for ValueView<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Value::Symbol(arg0) => write!(f, "@{}", arg0.replace("\n", "\\n")),
            Value::Usize(arg0) => write!(f, "{}", arg0),
            Value::Bool(arg0) => write!(f, "{}", arg0),
            Value::Tuple(values) => {
                if values.len() == 2
                    && values[0].r#type() == ValueType::Symbol
                    && values[1].r#type() == ValueType::Tuple
                {
                    let Value::Symbol(symbol) = &values[0] else {
                        panic!()
                    };
                    let Value::Tuple(args) = &values[1] else {
                        panic!()
                    };
                    write!(
                        f,
                        "#{}{{{}}}",
                        symbol,
                        args.iter()
                            .map(|v| ValueView {
                                sources: self.sources,
                                value: v
                            })
                            .join(", ")
                    )
                } else {
                    write!(
                        f,
                        "({})",
                        values
                            .iter()
                            .map(|v| ValueView {
                                sources: self.sources,
                                value: v
                            })
                            .join(", ")
                    )
                }
            }
            Value::Char(arg0) => write!(f, "'{}'", arg0),
            Value::Array(elements) => {
                write!(
                    f,
                    "[{}]",
                    elements
                        .iter()
                        .map(|v| if let Some(v) = v {
                            ValueView {
                                sources: self.sources,
                                value: v,
                            }
                            .to_string()
                        } else {
                            "None".to_string()
                        })
                        .join(", ")
                )
            }
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

#[cfg(test)]
mod tests {}
