use derive_more::derive::{From, Into};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use typed_index_collections::TiVec;

pub mod debuginfo;

macro_rules! builtins {
    {
        $(($ident:ident, $name:literal),)*
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, debug_with::DebugWith)]
        #[debug_with(passthrough)]
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

    (Lt, "lt"),

    (If, "if"),

    (Ord, "ord"),

    (ArrayCreate, "array_create"),
    (ArrayFree, "array_free"),
    (ArrayGet, "array_get"),
    (ArraySet, "array_set"),

    (MapNew, "map_new"),
    (MapGet, "map_get"),
    (MapSet, "map_set"),
}

#[derive(
    From,
    Into,
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    Hash,
    Serialize,
    Deserialize,
    debug_with::DebugWith,
    PartialOrd,
    Ord,
)]
#[debug_with(passthrough)]
pub struct SymbolIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SentenceIndex(usize);

#[derive(
    Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize, debug_with::DebugWith,
)]
#[debug_with(passthrough)]
pub enum PrimitiveValue {
    Symbol(SymbolIndex),
    Usize(usize),
    Bool(bool),
    Char(char),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StackOperation {
    Push(PrimitiveValue),
    Copy(usize),
    Drop(usize),
    Move(usize),
    Builtin(Builtin),
    Tuple(usize),
    Untuple(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Word {
    StackOperation(StackOperation),
    Call(SentenceIndex),
    Branch(SentenceIndex, SentenceIndex),
    JumpTable(Vec<SentenceIndex>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sentence {
    pub words: Vec<Word>,
}

#[derive(Debug, Clone, Default)]
pub struct Library {
    pub debuginfo: debuginfo::Library,
    pub num_symbols: usize,
    pub sentences: TiVec<SentenceIndex, Sentence>,
    pub exports: BTreeMap<String, SentenceIndex>,
}

#[derive(Serialize, Deserialize)]
struct LibrarySerde {
    debuginfo: debuginfo::Library,
    num_symbols: usize,
    sentences: Vec<Sentence>,
    exports: BTreeMap<String, SentenceIndex>,
}

impl Serialize for Library {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let serde_repr = LibrarySerde {
            debuginfo: self.debuginfo.clone(),
            num_symbols: self.num_symbols,
            sentences: self.sentences.iter().cloned().collect(),
            exports: self.exports.clone(),
        };
        serde_repr.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Library {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let serde_repr = LibrarySerde::deserialize(deserializer)?;
        Ok(Library {
            debuginfo: serde_repr.debuginfo,
            num_symbols: serde_repr.num_symbols,
            sentences: serde_repr.sentences.into_iter().collect(),
            exports: serde_repr.exports,
        })
    }
}

impl Library {}
