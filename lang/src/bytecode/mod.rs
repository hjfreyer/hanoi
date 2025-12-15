use derive_more::derive::{From, Into};
use std::collections::BTreeMap;
use typed_index_collections::TiVec;

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

    (Lt, "lt"),

    (If, "if"),

    (Ord, "ord"),

    (ArrayCreate, "array_create"),
    (ArrayFree, "array_free"),
    (ArrayGet, "array_get"),
    (ArraySet, "array_set"),
}

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SentenceIndex(usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum PrimitiveValue {
    Symbol(SymbolIndex),
    Usize(usize),
    Bool(bool),
    Char(char),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackOperation {
    Push(PrimitiveValue),
    Copy(usize),
    Drop(usize),
    Move(usize),
    Builtin(Builtin),
    Tuple(usize),
    Untuple(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Word {
    StackOperation(StackOperation),
    Call(SentenceIndex),
    Branch(SentenceIndex, SentenceIndex),
    JumpTable(Vec<SentenceIndex>),
}

pub struct Sentence {
    pub words: Vec<Word>,
}

pub struct Library {
    pub symbols: TiVec<SymbolIndex, String>,
    pub sentences: TiVec<SentenceIndex, Sentence>,
    pub exports: BTreeMap<String, SentenceIndex>,
}