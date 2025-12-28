use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
use typed_index_collections::TiVec;

use crate::bytecode::{self, Builtin};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct IdentifierIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PathIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct VariableRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymbolDefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SentenceDefIndex(usize);
#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SentenceRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct FunctionIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ConstRefIndex(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackOperation {
    Push(ConstRefIndex),
    Copy(VariableRefIndex),
    Drop(VariableRefIndex),
    Move(VariableRefIndex),
    Builtin(Builtin),
    Tuple(usize),
    Untuple(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Word {
    StackOperation(StackOperation),
    Call(SentenceRefIndex),
    Branch(SentenceRefIndex, SentenceRefIndex),
    JumpTable(Vec<SentenceRefIndex>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SentenceDef {
    pub words: Vec<Word>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub name: PathIndex,
    pub sentence: SentenceRefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path(pub Vec<IdentifierIndex>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolDef {
    pub name: PathIndex,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRef(PathIndex);
