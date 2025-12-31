
use derive_more::derive::{From, Into};

use crate::{
    bytecode::Builtin,
    parser::source,
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IdentifierIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PathIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VariableRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolDefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SentenceDefIndex(usize);
#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SentenceRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
pub enum WordInner {
    StackOperation(StackOperation),
    Call(SentenceRefIndex),
    Branch(SentenceRefIndex, SentenceRefIndex),
    JumpTable(Vec<SentenceRefIndex>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Word {
    pub inner: WordInner,
    pub span: source::Span,
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
pub struct Path(pub Vec<source::Span>);

impl Path {
    pub fn as_strs<'a>(&self, sources: &'a source::Sources) -> Vec<&'a str> {
        self.0.iter().map(|s| s.as_str(sources)).collect()
    }

    pub fn bind<'a>(&self, sources: &'a source::Sources) -> BoundPath<'a> {
        BoundPath(self.clone(), sources)
    }

    pub fn join(&self, other: impl Into<Path>) -> Path {
        Path(
            self.0
                .iter()
                .copied()
                .chain(other.into().0.iter().copied())
                .collect(),
        )
    }
}

impl From<source::Span> for Path {
    fn from(span: source::Span) -> Self {
        Path(vec![span])
    }
}

pub struct BoundPath<'a>(Path, &'a source::Sources);

impl<'a> BoundPath<'a> {
    pub fn as_strs(&self) -> Vec<&'a str> {
        self.0.as_strs(self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolDef {
    pub name: PathIndex,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRef(PathIndex);
