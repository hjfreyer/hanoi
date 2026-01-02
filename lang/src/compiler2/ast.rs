use derive_more::derive::{From, Into};

use crate::{
    bytecode::{self, Builtin},
    compiler2::unresolved::{DebugWith, UseDebugWith},
    parser::source,
};

use debug_with_trait;

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IdentifierIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PathIndex(usize);

#[derive(
    From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, debug_with::DebugWith,
)]
#[debug_with(passthrough)]
pub struct VariableRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolDefIndex(usize);

#[derive(
    From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, debug_with::DebugWith,
)]
#[debug_with(passthrough)]
pub struct SentenceDefIndex(usize);
#[derive(
    From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, debug_with::DebugWith,
)]
#[debug_with(passthrough)]
pub struct SentenceRefIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionIndex(usize);

#[derive(
    From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, debug_with::DebugWith,
)]
#[debug_with(passthrough)]
pub struct ConstRefIndex(usize);

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum ConstRef {
    Inline(bytecode::PrimitiveValue),
    Path(Path),
}

impl<C> DebugWith<C> for ConstRef
where
    source::Span: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstRef::Inline(value) => f.debug_tuple("ConstRef::Inline").field(value).finish(),
            ConstRef::Path(path) => f
                .debug_tuple("ConstRef::Path")
                .field(&UseDebugWith(path, c))
                .finish(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum StackOperation {
    Push(ConstRefIndex),
    Copy(VariableRefIndex),
    Drop(VariableRefIndex),
    Move(VariableRefIndex),
    Builtin(Builtin),
    Tuple(usize),
    Untuple(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum WordInner {
    StackOperation(StackOperation),
    Call(SentenceRefIndex),
    Branch(SentenceRefIndex, SentenceRefIndex),
    JumpTable(Vec<SentenceRefIndex>),
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Word {
    pub inner: WordInner,
    pub span: source::Span,
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct SentenceDef {
    pub words: Vec<Word>,
}

impl<C> DebugWith<C> for SentenceDef
where
    Word: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.words.iter().map(|w| UseDebugWith(w, c)))
            .finish()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub name: PathIndex,
    pub sentence: SentenceRefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Path(pub Vec<source::Span>);

impl<C> DebugWith<C> for Path
where
    source::Span: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, s) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str("::")?;
            }
            s.debug_with(c, f)?;
        }
        Ok(())
    }
}

impl<C> DebugWith<C> for Word {
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.inner {
            WordInner::StackOperation(operation) => f
                .debug_tuple("WordInner::StackOperation")
                .field(operation)
                .finish(),
            WordInner::Call(sentence_ref_index) => f
                .debug_tuple("WordInner::Call")
                .field(sentence_ref_index)
                .finish(),
            WordInner::Branch(sentence_ref_index, sentence_ref_index2) => f
                .debug_tuple("WordInner::Branch")
                .field(sentence_ref_index)
                .field(sentence_ref_index2)
                .finish(),
            WordInner::JumpTable(sentence_ref_indices) => f
                .debug_tuple("WordInner::JumpTable")
                .field(sentence_ref_indices)
                .finish(),
        }
    }
}

impl Path {
    pub fn as_strs<'a>(&self, sources: &'a source::Sources) -> Vec<&'a str> {
        self.0.iter().map(|s| s.as_str(sources)).collect()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolDef {
    pub name: PathIndex,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolRef(PathIndex);
