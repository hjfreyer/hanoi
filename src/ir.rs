use std::collections::BTreeMap;

use typed_index_collections::TiVec;

use crate::{
    flat::SentenceIndex,
    rawast,
    source::{FileIndex, Span},
};

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

impl Crate {
    pub fn add_file(
        &mut self,
        name_prefix: QualifiedName,
        file_idx: FileIndex,
        file: rawast::File,
    ) {
        for decl in file.decl {
            match decl {
                rawast::Decl::SentenceDecl(sentence_decl) => self.sentences.push(Sentence {
                    span: Span::from_ast(file_idx, sentence_decl.span),
                    name: name_prefix.append(Identifier::from_ast(file_idx, sentence_decl.label.0)),
                    words: sentence_decl
                        .sentence
                        .words
                        .into_iter()
                        .map(|w| Word::from_ast(file_idx, &name_prefix, w))
                        .collect(),
                }),
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Identifier(pub Span);

impl Identifier {
    pub fn from_ast(file_idx: FileIndex, i: rawast::Identifier) -> Self {
        Self(Span::from_ast(file_idx, i.0))
    }
}

#[derive(Debug, Clone)]
pub struct QualifiedName(pub Vec<Identifier>);

impl QualifiedName {
    pub fn join(&self, other: Self) -> Self {
        let mut res = self.clone();
        res.0.extend(other.0.into_iter());
        res
    }

    pub fn append(&self, label: Identifier) -> Self {
        let mut res = self.clone();
        res.0.push(label);
        res
    }
}

#[derive(Debug)]
pub struct Sentence {
    pub span: Span,
    pub name: QualifiedName,
    pub words: Vec<Word>,
}

#[derive(Debug)]
pub enum Word {
    Builtin(Builtin),
    Literal(Literal),
}

impl Word {
    fn from_ast(file_idx: FileIndex, name_prefix: &QualifiedName, w: rawast::Word<'_>) -> Self {
        match w {
            rawast::Word::Builtin(builtin) => {
                Word::Builtin(Builtin::from_ast(file_idx, name_prefix, builtin))
            }
            rawast::Word::Literal(literal) => Word::Literal(Literal::from_ast(file_idx, literal)),
        }
    }
}

// #[derive(Debug)]
// pub enum InnerWord {
//     Builtin(Builtin),
//     // Copy(usize),
//     // Move(usize),
//     // Send(usize),
//     // Drop(usize),
//     // Push(Value),
//     // Call(usize),
//     // Ref(usize),
//     // Tuple(usize),
//     // Untuple(usize),
// }

#[derive(Debug)]
pub struct Int {
    pub span: Span,
    pub value: usize,
}
impl Int {
    fn from_ast(file_idx: FileIndex, int: rawast::Int<'_>) -> Int {
        Self {
            span: Span::from_ast(file_idx, int.span),
            value: int.value,
        }
    }
}

#[derive(Debug)]
pub enum BuiltinArg {
    Int(Int),
    Label(QualifiedName),
}
impl BuiltinArg {
    fn from_ast(
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        a: rawast::BuiltinArg<'_>,
    ) -> BuiltinArg {
        match a {
            rawast::BuiltinArg::Int(int) => BuiltinArg::Int(Int::from_ast(file_idx, int)),
            rawast::BuiltinArg::Label(label) => {
                BuiltinArg::Label(name_prefix.append(Identifier::from_ast(file_idx, label.0)))
            }
        }
    }
}

#[derive(Debug)]
pub struct Builtin {
    pub span: Span,
    pub name: Identifier,
    pub args: Vec<BuiltinArg>,
}

impl Builtin {
    fn from_ast(
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        builtin: rawast::Builtin<'_>,
    ) -> Self {
        Self {
            span: Span::from_ast(file_idx, builtin.span),
            name: Identifier::from_ast(file_idx, builtin.name),
            args: builtin
                .args
                .into_iter()
                .map(|a| BuiltinArg::from_ast(file_idx, name_prefix, a))
                .collect(),
        }
    }
}

#[derive(Debug)]
pub enum Literal {
    Int(Int),
}

impl Literal {
    fn from_ast(file_idx: FileIndex, literal: rawast::Literal<'_>) -> Self {
        match literal {
            rawast::Literal::Int(int) => Literal::Int(Int::from_ast(file_idx, int)),
        }
    }
}
