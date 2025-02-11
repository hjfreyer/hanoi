use std::collections::BTreeMap;

use typed_index_collections::TiVec;

use crate::{
    flat::SentenceIndex,
    rawast,
    source::{self, FileIndex, Span},
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

    pub fn to_strings(&self, sources: &source::Sources) -> Vec<String> {
        self.0
            .iter()
            .map(|s| s.0.as_str(sources).to_owned())
            .collect()
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
    StackBindings(StackBindings),
    Builtin(Builtin),
    ValueExpression(ValueExpression),
    LabelCall(LabelCall),
}

impl Word {
    fn from_ast(file_idx: FileIndex, name_prefix: &QualifiedName, w: rawast::Word<'_>) -> Self {
        match w {
            rawast::Word::StackBindings(bindings) => {
                Word::StackBindings(StackBindings::from_ast(file_idx, bindings))
            }
            rawast::Word::Builtin(builtin) => {
                Word::Builtin(Builtin::from_ast(file_idx, name_prefix, builtin))
            }
            rawast::Word::ValueExpression(e) => {
                Word::ValueExpression(ValueExpression::from_ast(file_idx, e))
            }
            rawast::Word::LabelCall(l) => {
                Word::LabelCall(LabelCall::from_ast(file_idx, name_prefix, l))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct LabelCall {
    pub span: Span,
    pub path: QualifiedName,
}

impl LabelCall {
    pub fn from_ast(
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        i: rawast::LabelCall,
    ) -> Self {
        Self {
            span: Span::from_ast(file_idx, i.span),
            path: name_prefix.join(QualifiedName(
                i.path
                    .into_iter()
                    .map(|v| Identifier::from_ast(file_idx, v))
                    .collect(),
            )),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StackBindings {
    pub span: Span,
    pub bindings: Vec<Binding>,
}

impl StackBindings {
    fn from_ast(file_idx: FileIndex, r: rawast::StackBindings<'_>) -> Self {
        Self {
            span: Span::from_ast(file_idx, r.span),
            bindings: r
                .bindings
                .into_iter()
                .map(|r| Binding::from_ast(file_idx, r))
                .collect(),
        }
    }
}
#[derive(Debug, Clone)]
pub enum Binding {
    Drop(DropBinding),
    Literal(Literal),
    Identifier(Identifier),
}

impl Binding {
    fn from_ast(file_idx: FileIndex, r: rawast::Binding<'_>) -> Self {
        match r {
            rawast::Binding::DropBinding(drop_binding) => {
                Self::Drop(DropBinding::from_ast(file_idx, drop_binding))
            }
            rawast::Binding::Literal(literal) => {
                Self::Literal(Literal::from_ast(file_idx, literal))
            }
            rawast::Binding::Identifier(identifier) => {
                Self::Identifier(Identifier::from_ast(file_idx, identifier))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct DropBinding {
    pub span: Span,
}

impl DropBinding {
    fn from_ast(file_idx: FileIndex, int: rawast::DropBinding<'_>) -> Self {
        Self {
            span: Span::from_ast(file_idx, int.span),
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum Literal {
    Int(Int),
}

impl Literal {
    fn from_ast(file_idx: FileIndex, literal: rawast::Literal<'_>) -> Self {
        match literal {
            rawast::Literal::Int(int) => Literal::Int(Int::from_ast(file_idx, int)),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Literal::Int(int) => int.span,
        }
    }
}
#[derive(Debug, Clone)]
pub struct Tuple {
    pub span: Span,
    pub values: Vec<ValueExpression>,
}

impl Tuple {
    fn from_ast(file_idx: FileIndex, a: rawast::Tuple) -> Self {
        Self {
            span: Span::from_ast(file_idx, a.span),
            values: a
                .values
                .into_iter()
                .map(|a| ValueExpression::from_ast(file_idx, a))
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ValueExpression {
    Literal(Literal),
    Tuple(Tuple),
}

impl ValueExpression {
    fn from_ast(file_idx: FileIndex, a: rawast::ValueExpression) -> Self {
        match a {
            rawast::ValueExpression::Literal(literal) => {
                Self::Literal(Literal::from_ast(file_idx, literal))
            }
            rawast::ValueExpression::Tuple(tuple) => Self::Tuple(Tuple::from_ast(file_idx, tuple)),
        }
    }
}
