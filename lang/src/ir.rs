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
            let ctx = Context {
                file_idx,
                name_prefix: &name_prefix,
            };
            match decl {
                rawast::Decl::SentenceDecl(sentence_decl) => self.sentences.push(Sentence {
                    span: sentence_decl.span.with_ctx(ctx).into(),
                    name: name_prefix.append(sentence_decl.label.0.with_ctx(ctx).into()),
                    words: sentence_decl.sentence.words.with_ctx(ctx).into(),
                }),
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct Context<'t> {
    file_idx: FileIndex,
    name_prefix: &'t QualifiedName,
}

pub struct WithContext<'t, T>(T, Context<'t>);

pub trait MakeWithContext<'t, T> {
    fn with_ctx(self, ctx: Context<'t>) -> WithContext<'t, T>;
}

impl<'t, T> MakeWithContext<'t, T> for T {
    fn with_ctx(self, ctx: Context<'t>) -> WithContext<'t, T> {
        WithContext(self, ctx)
    }
}

impl<'t, A, B> Into<Vec<B>> for WithContext<'t, Vec<A>>
where
    WithContext<'t, A>: Into<B>,
{
    fn into(self) -> Vec<B> {
        self.0
            .into_iter()
            .map(|a| a.with_ctx(self.1).into())
            .collect()
    }
}

impl<'t> Into<Span> for WithContext<'t, pest::Span<'t>> {
    fn into(self) -> Span {
        Span::File(source::FileSpan {
            file_idx: self.1.file_idx,
            start: self.0.start(),
            end: self.0.end(),
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Identifier(pub Span);

impl<'t> From<WithContext<'t, rawast::Identifier<'t>>> for Identifier {
    fn from(value: WithContext<'t, rawast::Identifier<'t>>) -> Self {
        Self(value.0 .0.with_ctx(value.1).into())
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
    LabelCall(Label),
}

impl<'t> From<WithContext<'t, rawast::Word<'t>>> for Word {
    fn from(WithContext(w, c): WithContext<'t, rawast::Word<'t>>) -> Self {
        match w {
            rawast::Word::StackBindings(bindings) => {
                Word::StackBindings(bindings.with_ctx(c).into())
            }
            rawast::Word::Builtin(builtin) => Word::Builtin(builtin.with_ctx(c).into()),
            rawast::Word::ValueExpression(e) => Word::ValueExpression(e.with_ctx(c).into()),
            rawast::Word::LabelCall(l) => Word::LabelCall(l.with_ctx(c).into()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub path: QualifiedName,
}

impl<'t> From<WithContext<'t, rawast::LabelCall<'t>>> for Label {
    fn from(WithContext(a, c): WithContext<'t, rawast::LabelCall<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
            path: c.name_prefix.join(QualifiedName(a.path.with_ctx(c).into())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StackBindings {
    pub span: Span,
    pub bindings: Vec<Binding>,
}

impl<'t> From<WithContext<'t, rawast::StackBindings<'t>>> for StackBindings {
    fn from(WithContext(a, c): WithContext<'t, rawast::StackBindings<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
            bindings: a.bindings.with_ctx(c).into(),
        }
    }
}
#[derive(Debug, Clone)]
pub enum Binding {
    Drop(DropBinding),
    // Tuple(TupleBinding),
    Literal(Literal),
    Identifier(Identifier),
}
impl<'t> From<WithContext<'t, rawast::Binding<'t>>> for Binding {
    fn from(WithContext(a, c): WithContext<'t, rawast::Binding<'t>>) -> Self {
        match a {
            rawast::Binding::Drop(drop_binding) => Self::Drop(drop_binding.with_ctx(c).into()),
            // rawast::Binding::Tuple(b) => {
            //     Self::Tuple(b.with_ctx(c).into())
            // }
            rawast::Binding::Literal(literal) => Self::Literal(literal.with_ctx(c).into()),
            rawast::Binding::Identifier(identifier) => {
                Self::Identifier(identifier.with_ctx(c).into())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct DropBinding {
    pub span: Span,
}

impl<'t> From<WithContext<'t, rawast::DropBinding<'t>>> for DropBinding {
    fn from(WithContext(a, c): WithContext<'t, rawast::DropBinding<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
        }
    }
}

// #[derive(Debug, Clone)]
// pub struct TupleBinding {
//     pub span: Span,
//     pub bindings: Vec<Binding>,
// }

// impl <'t> From<WithContext<'t, rawast::TupleBinding<'t>>> for TupleBinding {
//     fn from(
//         WithContext(a, c):
//         WithContext<'t, rawast::TupleBinding<'t>>,
//     ) -> Self {
//         Self {
//             span: a.span.with_ctx(c).into(),
//             bindings: a
//                 .bindings.with_ctx(c).into(),
//         }
//     }
// }

#[derive(Debug, Clone)]
pub struct Int {
    pub span: Span,
    pub value: usize,
}

impl<'t> From<WithContext<'t, rawast::Int<'t>>> for Int {
    fn from(WithContext(a, c): WithContext<'t, rawast::Int<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
            value: a.value,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub span: Span,
    pub value: String,
}

impl<'t> From<WithContext<'t, rawast::Symbol<'t>>> for Symbol {
    fn from(WithContext(a, c): WithContext<'t, rawast::Symbol<'t>>) -> Self {
        match a {
            rawast::Symbol::Identifier(a) => Self {
                span: a.0.with_ctx(c).into(),
                value: a.0.as_str().to_owned(),
            },
            rawast::Symbol::String(a) => Self {
                span: a.span.with_ctx(c).into(),
                value: a.value,
            },
        }
    }
}

#[derive(Debug)]
pub enum BuiltinArg {
    Int(Int),
    Label(Label),
}

impl<'t> From<WithContext<'t, rawast::BuiltinArg<'t>>> for BuiltinArg {
    fn from(WithContext(a, c): WithContext<'t, rawast::BuiltinArg<'t>>) -> Self {
        match a {
            rawast::BuiltinArg::Int(int) => BuiltinArg::Int(int.with_ctx(c).into()),
            rawast::BuiltinArg::Label(label) => BuiltinArg::Label(label.with_ctx(c).into()),
        }
    }
}

#[derive(Debug)]
pub struct Builtin {
    pub span: Span,
    pub name: Identifier,
    pub args: Vec<BuiltinArg>,
}
impl<'t> From<WithContext<'t, rawast::Builtin<'t>>> for Builtin {
    fn from(WithContext(a, c): WithContext<'t, rawast::Builtin<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
            name: a.name.with_ctx(c).into(),
            args: a.args.with_ctx(c).into(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(Int),
    Symbol(Symbol),
}
impl<'t> From<WithContext<'t, rawast::Literal<'t>>> for Literal {
    fn from(WithContext(a, c): WithContext<'t, rawast::Literal<'t>>) -> Self {
        match a {
            rawast::Literal::Int(int) => Literal::Int(int.with_ctx(c).into()),
            rawast::Literal::Symbol(a) => Literal::Symbol(a.with_ctx(c).into()),
        }
    }
}

impl Literal {
    pub fn span(&self) -> Span {
        match self {
            Literal::Int(int) => int.span,
            Literal::Symbol(a) => a.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Tuple {
    pub span: Span,
    pub values: Vec<ValueExpression>,
}
impl<'t> From<WithContext<'t, rawast::Tuple<'t>>> for Tuple {
    fn from(WithContext(a, c): WithContext<'t, rawast::Tuple<'t>>) -> Self {
        Self {
            span: a.span.with_ctx(c).into(),
            values: a.values.with_ctx(c).into(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ValueExpression {
    Literal(Literal),
    Copy(Identifier),
    Move(Identifier),
    Tuple(Tuple),
}

impl<'t> From<WithContext<'t, rawast::ValueExpression<'t>>> for ValueExpression {
    fn from(WithContext(a, c): WithContext<'t, rawast::ValueExpression<'t>>) -> Self {
        match a {
            rawast::ValueExpression::Literal(literal) => {
                ValueExpression::Literal(literal.with_ctx(c).into())
            }
            rawast::ValueExpression::Move(a) => ValueExpression::Move(a.with_ctx(c).into()),
            rawast::ValueExpression::Copy(a) => ValueExpression::Copy(a.0.with_ctx(c).into()),
            rawast::ValueExpression::Tuple(tuple) => {
                ValueExpression::Tuple(tuple.with_ctx(c).into())
            }
        }
    }
}
