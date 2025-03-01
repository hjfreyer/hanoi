use std::{collections::BTreeMap, fmt::write};

use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    ast::{self, NamespaceDecl, ProcDecl}, flat::SentenceIndex, source::{self, FileIndex, Span}
};
use from_raw_ast::FromRawAst;

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

impl Crate {
    pub fn add_file(
        &mut self,
        name_prefix: QualifiedName,
        file_idx: FileIndex,
        file: ast::File,
    ) {
        self.visit_namespace(file_idx, &name_prefix, file.ns);
    }

    fn visit_namespace(
        &mut self,
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        ns: ast::Namespace,
    ) {
        for decl in ns.decl {
            let ctx = Context {
                file_idx,
                name_prefix: &name_prefix,
            };
            match decl {
                ast::Decl::SentenceDecl(sentence_decl) => self.sentences.push(Sentence {
                    span: sentence_decl.span.with_ctx(ctx).into(),
                    name: name_prefix.append(Name::from_raw_ast(ctx, sentence_decl.name)),
                    words: FromRawAst::from_raw_ast(ctx, sentence_decl.sentence.words),
                }),
                ast::Decl::Namespace(NamespaceDecl { name, ns }) => {
                    let name = FromRawAst::from_raw_ast(ctx, name);
                    let name_prefix = name_prefix.append(name);
                    self.visit_namespace(file_idx, &name_prefix, ns);
                }
                ast::Decl::Proc(ProcDecl { binding, name, expression }) => {
                    let name = name_prefix.append(Name::from_raw_ast(ctx, name));
                    self.visit_proc(file_idx, &name_prefix, binding, name, expression);
                }
            }
        }
    }
    
    fn visit_proc(&self, file_idx: FileIndex, name_prefix: &QualifiedName, binding: ast::Binding, name: QualifiedName, expression: ast::Expression) {
        todo!()
    }
}

pub trait FromRawAst<'t, R> {
    fn from_raw_ast(ctx: Context<'t>, r: R) -> Self;
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

impl<'t, A, B> FromRawAst<'t, Vec<A>> for Vec<B>
where
    B: FromRawAst<'t, A>,
{
    fn from_raw_ast(ctx: Context<'t>, r: Vec<A>) -> Self {
        r.into_iter()
            .map(|a| FromRawAst::from_raw_ast(ctx, a))
            .collect()
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

impl<'t> FromRawAst<'t, pest::Span<'t>> for Span {
    fn from_raw_ast(ctx: Context<'t>, r: pest::Span<'t>) -> Self {
        Span::File(source::FileSpan {
            file_idx: ctx.file_idx,
            start: r.start(),
            end: r.end(),
        })
    }
}

impl<'t, X, T> FromRawAst<'t, X> for T
where
    T: From<WithContext<'t, X>>,
{
    fn from_raw_ast(ctx: Context<'t>, r: X) -> Self {
        r.with_ctx(ctx).into()
    }
}

#[derive(Debug, Clone, Copy, FromRawAst)]
#[from_raw_ast(raw=ast::Identifier)]
pub struct Identifier(pub Span);

#[derive(Debug, Clone, Copy)]
pub enum Name {
    User(Identifier),
    Generated(usize),
}

impl Name {
    pub fn as_str<'t>(self, sources: &'t source::Sources) -> Option<&'t str> {
        match self {
            Name::User(id) => Some(id.0.as_str(sources)),
            Name::Generated(_) => None,
                    }
    }

pub fn as_ref<'t>(self, sources: &'t source::Sources) -> NameRef<'t> {
        match self {
            Name::User(id) => NameRef::User(id.0.as_str(sources)),
            Name::Generated(id) => NameRef::Generated(id),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq,Eq, PartialOrd, Ord)]
pub enum NameRef<'t> {
    User(&'t str),
    Generated(usize),
}

impl <'t> FromRawAst<'t, ast::Identifier<'t>> for Name {
    fn from_raw_ast(ctx: Context<'t>, r: ast::Identifier<'t>) -> Self {
        Name::User(Identifier::from_raw_ast(ctx, r))
    }
}

#[derive(Debug, Clone)]
pub struct QualifiedName(pub Vec<Name>);

impl QualifiedName {
    pub fn join(&self, other: Self) -> Self {
        let mut res = self.clone();
        res.0.extend(other.0.into_iter());
        res
    }

    pub fn append(&self, label: Name) -> Self {
        let mut res = self.clone();
        res.0.push(label);
        res
    }

    // pub fn to_strings(&self, sources: &source::Sources) -> Vec<String> {
    //     self.0
    //         .iter()
    //         .map(|s| s.0.as_str(sources).to_owned())
    //         .collect()
    // }

    pub fn as_ref<'t>(&self, sources: &'t source::Sources) -> QualifiedNameRef<'t> {
        QualifiedNameRef(self.0.iter().map(|s| s.as_ref(sources)).collect())
    }
}
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct QualifiedNameRef<'t>(pub Vec<NameRef<'t>>);

impl <'t> std::fmt::Display for QualifiedNameRef<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (p, r) in self.0.iter().with_position() {
            match r {
                NameRef::User(s) => write!(f, "{}", s)?,
                NameRef::Generated(idx) => write!(f, "${}", idx)?,
            }
            match p {
                itertools::Position::First| 
                itertools::Position::Middle =>   {
                    write!(f, "::")?
                },
                itertools::Position::Last |
                itertools::Position::Only => {},
            }
        }
        Ok(())
    }
}


#[derive(Debug)]
pub struct Sentence {
    pub span: Span,
    pub name: QualifiedName,
    pub words: Vec<Word>,
}

#[derive(Debug, FromRawAst)]
#[from_raw_ast(raw = ast::Word)]
pub enum Word {
    StackBindings(StackBindings),
    Builtin(Builtin),
    ValueExpression(ValueExpression),
}

#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub path: QualifiedName,
}

impl<'t> FromRawAst<'t, ast::LabelCall<'t>> for Label {
    fn from_raw_ast(ctx: Context<'t>, r: ast::LabelCall<'t>) -> Self {
        Self {
            span: r.span.with_ctx(ctx).into(),
            path: ctx
                .name_prefix
                .join(QualifiedName(FromRawAst::from_raw_ast(ctx, r.path))),
        }
    }
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw=ast::StackBindings)]
pub struct StackBindings {
    pub span: Span,
    pub bindings: Vec<Binding>,
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::Binding)]
pub enum Binding {
    Drop(DropBinding),
    Tuple(TupleBinding),
    Literal(Literal),
    Identifier(Identifier),
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::DropBinding)]
pub struct DropBinding {
    pub span: Span,
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::TupleBinding)]

pub struct TupleBinding {
    pub span: Span,
    pub bindings: Vec<Binding>,
}

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

impl<'t> From<WithContext<'t, ast::Int<'t>>> for Int {
    fn from(WithContext(a, c): WithContext<'t, ast::Int<'t>>) -> Self {
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

impl<'t> From<WithContext<'t, ast::Symbol<'t>>> for Symbol {
    fn from(WithContext(a, c): WithContext<'t, ast::Symbol<'t>>) -> Self {
        match a {
            ast::Symbol::Identifier(a) => Self {
                span: a.0.with_ctx(c).into(),
                value: a.0.as_str().to_owned(),
            },
            ast::Symbol::String(a) => Self {
                span: a.span.with_ctx(c).into(),
                value: a.value,
            },
        }
    }
}

#[derive(Debug, FromRawAst)]
#[from_raw_ast(raw = ast::BuiltinArg)]
pub enum BuiltinArg {
    Int(Int),
    Label(Label),
}

#[derive(Debug, FromRawAst)]
#[from_raw_ast(raw = ast::Builtin)]
pub struct Builtin {
    pub span: Span,
    pub name: Identifier,
    pub args: Vec<BuiltinArg>,
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::Literal)]
pub enum Literal {
    Int(Int),
    Symbol(Symbol),
}

impl Literal {
    pub fn span(&self) -> Span {
        match self {
            Literal::Int(int) => int.span,
            Literal::Symbol(a) => a.span,
        }
    }
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::Tuple)]
pub struct Tuple {
    pub span: Span,
    pub values: Vec<ValueExpression>,
}

#[derive(Debug, Clone, FromRawAst)]
#[from_raw_ast(raw = ast::ValueExpression)]
pub enum ValueExpression {
    Literal(Literal),
    Copy(Identifier),
    Move(Identifier),
    Tuple(Tuple),
}

impl<'t> FromRawAst<'t, ast::Copy<'t>> for Identifier {
    fn from_raw_ast(ctx: Context<'t>, r: ast::Copy<'t>) -> Self {
        FromRawAst::from_raw_ast(ctx, r.0)
    }
}
