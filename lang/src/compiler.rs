use std::{
    collections::{BTreeMap, VecDeque},
    fmt::write,
};

use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    ast::{self, NamespaceDecl},
    flat::{self, SentenceIndex},
    linker::{self, Error},
    source::{self, FileIndex, FileSpan, Sources},
};
use from_raw_ast::FromRawAst;

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

pub struct Compiler<'t> {
    sources: &'t Sources,
    res: Crate,
}

impl<'t> Compiler<'t> {
    pub fn new(sources: &'t Sources) -> Self {
        Self {
            sources,
            res: Crate::default(),
        }
    }

    pub fn build(self) -> Crate {
        self.res
    }

    pub fn add_file(
        &mut self,
        name_prefix: QualifiedName,
        file_idx: FileIndex,
        file: ast::File,
    ) -> Result<(), linker::Error> {
        self.visit_namespace(file_idx, &name_prefix, file.ns)
    }

    fn visit_namespace(
        &mut self,
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        ns: ast::Namespace,
    ) -> Result<(), linker::Error> {
        for decl in ns.decl {
            let ctx = Context {
                file_idx,
                name_prefix: &name_prefix,
            };
            match decl {
                ast::Decl::SentenceDecl(sentence_decl) => {
                    self.visit_sentence(
                        file_idx,
                        name_prefix.append(sentence_decl.name.into_ir(self.sources, file_idx)),
                        sentence_decl.sentence,
                    )?;
                }
                ast::Decl::Namespace(NamespaceDecl { name, ns }) => {
                    let name_prefix = name_prefix.append(name.into_ir(self.sources, file_idx));
                    self.visit_namespace(file_idx, &name_prefix, ns)?;
                }
                ast::Decl::Proc(ast::ProcDecl {
                    span,
                    binding,
                    name,
                    expression,
                }) => {
                    let name = name_prefix.append(name.into_ir(self.sources, file_idx));
                    self.visit_proc(
                        span.into_ir(self.sources, file_idx),
                        file_idx,
                        &name_prefix,
                        binding,
                        name,
                        expression,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn visit_proc(
        &mut self,
        span: FileSpan,
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        binding: ast::Binding,
        name: QualifiedName,
        expression: ast::Expression,
    ) -> Result<(), linker::Error> {
        let mut names = NameSequence {
            base: name,
            count: 0,
        };
        let mut locals = VecDeque::new();
        self.visit_expr(file_idx, name_prefix, &mut names, &mut locals, expression)?;
        Ok(())
    }

    fn visit_expr(
        &mut self,
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        name_sequence: &mut NameSequence,
        locals: &mut VecDeque<Option<FileSpan>>,
        expression: ast::Expression,
    ) -> Result<QualifiedName, linker::Error> {
        match expression {
            ast::Expression::Literal(literal) => {
                let name = name_sequence.next();
                let mut b = SentenceBuilder::new(
                    literal.span(file_idx),
                    self.sources,
                    name.clone(),
                    locals.clone(),
                );
                b.literal(literal);
                *locals = b.names.clone();
                self.res.sentences.push(b.build());
                Ok(name)
            }
            ast::Expression::Tuple(t) => {
                let span = t.span(file_idx);
                let name = name_sequence.next();

                let mut b = SentenceBuilder::new(span, self.sources, name.clone(), locals.clone());
                let size = t.values.len();
                for v in t.values {
                    let span = v.span(file_idx);
                    let tc = self.visit_expr(file_idx, name_prefix, name_sequence, locals, v)?;
                    b.fully_qualified_call(span, tc)?;
                    b.names = locals.clone();
                }
                b.tuple(span, size);
                *locals = b.names.clone();
                self.res.sentences.push(b.build());

                Ok(name)
            }
        }
    }

    fn visit_sentence(
        &mut self,
        file_idx: FileIndex,
        name: QualifiedName,
        sentence: ast::Sentence,
    ) -> Result<(), linker::Error> {
        let mut next_name = 1;
        let words: Result<Vec<Word>, Error> = sentence
            .words
            .into_iter()
            .map(|w| self.visit_word(file_idx, w))
            .collect();

        self.res.sentences.push(Sentence {
            // span: sentence.span.into_ir(self.sources, file_idx),
            name: name.clone(),
            words: words?,
        });
        Ok(())
    }

    fn visit_word(&mut self, file_idx: FileIndex, op: ast::Word) -> Result<Word, Error> {
        match op {
            // ast::Word::StackBindings(stack_bindings) => {
            //     Word::StackBindings(FromRawAst::from_raw_ast(ctx, stack_bindings.into()))
            // }
            ast::Word::Builtin(builtin) => {
                Ok(Word {
                    span: builtin.span.into_ir(self.sources, file_idx),
                    inner: self.convert_builtin(file_idx, builtin)?,
                    names: VecDeque::new(),
                })
                // Word::Builtin(FromRawAst::from_raw_ast(ctx, builtin))},
            }
            ast::Word::Literal(literal) => todo!(), //Word::Literal(FromRawAst::from_raw_ast(ctx, literal)),
                                                    // ast::Word::Move(identifier) => Word::Move(FromRawAst::from_raw_ast(ctx, identifier)),
                                                    // ast::Word::Copy(copy) => Word::Copy(FromRawAst::from_raw_ast(ctx, copy)),
                                                    // ast::Word::Tuple(tuple) => Word::Tuple(Tuple {
                                                    //     span: tuple.span.into_ir(ctx),
                                                    //     values: tuple
                                                    //         .values
                                                    //         .into_iter()
                                                    //         .map(|o| {
                                                    //             let name_prefix = name_prefix.append(Name::Generated(*next_name));
                                                    //             *next_name += 1;
                                                    //             Label {
                                                    //                 span: o.span.into_ir(ctx),
                                                    //                 path: self.visit_sentence(ctx, &name_prefix, o),
                                                    //             }
                                                    //         })
                                                    //         .collect(),
                                                    // }),
        }
    }

    fn convert_builtin(
        &self,
        file_idx: FileIndex,
        builtin: ast::Builtin,
    ) -> Result<InnerWord, linker::Error> {
        let name = builtin.name.0.as_str();
        if builtin.args.is_empty() {
            if let Some(b) = flat::Builtin::ALL.iter().find(|b| b.name() == name) {
                Ok(InnerWord::Builtin(*b))
            } else {
                Err(Error::UnknownBuiltin {
                    location: builtin.span.into_ir(self.sources, file_idx),
                    name: name.to_owned(),
                })
            }
        } else {
            match name {
                "cp" => self.convert_single_int_builtin(InnerWord::Copy, file_idx, builtin),
                "drop" => self.convert_single_int_builtin(InnerWord::Drop, file_idx, builtin),
                "mv" => self.convert_single_int_builtin(InnerWord::Move, file_idx, builtin),
                "tuple" => self.convert_single_int_builtin(InnerWord::Tuple, file_idx, builtin),
                "untuple" => self.convert_single_int_builtin(InnerWord::Untuple, file_idx, builtin),
                "branch" => {
                    let Some((
                        ast::BuiltinArg::Label(true_case),
                        ast::BuiltinArg::Label(false_case),
                    )) = builtin.args.into_iter().collect_tuple()
                    else {
                        return Err(Error::IncorrectBuiltinArguments {
                            location: builtin.span.into_ir(self.sources, file_idx),
                            name: name.to_owned(),
                        });
                    };

                    Ok(InnerWord::Branch(
                        true_case.into_ir(self.sources, file_idx),
                        false_case.into_ir(self.sources, file_idx),
                    ))
                }
                "call" => {
                    let Ok(ast::BuiltinArg::Label(label)) = builtin.args.into_iter().exactly_one()
                    else {
                        return Err(Error::IncorrectBuiltinArguments {
                            location: builtin.span.into_ir(self.sources, file_idx),
                            name: name.to_owned(),
                        });
                    };

                    Ok(InnerWord::Call(label.into_ir(self.sources, file_idx)))
                }
                _ => Err(Error::UnknownBuiltin {
                    location: builtin.span.into_ir(self.sources, file_idx),
                    name: name.to_owned(),
                }),
            }
        }
    }

    fn convert_single_int_builtin(
        &self,
        f: impl FnOnce(usize) -> InnerWord,
        file_idx: FileIndex,
        builtin: ast::Builtin,
    ) -> Result<InnerWord, Error> {
        let Ok(ast::BuiltinArg::Int(ast::Int { value: size, .. })) =
            builtin.args.into_iter().exactly_one()
        else {
            return Err(Error::IncorrectBuiltinArguments {
                location: builtin.span.into_ir(self.sources, file_idx),
                name: builtin.name.0.as_str().to_owned(),
            });
        };
        Ok(f(size))
    }
}

#[derive(Debug, Clone)]
pub struct Word {
    pub span: FileSpan,
    pub inner: InnerWord,
    pub names: VecDeque<Option<FileSpan>>,
}

impl Word {}

#[derive(Debug, Clone)]
pub enum InnerWord {
    Push(flat::Value),
    Builtin(flat::Builtin),
    Copy(usize),
    Drop(usize),
    Move(usize),
    Tuple(usize),
    Untuple(usize),
    Call(QualifiedName),
    Branch(QualifiedName, QualifiedName),
}

pub trait FromRawAst<'t, R> {
    fn from_raw_ast(ctx: Context<'t>, r: R) -> Self;
}

pub trait IntoIr<'t, I> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> I;
}

impl<'t> IntoIr<'t, source::FileSpan> for pest::Span<'_> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> source::FileSpan {
        source::FileSpan::from_ast(file_idx, self)
    }
}
impl<'t> IntoIr<'t, source::Location> for pest::Span<'_> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> source::Location {
        source::FileSpan::from_ast(file_idx, self).location(sources)
    }
}

// impl<'t, I, R> IntoIr<'t, I> for R
// where
//     I: FromRawAst<'t, R>,
// {
//     fn into_ir(self, file_idx: FileIndex) -> I {
//         I::from_raw_ast(ctx, self)
//     }
// }

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

// impl<'t> Into<FileSpan> for WithContext<'t, pest::Span<'t>> {
//     fn into(self) -> FileSpan {
//         FileSpan::File(source::FileSpan {
//             file_idx: self.1.file_idx,
//             start: self.0.start(),
//             end: self.0.end(),
//         })
//     }
// }

// impl<'t> FromRawAst<'t, pest::Span<'t>> for FileSpan {
//     fn from_raw_ast(ctx: Context<'t>, r: pest::Span<'t>) -> Self {
//         FileSpan::File(source::FileSpan {
//             file_idx: ctx.file_idx,
//             start: r.start(),
//             end: r.end(),
//         })
//     }
// }

impl<'t, X, T> FromRawAst<'t, X> for T
where
    T: From<WithContext<'t, X>>,
{
    fn from_raw_ast(ctx: Context<'t>, r: X) -> Self {
        r.with_ctx(ctx).into()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Identifier(pub FileSpan);

#[derive(Debug, Clone, Copy)]
pub enum Name {
    User(FileSpan),
    Generated(usize),
}

impl Name {
    pub fn as_str<'t>(self, sources: &'t source::Sources) -> Option<&'t str> {
        match self {
            Name::User(id) => Some(id.as_str(sources)),
            Name::Generated(_) => None,
        }
    }

    pub fn as_ref<'t>(self, sources: &'t source::Sources) -> NameRef<'t> {
        match self {
            Name::User(id) => NameRef::User(id.as_str(sources)),
            Name::Generated(id) => NameRef::Generated(id),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NameRef<'t> {
    User(&'t str),
    Generated(usize),
}

impl<'t> NameRef<'t> {
    pub fn as_str(self) -> Option<&'t str> {
        match self {
            NameRef::User(s) => Some(s),
            NameRef::Generated(_) => None,
        }
    }
}

// impl<'t> FromRawAst<'t, ast::Identifier<'t>> for Name {
//     fn from_raw_ast(ctx: Context<'t>, r: ast::Identifier<'t>) -> Self {
//         Name::User(Identifier::from_raw_ast(ctx, r))
//     }
// }

impl<'t> IntoIr<'t, Name> for ast::Identifier<'t> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> Name {
        Name::User(self.0.into_ir(sources, file_idx))
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

impl<'t> std::fmt::Display for QualifiedNameRef<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (p, r) in self.0.iter().with_position() {
            match r {
                NameRef::User(s) => write!(f, "{}", s)?,
                NameRef::Generated(idx) => write!(f, "${}", idx)?,
            }
            match p {
                itertools::Position::First | itertools::Position::Middle => write!(f, "::")?,
                itertools::Position::Last | itertools::Position::Only => {}
            }
        }
        Ok(())
    }
}

impl<'t> IntoIr<'t, QualifiedName> for ast::QualifiedLabel<'_> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> QualifiedName {
        QualifiedName(
            self.path
                .into_iter()
                .map(|n| n.into_ir(sources, file_idx))
                .collect(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct Sentence {
    // pub span: FileSpan,
    pub name: QualifiedName,
    pub words: Vec<Word>,
}

struct NameSequence {
    base: QualifiedName,
    count: usize,
}

impl NameSequence {
    fn next(&mut self) -> QualifiedName {
        let res = self.base.append(Name::Generated(self.count));
        self.count += 1;
        res
    }
}

// #[derive(Debug, Clone)]
// pub struct Label {
//     pub span: FileSpan,
//     pub path: QualifiedName,
// }

// impl<'t> FromRawAst<'t, ast::QualifiedLabel<'t>> for Label {
//     fn from_raw_ast(ctx: Context<'t>, r: ast::QualifiedLabel<'t>) -> Self {
//         Self {
//             span: r.span.with_ctx(ctx).into(),
//             path: ctx
//                 .name_prefix
//                 .join(QualifiedName(FromRawAst::from_raw_ast(ctx, r.path))),
//         }
//     }
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw=ast::StackBindings)]
// pub struct StackBindings {
//     pub span: FileSpan,
//     pub bindings: Vec<Binding>,
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::Binding)]
// pub enum Binding {
//     Drop(DropBinding),
//     Tuple(TupleBinding),
//     Literal(Literal),
//     Identifier(Identifier),
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::DropBinding)]
// pub struct DropBinding {
//     pub span: FileSpan,
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::TupleBinding)]

// pub struct TupleBinding {
//     pub span: FileSpan,
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
    pub span: FileSpan,
    pub value: usize,
}

// impl<'t> From<WithContext<'t, ast::Int<'t>>> for Int {
//     fn from(WithContext(a, c): WithContext<'t, ast::Int<'t>>) -> Self {
//         Self {
//             span: a.span.with_ctx(c).into(),
//             value: a.value,
//         }
//     }
// }

#[derive(Debug, Clone)]
pub struct Symbol {
    pub span: FileSpan,
    pub value: String,
}

// impl<'t> From<WithContext<'t, ast::Symbol<'t>>> for Symbol {
//     fn from(WithContext(a, c): WithContext<'t, ast::Symbol<'t>>) -> Self {
//         match a {
//             ast::Symbol::Identifier(a) => Self {
//                 span: a.0.with_ctx(c).into(),
//                 value: a.0.as_str().to_owned(),
//             },
//             ast::Symbol::String(a) => Self {
//                 span: a.span.with_ctx(c).into(),
//                 value: a.value,
//             },
//         }
//     }
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::BuiltinArg)]
// pub enum BuiltinArg {
//     Int(Int),
//     Label(Label),
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::Builtin)]
// pub struct Builtin {
//     pub span: FileSpan,
//     pub name: Identifier,
//     pub args: Vec<BuiltinArg>,
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::Literal)]
// pub enum Literal {
//     Int(Int),
//     Symbol(Symbol),
// }

// impl Literal {
//     pub fn span(&self) -> FileSpan {
//         match self {
//             Literal::Int(int) => int.span,
//             Literal::Symbol(a) => a.span,
//         }
//     }
// }

// #[derive(Debug, Clone)]
// pub struct Tuple {
//     pub span: FileSpan,
//     pub values: Vec<Label>,
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::ValueExpression)]
// pub enum ValueExpression {
//     Literal(Literal),
//     Copy(Identifier),
//     Move(Identifier),
//     Tuple(Tuple),
// }

// impl<'t> FromRawAst<'t, ast::Copy<'t>> for Identifier {
//     fn from_raw_ast(ctx: Context<'t>, r: ast::Copy<'t>) -> Self {
//         FromRawAst::from_raw_ast(ctx, r.0)
//     }
// }

// #[derive(Debug, Clone)]
// #[from_raw_ast(raw = ast::ProcDecl)]
// pub struct ProcDecl {
//     pub span: FileSpan,
//     pub binding: Binding,
//     pub name: Identifier,
//     pub expression: Expression,
// }

// #[derive(Debug, Clone, FromRawAst)]
// #[from_raw_ast(raw = ast::ValueExpression)]
// pub enum ValueExpression {
//     Literal(Literal),
//     Copy(Identifier),
//     Move(Identifier),
//     Tuple(Tuple),
// }

pub struct SentenceBuilder<'a> {
    pub span: FileSpan,
    pub name: QualifiedName,
    pub sources: &'a source::Sources,
    pub names: VecDeque<Option<FileSpan>>,
    pub words: Vec<Word>,
}

impl<'a> SentenceBuilder<'a> {
    pub fn new(
        span: FileSpan,
        sources: &'a source::Sources,
        name: QualifiedName,
        names: VecDeque<Option<FileSpan>>,
    ) -> Self {
        Self {
            span,
            name,
            sources,
            names,
            words: vec![],
        }
    }

    pub fn build(self) -> Sentence {
        Sentence {
            // span: self.span,
            name: self.name,
            words: self.words,
        }
    }

    // pub fn literal(&mut self, literal: Literal) {
    //     self.literal_split(literal.span, literal.value)
    // }

    pub fn literal(&mut self, value: ast::Literal) {
        let span = value.span(self.span.file_idx);
        match value {
            ast::Literal::Int(ast::Int { span: _, value }) => {
                self.push_value(span, flat::Value::Usize(value))
            }
            ast::Literal::Symbol(sym) => match sym {
                ast::Symbol::Identifier(identifier) => {
                    self.push_value(span, flat::Value::Symbol(identifier.0.as_str().to_owned()))
                }
                ast::Symbol::String(string_literal) => {
                    self.push_value(span, flat::Value::Symbol(string_literal.value))
                }
            },
        }
    }

    pub fn push_value(&mut self, span: FileSpan, value: flat::Value) {
        self.words.push(Word {
            span,
            inner: InnerWord::Push(value),
            names: self.names.clone(),
        });
        self.names.push_front(None);
    }

    // pub fn mv(&mut self, ident: ir::Identifier) -> Result<(), Error> {
    //     let name = ident.0.as_str(self.sources);
    //     let Some(idx) = self.names.iter().position(|n| match n {
    //         Some(n) => n.as_str() == name,
    //         None => false,
    //     }) else {
    //         return Err(Error::UnknownReference {
    //             location: ident.0.location(self.sources).unwrap(),
    //             name: name.to_owned(),
    //         });
    //     };
    //     Ok(self.mv_idx(ident.0, idx))
    // }

    // pub fn mv_idx(&mut self, span: FileSpan, idx: usize) {
    //     let names = self.names.clone();
    //     let declared = self.names.remove(idx).unwrap();
    //     self.names.push_front(declared);

    //     self.words.push(flat::Word {
    //         inner: flat::InnerWord::Move(idx),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // pub fn cp(&mut self, i: ir::Identifier) -> Result<(), Error> {
    //     let name = i.0.as_str(&self.sources);
    //     let Some(idx) = self.names.iter().position(|n| match n {
    //         Some(n) => n.as_str() == name,
    //         None => false,
    //     }) else {
    //         return Err(Error::UnknownReference {
    //             location: i.0.location(self.sources).unwrap(),
    //             name: name.to_owned(),
    //         });
    //     };
    //     Ok(self.cp_idx(i.0, idx))
    // }

    // pub fn cp_idx(&mut self, span: FileSpan, idx: usize) {
    //     let names = self.names.clone();
    //     self.names.push_front(None);

    //     self.words.push(flat::Word {
    //         inner: flat::InnerWord::Copy(idx),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // // pub fn sd_idx(&mut self, span: FileSpan<'t>, idx: usize) {
    // //     let names = self.names.clone();

    // //     let declared = self.names.pop_front().unwrap();
    // //     self.names.insert(idx, declared);

    // //     self.words.push(Word {
    // //         inner: InnerWord::Send(idx),
    // //         modname: self.modname.clone(),
    // //         span,
    // //         names: Some(names),
    // //     });
    // // }
    // // pub fn sd_top(&mut self, span: FileSpan<'t>) {
    // //     self.sd_idx(span, self.names.len() - 1)
    // // }

    // pub fn drop_idx(&mut self, span: FileSpan, idx: usize) {
    //     let names = self.names.clone();
    //     let declared = self.names.remove(idx).unwrap();

    //     self.words.push(flat::Word {
    //         inner: flat::InnerWord::Drop(idx),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // // pub fn path(&mut self, ast::Path { span, segments }: ast::Path<'t>) {
    // //     for segment in segments.iter().rev() {
    // //         self.literal_split(*segment, Value::Symbol(segment.as_str().to_owned()));
    // //     }
    // //     self.literal_split(span, Value::Namespace(self.ns_idx));
    // //     for segment in segments {
    // //         self.builtin(segment, Builtin::Get);
    // //     }
    // // }

    // pub fn ir_builtin(&mut self, builtin: ir::Builtin) -> Result<(), Error> {
    //     let name = builtin.name.0.as_str(self.sources);
    //     if builtin.args.is_empty() {
    //         if let Some(b) = flat::Builtin::ALL.iter().find(|b| b.name() == name) {
    //             self.builtin(builtin.span, *b);
    //             Ok(())
    //         } else {
    //             Err(Error::UnknownBuiltin {
    //                 location: builtin.span.location(self.sources).unwrap(),
    //                 name: name.to_owned(),
    //             })
    //         }
    //     } else {
    //         match name {
    //             "untuple" => {
    //                 let Ok(ir::BuiltinArg::Int(ir::Int { value: size, .. })) =
    //                     builtin.args.into_iter().exactly_one()
    //                 else {
    //                     return Err(Error::IncorrectBuiltinArguments {
    //                         location: builtin.span.location(self.sources).unwrap(),
    //                         name: name.to_owned(),
    //                     });
    //                 };

    //                 self.untuple(builtin.span, size);
    //                 Ok(())
    //             }
    //             "branch" => {
    //                 let Some((ir::BuiltinArg::Label(true_case), ir::BuiltinArg::Label(false_case))) =
    //                     builtin.args.into_iter().collect_tuple()
    //                 else {
    //                     return Err(Error::IncorrectBuiltinArguments {
    //                         location: builtin.span.location(self.sources).unwrap(),
    //                         name: name.to_owned(),
    //                     });
    //                 };

    //                 let true_case = self.lookup_label(&true_case)?;
    //                 let false_case = self.lookup_label(&false_case)?;

    //                 let names = self.names.clone();
    //                 self.names.pop_front();
    //                 self.words.push(flat::Word {
    //                     inner: flat::InnerWord::Branch(true_case, false_case),
    //                     span: builtin.span,
    //                     names: Some(names),
    //                 });
    //                 Ok(())
    //             }
    //             "call" => {
    //                 let Ok(ir::BuiltinArg::Label(label)) = builtin.args.into_iter().exactly_one()
    //                 else {
    //                     return Err(Error::IncorrectBuiltinArguments {
    //                         location: builtin.span.location(self.sources).unwrap(),
    //                         name: name.to_owned(),
    //                     });
    //                 };

    //                 self.label_call(label)?;
    //                 Ok(())
    //             }
    //             _ => Err(Error::UnknownBuiltin {
    //                 location: builtin.span.location(self.sources).unwrap(),
    //                 name: name.to_owned(),
    //             }),
    //         }
    //     }
    // }

    // pub fn builtin(&mut self, span: FileSpan, builtin: flat::Builtin) {
    //     self.words.push(flat::Word {
    //         span,
    //         inner: flat::InnerWord::Builtin(builtin),
    //         names: Some(self.names.clone()),
    //     });
    //     match builtin {
    //         flat::Builtin::Add
    //         | flat::Builtin::Eq
    //         | flat::Builtin::Curry
    //         | flat::Builtin::Prod
    //         | flat::Builtin::Lt
    //         | flat::Builtin::Or
    //         | flat::Builtin::And
    //         | flat::Builtin::Sub
    //         | flat::Builtin::Get
    //         | flat::Builtin::SymbolCharAt
    //         | flat::Builtin::Cons => {
    //             self.names.pop_front();
    //             self.names.pop_front();
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::NsEmpty => {
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::NsGet => {
    //             let ns = self.names.pop_front().unwrap();
    //             self.names.pop_front();
    //             self.names.push_front(ns);
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::NsInsert | flat::Builtin::If => {
    //             self.names.pop_front();
    //             self.names.pop_front();
    //             self.names.pop_front();
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::NsRemove => {
    //             let ns = self.names.pop_front().unwrap();
    //             self.names.pop_front();
    //             self.names.push_front(ns);
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::Not
    //         | flat::Builtin::SymbolLen
    //         | flat::Builtin::Deref
    //         | flat::Builtin::Ord => {
    //             self.names.pop_front();
    //             self.names.push_front(None);
    //         }
    //         flat::Builtin::AssertEq => {
    //             self.names.pop_front();
    //             self.names.pop_front();
    //         }
    //         flat::Builtin::Snoc => {
    //             self.names.pop_front();
    //             self.names.push_front(None);
    //             self.names.push_front(None);
    //         }
    //     }
    // }

    fn fully_qualified_call(&mut self, span: FileSpan, name: QualifiedName) -> Result<(), Error> {
        self.words.push(Word {
            span,
            inner: InnerWord::Call(name),
            names: self.names.clone(),
        });
        Ok(())
    }

    // fn normalize_path(&self, mut path: QualifiedName) -> QualifiedNameRef<'a> {
    //     loop {
    //         let Some(super_idx) = path
    //             .0
    //             .iter()
    //             .position(|n| n.as_ref(&self.sources) == NameRef::User("super"))
    //         else {
    //             return path.as_ref(self.sources);
    //         };
    //         path.0.remove(super_idx - 1);
    //         path.0.remove(super_idx - 1);
    //     }
    // }

    // fn lookup_label(&self, l: &ir::Label) -> Result<SentenceIndex, Error> {
    //     let sentence_key = self.normalize_path(l.path.clone());
    //     self.sentence_index
    //         .get(&sentence_key)
    //         .ok_or_else(|| Error::LabelNotFound {
    //             location: l.span.location(self.sources).unwrap(),
    //             name: sentence_key.to_string(),
    //         })
    //         .copied()
    // }

    pub fn tuple(&mut self, span: FileSpan, size: usize) {
        self.words.push(Word {
            inner: InnerWord::Tuple(size),
            span: span,
            names: self.names.clone(),
        });
        for _ in 0..size {
            self.names.pop_front().unwrap();
        }
        self.names.push_front(None);
    }

    // pub fn untuple(&mut self, span: FileSpan, size: usize) {
    //     self.words.push(flat::Word {
    //         inner: flat::InnerWord::Untuple(size),
    //         span: span,
    //         names: Some(self.names.clone()),
    //     });
    //     self.names.pop_front();
    //     for _ in 0..size {
    //         self.names.push_front(None);
    //     }
    // }

    // // fn func_call(&mut self, call: ast::Call<'t>) -> Result<usize, BuilderError<'t>> {
    // //     let argc = call.args.len();

    // //     for arg in call.args.into_iter().rev() {
    // //         self.value_expr(arg)?;
    // //     }

    // //     match call.func {
    // //         ast::PathOrIdent::Path(p) => self.path(p),
    // //         ast::PathOrIdent::Ident(i) => self.mv(i)?,
    // //     }
    // //     Ok(argc)
    // // }

    // // fn value_expr(&mut self, expr: ir::ValueExpression) -> Result<(), Error> {
    // //     match expr {
    // //         ir::ValueExpression::Literal(literal) => Ok(self.literal(literal)),
    // //         ir::ValueExpression::Tuple(tuple) => {
    // //             let num_values = tuple.values.len();
    // //             for v in tuple.values {
    // //                 self.value_expr(v)?;
    // //             }
    // //             self.tuple(tuple.span, num_values);
    // //             Ok(())
    // //         } // ValueExpression::Path(path) => Ok(self.path(path)),
    // //         ir::ValueExpression::Move(identifier) => self.mv(identifier),
    // //         ir::ValueExpression::Copy(identifier) => self.cp(identifier),
    // //         // ValueExpression::Closure { span, func, args } => {
    // //         //     let argc = args.len();
    // //         //     for arg in args.into_iter().rev() {
    // //         //         self.value_expr(arg)?;
    // //         //     }
    // //         //     match func {
    // //         //         ast::PathOrIdent::Path(p) => self.path(p),
    // //         //         ast::PathOrIdent::Ident(i) => self.mv(i)?,
    // //         //     }
    // //         //     for _ in 0..argc {
    // //         //         self.builtin(span, Builtin::Curry);
    // //         //     }
    // //         //     Ok(())
    // //         // }
    // //     }
    // // }

    // fn bindings(&mut self, b: StackBindings) {
    //     self.names = b
    //         .bindings
    //         .iter()
    //         .rev()
    //         .map(|b| match b {
    //             Binding::Literal(_) | &Binding::Drop(_) => None,
    //             Binding::Identifier(span) => Some(span.0.as_str(self.sources).to_owned()),
    //             Binding::Tuple(tuple_binding) => todo!(),
    //         })
    //         .collect();
    //     let mut dropped = 0;
    //     for (idx, binding) in b.bindings.into_iter().rev().enumerate() {
    //         match binding {
    //             Binding::Literal(l) => {
    //                 let span = l.span();
    //                 self.mv_idx(span, idx - dropped);
    //                 self.literal(l);
    //                 self.builtin(span, flat::Builtin::AssertEq);
    //                 dropped += 1;
    //             }
    //             Binding::Drop(drop) => {
    //                 self.drop_idx(drop.span, idx - dropped);
    //                 dropped += 1;
    //             }
    //             Binding::Identifier(_) => {},
    //             Binding::Tuple(_) => {},
    //         }
    //     }
    // }
}
