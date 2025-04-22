use std::{
    collections::{BTreeMap, VecDeque},
    fmt::{write, Write},
};

use crate::ast::Spanner;
use builder::{FileContext, Output};
use itertools::{Itertools, Position};
use typed_index_collections::TiVec;

use crate::{
    ast::{self, NamespaceDecl},
    flat::{self, SentenceIndex},
    linker::{self, Error},
    source::{self, FileIndex, FileSpan, Sources},
};

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

pub struct Compiler<'t> {
    sources: &'t Sources,
    res: Crate,
}

// pub enum Phrase<'t> {
//     Expression(ast::Expression<'t>),
//     Binding(ast::Binding<'t>),
// }

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
                        name_prefix
                            .append(sentence_decl.name.into_ir(self.sources, file_idx))
                            .append(Name::Generated(0)),
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
        let expression = Expression::from_ast(expression);
        let span = expression.span(file_idx);

        let mut out = Output {
            words: vec![],
            locals: Locals::default(),
        };
        out.locals.push_unnamed();
        let ctx = FileContext {
            file_idx,
            sources: self.sources,
        };
        let () = builder::binding(ctx, binding, &mut out)?;

        let () = expression.compilation(ctx, name_prefix, &mut out)?;

        if out.locals.len() != 1 {
            let Name::User(name) = out.locals.names()[1] else {
                panic!("unused generated name?")
            };
            return Err(Error::UnusedVariable {
                location: name.location(self.sources),
                name: name.as_str(self.sources).to_owned(),
            });
        }

        let sentence = RecursiveSentence {
            span,
            words: out.words,
        };

        let mut names = NameSequence {
            base: name,
            count: 0,
        };
        self.visit_recursive_sentence(&mut names, sentence);
        Ok(())
    }

    fn visit_sentence(
        &mut self,
        file_idx: FileIndex,
        name: QualifiedName,
        sentence: ast::Sentence,
    ) -> Result<(), linker::Error> {
        let span = sentence.span(file_idx);
        let words: Result<Vec<Word>, Error> = sentence
            .words
            .into_iter()
            .map(|w| self.visit_word(file_idx, w))
            .collect();

        self.res.sentences.push(Sentence {
            span,
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
                    names: vec![],
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

    fn convert_builtin<BranchRepr>(
        &self,
        file_idx: FileIndex,
        builtin: ast::Builtin,
    ) -> Result<InnerWord<BranchRepr>, linker::Error> {
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
                    todo!()
                    // let Some((
                    //     ast::BuiltinArg::Label(true_case),
                    //     ast::BuiltinArg::Label(false_case),
                    // )) = builtin.args.into_iter().collect_tuple()
                    // else {
                    //     return Err(Error::IncorrectBuiltinArguments {
                    //         location: builtin.span.into_ir(self.sources, file_idx),
                    //         name: name.to_owned(),
                    //     });
                    // };

                    // Ok(InnerWord::Branch(
                    //     true_case.into_ir(self.sources, file_idx),
                    //     false_case.into_ir(self.sources, file_idx),
                    // ))
                }
                "call" => {
                    let Ok(ast::BuiltinArg::Label(label)) = builtin.args.into_iter().exactly_one()
                    else {
                        return Err(Error::IncorrectBuiltinArguments {
                            location: builtin.span.into_ir(self.sources, file_idx),
                            name: name.to_owned(),
                        });
                    };

                    Ok(InnerWord::Call(
                        label
                            .into_ir(self.sources, file_idx)
                            .append(Name::Generated(0)),
                    ))
                }
                _ => Err(Error::UnknownBuiltin {
                    location: builtin.span.into_ir(self.sources, file_idx),
                    name: name.to_owned(),
                }),
            }
        }
    }

    fn convert_single_int_builtin<BranchRepr>(
        &self,
        f: impl FnOnce(usize) -> InnerWord<BranchRepr>,
        file_idx: FileIndex,
        builtin: ast::Builtin,
    ) -> Result<InnerWord<BranchRepr>, Error> {
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

    fn visit_recursive_sentence(
        &mut self,
        names: &mut NameSequence,
        sentence: RecursiveSentence,
    ) -> QualifiedName {
        let res = names.next();
        let words = sentence
            .words
            .into_iter()
            .map(|w| self.visit_recursive_word(names, w))
            .collect();
        self.res.sentences.push(Sentence {
            span: sentence.span,
            name: res.clone(),
            words,
        });
        res
    }

    fn visit_recursive_word(&mut self, names: &mut NameSequence, word: RecursiveWord) -> Word {
        let new_inner = match word.inner {
            InnerWord::Push(value) => InnerWord::Push(value),
            InnerWord::Builtin(builtin) => InnerWord::Builtin(builtin),
            InnerWord::Copy(idx) => InnerWord::Copy(idx),
            InnerWord::Drop(idx) => InnerWord::Drop(idx),
            InnerWord::Move(idx) => InnerWord::Move(idx),
            InnerWord::Tuple(idx) => InnerWord::Tuple(idx),
            InnerWord::Untuple(idx) => InnerWord::Untuple(idx),
            InnerWord::Call(qualified_name) => InnerWord::Call(qualified_name),
            InnerWord::Branch(true_case, false_case) => InnerWord::Branch(
                self.visit_recursive_sentence(names, true_case),
                self.visit_recursive_sentence(names, false_case),
            ),
        };

        Word {
            span: word.span,
            inner: new_inner,
            names: word.names,
        }
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Locals {
    terminal: bool,
    num_generated: usize,
    scope: usize,
    stack: Vec<(usize, Name)>,
}

impl Locals {
    fn pop(&mut self) -> Name {
        assert!(!self.terminal);
        let (_, name) = self.stack.pop().unwrap();
        name
    }

    fn names(&self) -> Vec<Name> {
        assert!(!self.terminal);

        self.stack
            .iter()
            .cloned()
            .map(|(scope, name)| name)
            .rev()
            .collect()
    }

    fn len(&self) -> usize {
        assert!(!self.terminal);
        self.stack.len()
    }

    fn push_unnamed(&mut self) -> Name {
        assert!(!self.terminal);
        let name = Name::Generated(self.num_generated);
        self.stack.push((self.scope, name));
        self.num_generated += 1;
        name
    }

    fn push_scope(&mut self) -> usize {
        assert!(!self.terminal);
        self.scope += 1;
        self.scope
    }

    fn collapse_scope(&mut self) {
        assert!(!self.terminal);
        assert!(!self.stack.iter().any(|(s, n)| *s == self.scope - 1));
        for (s, n) in self.stack.iter_mut() {
            if *s == self.scope {
                *s -= 1;
            }
        }
        self.scope -= 1
    }

    fn push_named(&mut self, name: FileSpan) {
        assert!(!self.terminal);
        self.stack.push((self.scope, Name::User(name)))
    }

    fn check_consumed(&mut self, sources: &Sources, name: FileSpan) -> Result<(), Error> {
        assert!(!self.terminal);
        if self.stack.iter().any(|(_, n)| match n {
            Name::Generated(_) => false,
            Name::User(n) => *n == name,
        }) {
            Err(Error::UnusedVariable {
                location: name.location(sources),
                name: name.as_str(sources).to_owned(),
            })
        } else {
            Ok(())
        }
    }

    fn prev_scope(&self) -> Vec<Name> {
        assert!(!self.terminal);
        self.stack
            .iter()
            .filter_map(|(s, n)| {
                if *s == self.scope - 1 {
                    Some(n.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    fn remove(&mut self, idx: usize) {
        assert!(!self.terminal);
        self.stack.remove(self.stack.len() - idx - 1);
    }

    fn find(&self, sources: &Sources, name: Name) -> Option<usize> {
        assert!(!self.terminal);
        let pos = self
            .stack
            .iter()
            .position(|(s, n)| n.as_ref(sources) == name.as_ref(sources))?;
        Some(self.stack.len() - pos - 1)
    }

    fn compare(&self, sources: &Sources, other: &Self) -> bool {
        if self.terminal || other.terminal {
            return true;
        }

        if self.stack.len() != other.stack.len() {
            return false;
        }
        for ((_, n1), (_, n2)) in self.stack.iter().zip_eq(other.stack.iter()) {
            match (n1, n2) {
                (Name::Generated(_), Name::Generated(_)) => continue,
                (Name::User(n1), Name::User(n2)) => {
                    if n1.as_str(sources) != n2.as_str(sources) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn display<'a>(&'a self, sources: &'a source::Sources) -> LocalsDisplay<'a> {
        LocalsDisplay {
            sources,
            locals: self,
        }
    }
}

struct LocalsDisplay<'t> {
    sources: &'t Sources,
    locals: &'t Locals,
}

impl<'t> std::fmt::Debug for LocalsDisplay<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.locals.terminal {
            f.debug_struct("Locals").field("terminal", &true).finish()
        } else {
            f.debug_struct("Locals")
                .field(
                    "stack",
                    &self
                        .locals
                        .stack
                        .iter()
                        .map(|(_, n)| n.as_ref(self.sources))
                        .collect_vec(),
                )
                .finish()
        }
    }
}

#[derive(Debug)]
pub enum Expression<'t> {
    Literal(ast::Literal<'t>),
    Identifier(ast::Identifier<'t>),
    Copy(ast::Identifier<'t>),
    LetBlock {
        span: pest::Span<'t>,
        binding: ast::Binding<'t>,
        rhs: Box<Expression<'t>>,
        inner: Box<Expression<'t>>,
    },
    Tuple {
        span: pest::Span<'t>,
        values: Vec<Expression<'t>>,
    },
    Call {
        span: pest::Span<'t>,
        arg: Box<Expression<'t>>,
        label: ast::QualifiedLabel<'t>,
    },
    Match {
        span: pest::Span<'t>,
        arg: Box<Expression<'t>>,
        cases: Vec<MatchCase<'t>>,
    },
    If {
        span: pest::Span<'t>,
        cond: Box<Expression<'t>>,
        true_case: Box<Expression<'t>>,
        false_case: Box<Expression<'t>>,
    },
}

#[derive(Debug)]
pub struct MatchCase<'t> {
    span: pest::Span<'t>,
    binding: ast::Binding<'t>,
    rhs: Expression<'t>,
}

impl<'t> Expression<'t> {
    pub fn from_ast(mut a: ast::Expression<'t>) -> Self {
        match a.transformers.pop() {
            Some(ast::Transformer::Call(label)) => Self::Call {
                span: a.span,
                label,
                arg: Box::new(Self::from_ast(a)),
            },
            Some(ast::Transformer::Match(m)) => Self::Match {
                span: m.span,
                arg: Box::new(Self::from_ast(a)),
                cases: m
                    .cases
                    .into_iter()
                    .map(|c| MatchCase {
                        span: c.span,
                        binding: c.binding,
                        rhs: Expression::from_ast(c.rhs),
                    })
                    .collect(),
            },
            Some(ast::Transformer::If(if_)) => Self::If {
                span: if_.span,
                cond: Box::new(Self::from_ast(a)),
                true_case: Box::new(Expression::from_ast(*if_.true_case)),
                false_case: Box::new(Expression::from_ast(*if_.false_case)),
            },
            None => Self::from_ast_root(a.root),
        }
    }

    fn from_ast_root(a: ast::RootExpression<'t>) -> Self {
        match a {
            ast::RootExpression::Literal(literal) => Self::Literal(literal),
            ast::RootExpression::Tuple(tuple) => Self::Tuple {
                span: tuple.span,
                values: tuple.values.into_iter().map(Expression::from_ast).collect(),
            },
            ast::RootExpression::Block(mut block) => {
                if block.statements.is_empty() {
                    Self::from_ast(*block.expression)
                } else {
                    let ast::Statement::Let(s) = block.statements.remove(0);
                    Self::LetBlock {
                        span: block.span,
                        binding: s.binding,
                        rhs: Box::new(Self::from_ast(s.rhs)),
                        inner: Box::new(Self::from_ast_root(ast::RootExpression::Block(block))),
                    }
                }
            }
            ast::RootExpression::Identifier(identifier) => Self::Identifier(identifier),
            ast::RootExpression::Copy(copy) => Self::Copy(copy.0),
        }
    }

    fn compilation(
        self,
        ctx: FileContext,
        name_prefix: &QualifiedName,
        out: &mut Output,
    ) -> Result<(), Error> {
        match self {
            Expression::Literal(literal) => {
                builder::literal(ctx, literal, out);
                Ok(())
            }
            Expression::Identifier(id) => builder::mv_ident(ctx, id, out),
            Expression::Copy(id) => builder::cp_ident(ctx, id, out),
            Expression::LetBlock {
                span,
                binding,
                rhs,
                inner,
            } => {
                let () = rhs.compilation(ctx, name_prefix, out)?;

                let () = builder::binding(ctx, binding, out)?;

                let () = inner.compilation(ctx, name_prefix, out)?;
                // TODO: Check scope leakage?
                Ok(())
            }
            Expression::Tuple { span, values } => {
                let span = span.span(ctx.file_idx);

                let len = values.len();
                for v in values {
                    let () = v.compilation(ctx, name_prefix, out)?;
                }
                builder::tuple(ctx, span, len, out);
                Ok(())
            }
            Expression::Call { span, arg, label } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                let () = arg.compilation(ctx, name_prefix, out)?;

                let qualified = name_prefix
                    .join(label.into_ir(ctx.sources, ctx.file_idx))
                    .append(Name::Generated(0));

                out.words.push(RecursiveWord {
                    span,
                    inner: InnerWord::Call(normalize_path(ctx.sources, qualified)),
                    names: out.locals.names(),
                });
                out.locals.pop();
                out.locals.push_unnamed();

                Ok(())
            }
            Expression::Match { span, arg, cases } => {
                let span = span.span(ctx.file_idx);
                let () = arg.compilation(ctx, name_prefix, out)?;

                let mut else_case_out: Box<dyn FnOnce(&mut Output) -> Result<(), Error>> =
                    Box::new(|out: &mut Output| {
                        let () = builder::unreachable(span, out);
                        Ok(())
                    });

                for (pos, case) in cases.into_iter().rev().with_position() {
                    else_case_out = Box::new(move |out| {
                        let span = case.span.span(ctx.file_idx);
                        builder::cp_idx(ctx, span, 0, out);
                        let () = builder::matches(ctx, &case.binding, out)?;
                        builder::conditional(
                            ctx,
                            span,
                            span,
                            move |out| {
                                builder::binding(ctx, case.binding, out)?;
                                case.rhs.compilation(ctx, name_prefix, out)
                            },
                            span,
                            else_case_out,
                            out,
                        )
                    });
                }
                else_case_out(out)
            }
            Expression::If {
                span,
                cond,
                true_case,
                false_case,
            } => {
                let span = span.span(ctx.file_idx);
                let true_span = true_case.span(ctx.file_idx);
                let false_span = false_case.span(ctx.file_idx);

                let () = cond.compilation(ctx, name_prefix, out)?;

                builder::conditional(
                    ctx,
                    span,
                    true_span,
                    |out| true_case.compilation(ctx, name_prefix, out),
                    false_span,
                    |out| false_case.compilation(ctx, name_prefix, out),
                    out,
                )
            }
        }
    }
}

impl<'t> Spanner<'t> for Expression<'t> {
    fn pest_span(&self) -> pest::Span<'t> {
        match self {
            Expression::Literal(literal) => literal.pest_span(),
            Expression::Identifier(i) => i.pest_span(),
            Expression::Copy(i) => i.pest_span(),
            Expression::LetBlock {
                span,
                binding,
                rhs,
                inner,
            } => *span,
            Expression::Tuple { span, values } => *span,
            Expression::Call { span, arg, label } => *span,
            Expression::Match { span, .. } => *span,
            Expression::If { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Sentence {
    pub span: FileSpan,
    pub name: QualifiedName,
    pub words: Vec<Word>,
}

#[derive(Debug, Clone)]
pub struct Word {
    pub span: FileSpan,
    pub inner: InnerWord<QualifiedName>,
    pub names: Vec<Name>,
}

#[derive(Debug, Clone)]
pub struct RecursiveSentence {
    pub span: FileSpan,
    pub words: Vec<RecursiveWord>,
}

#[derive(Debug, Clone)]
pub struct RecursiveWord {
    pub span: FileSpan,
    pub inner: InnerWord<RecursiveSentence>,
    pub names: Vec<Name>,
}

#[derive(Debug, Clone)]
pub enum InnerWord<BranchRepr> {
    Push(flat::Value),
    Builtin(flat::Builtin),
    Copy(usize),
    Drop(usize),
    Move(usize),
    Tuple(usize),
    Untuple(usize),
    Call(QualifiedName),
    Branch(BranchRepr, BranchRepr),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NameRef<'t> {
    User(&'t str),
    Generated(usize),
}

impl<'t> std::fmt::Debug for NameRef<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::User(arg0) => f.write_str(arg0),
            Self::Generated(arg0) => write!(f, "${}", arg0),
        }
    }
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

fn literal_to_value(literal: ast::Literal) -> flat::Value {
    match literal {
        ast::Literal::Int(ast::Int { span: _, value }) => flat::Value::Usize(value),
        ast::Literal::Symbol(sym) => match sym {
            ast::Symbol::Identifier(identifier) => {
                flat::Value::Symbol(identifier.0.as_str().to_owned())
            }
            ast::Symbol::String(string_literal) => flat::Value::Symbol(string_literal.value),
        },
    }
}

fn normalize_path(sources: &Sources, mut path: QualifiedName) -> QualifiedName {
    loop {
        let Some(super_idx) = path
            .0
            .iter()
            .position(|n| n.as_ref(sources) == NameRef::User("super"))
        else {
            return path;
        };
        path.0.remove(super_idx - 1);
        path.0.remove(super_idx - 1);
    }
}

mod builder {
    use super::*;

    #[derive(Clone, Copy)]
    pub struct FileContext<'a> {
        pub sources: &'a source::Sources,
        pub file_idx: FileIndex,
    }

    pub struct Output {
        pub words: Vec<RecursiveWord>,
        pub locals: Locals,
    }

    // fn compile_matches(
    //     file_idx: FileIndex,
    //     sources: &Sources,
    //     b: ast::Binding,
    //     words: &mut Vec<RecursiveWord>,
    //     locals: &mut Locals,
    // ) -> Result<(), Error> {
    //     let span = b.span(file_idx);
    //     match b {
    //         ast::Binding::Literal(l) => {
    //             compile_literal(file_idx, l, words, locals);
    //             words.push(RecursiveWord {
    //                 span,
    //                 inner: InnerWord::Builtin(flat::Builtin::Eq),
    //                 names: locals.names(),
    //             });
    //             locals.pop();
    //             locals.pop();
    //             locals.push_unnamed();

    //             Ok(())
    //         }
    //         ast::Binding::Drop(drop_binding) => {
    //             words.push(RecursiveWord {
    //                 inner: InnerWord::Drop(0),
    //                 span: span,
    //                 names: locals.names(),
    //             });
    //             locals.pop();
    //             words.push(RecursiveWord {
    //                 inner: InnerWord::Push(flat::Value::Bool(true)),
    //                 span: span,
    //                 names: locals.names(),
    //             });
    //             locals.push_unnamed();
    //             Ok(())
    //         }
    //         ast::Binding::Tuple(tuple_binding) => {
    //             words.push(RecursiveWord {
    //                 inner: InnerWord::Untuple(tuple_binding.bindings.len()),
    //                 span: span,
    //                 names: locals.names(),
    //             });
    //             locals.pop();
    //             if tuple_binding.bindings.len() == 0 {
    //                 words.push(RecursiveWord {
    //                     inner: InnerWord::Push(flat::Value::Bool(true)),
    //                     span: span,
    //                     names: locals.names(),
    //                 });
    //                 locals.push_unnamed();
    //                 return Ok(())
    //             }

    //             for _ in (0..tuple_binding.bindings.len()){
    //                 locals.push_unnamed();
    //             }

    //             words.push(RecursiveWord {
    //                 inner: InnerWord::Push(flat::Value::Bool(true)),
    //                 span: span,
    //                 names: locals.names(),
    //             });

    //             // let tmp_names: Vec<Name> = (0..tuple_binding.bindings.len())
    //             //     .map(|_| locals.push_unnamed())
    //             //     .collect();

    //             // // let names = self.untuple(span, tuple_binding.bindings.len());
    //             // for (name, binding) in tmp_names.into_iter().zip_eq(tuple_binding.bindings) {
    //             //     let (more_words, more_locals) = compile_matches(file_idx, sources, span, &name, locals.clone())?;
    //             //     words.extend(more_words);
    //             //     *locals = more_locals;
    //             //     let () = compile_binding(file_idx, sources, binding, words, locals)?;
    //             // }
    //             Ok(())
    //         }
    //         ast::Binding::Identifier(identifier) => {
    //             locals.pop();
    //             locals.push_named(span);
    //             Ok(())
    //         }
    //     }
    // }

    pub fn literal(ctx: FileContext, value: ast::Literal, output: &mut Output) {
        let span = value.span(ctx.file_idx);
        match value {
            ast::Literal::Int(ast::Int { span: _, value }) => {
                push_value(span, flat::Value::Usize(value), output)
            }
            ast::Literal::Symbol(sym) => match sym {
                ast::Symbol::Identifier(identifier) => push_value(
                    span,
                    flat::Value::Symbol(identifier.0.as_str().to_owned()),
                    output,
                ),
                ast::Symbol::String(string_literal) => {
                    push_value(span, flat::Value::Symbol(string_literal.value), output)
                }
            },
        }
    }

    pub fn push_value(span: FileSpan, value: flat::Value, output: &mut Output) {
        output.words.push(RecursiveWord {
            span,
            inner: InnerWord::Push(value),
            names: output.locals.names(),
        });
        output.locals.push_unnamed();
    }

    fn mv(
        FileContext { sources, file_idx }: FileContext,
        span: FileSpan,
        name: Name,
        out: &mut Output,
    ) -> Result<(), Error> {
        let Some(idx) = out.locals.find(sources, name) else {
            return Err(Error::UnknownReference {
                location: span.location(sources),
                name: name
                    .as_ref(sources)
                    .as_str()
                    .unwrap_or("<unnamed>")
                    .to_owned(),
            });
        };
        mv_idx(span, idx, out);
        Ok(())
    }

    pub fn mv_ident(
        ctx: FileContext,
        ident: ast::Identifier,
        out: &mut Output,
    ) -> Result<(), Error> {
        let span = ident.span(ctx.file_idx);
        mv(ctx, span, Name::User(span), out)
    }

    pub fn mv_idx(span: FileSpan, idx: usize, Output { locals, words }: &mut Output) {
        let names = locals.names();
        let declared = locals.remove(idx);
        locals.push_unnamed();

        words.push(RecursiveWord {
            inner: InnerWord::Move(idx),
            span,
            names,
        });
    }

    pub fn cp(ctx: FileContext, span: FileSpan, name: Name, out: &mut Output) -> Result<(), Error> {
        let Some(idx) = out.locals.find(ctx.sources, name) else {
            return Err(Error::UnknownReference {
                location: span.location(ctx.sources),
                name: name
                    .as_ref(ctx.sources)
                    .as_str()
                    .unwrap_or("<unnamed>")
                    .to_owned(),
            });
        };
        Ok(cp_idx(ctx, span, idx, out))
    }

    pub fn cp_ident(
        ctx: FileContext,
        ident: ast::Identifier,
        out: &mut Output,
    ) -> Result<(), Error> {
        let span = ident.span(ctx.file_idx);
        cp(ctx, span, Name::User(span), out)
    }

    pub fn cp_idx(ctx: FileContext, span: FileSpan, idx: usize, out: &mut Output) {
        let names = out.locals.names();
        out.words.push(RecursiveWord {
            inner: InnerWord::Copy(idx),
            span,
            names,
        });
        out.locals.push_unnamed();
    }

    // // pub fn sd_idx(&mut self, span: FileSpan<'t>, idx: usize) {
    // //     let names = out.locals.names();

    // //     let declared = out.locals.pop();
    // //     out.locals.insert(idx, declared);

    // //     out.words.push(RecursiveWord {
    // //         inner: InnerWord::Send(idx),
    // //         modname: self.modname.clone(),
    // //         span,
    // //         names,
    // //     });
    // // }
    // // pub fn sd_top(&mut self, span: FileSpan<'t>) {
    // //     self.sd_idx(span, out.locals.len() - 1)
    // // }

    pub fn drop(ctx: FileContext, span: FileSpan, name: Name, out: &mut Output) {
        let idx = out
            .locals
            .find(ctx.sources, name)
            .expect(&format!("Unknown name: {:?}", name));
        drop_idx(ctx, span, idx, out);
    }

    pub fn drop_idx(ctx: FileContext, span: FileSpan, idx: usize, out: &mut Output) {
        let names = out.locals.names();
        let declared = out.locals.remove(idx);

        out.words.push(RecursiveWord {
            inner: InnerWord::Drop(idx),
            span,
            names,
        });
    }

    // // pub fn path(ctx:FileContext, ast::Path { span, segments }: ast::Path<'t>) {
    // //     for segment in segments.iter().rev() {
    // //         self.literal_split(*segment, Value::Symbol(segment.as_str().to_owned()));
    // //     }
    // //     self.literal_split(span, Value::Namespace(self.ns_idx));
    // //     for segment in segments {
    // //         self.builtin(segment, Builtin::Get);
    // //     }
    // // }

    // pub fn ir_builtin(ctx:FileContext, builtin: ir::Builtin) -> Result<(), Error> {
    //     let name = builtin.name.0.as_str(ctx.sources);
    //     if builtin.args.is_empty() {
    //         if let Some(b) = flat::Builtin::ALL.iter().find(|b| b.name() == name) {
    //             self.builtin(builtin.span, *b);
    //             Ok(())
    //         } else {
    //             Err(Error::UnknownBuiltin {
    //                 location: builtin.span.location(ctx.sources).unwrap(),
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
    //                         location: builtin.span.location(ctx.sources).unwrap(),
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
    //                         location: builtin.span.location(ctx.sources).unwrap(),
    //                         name: name.to_owned(),
    //                     });
    //                 };

    //                 let true_case = self.lookup_label(&true_case)?;
    //                 let false_case = self.lookup_label(&false_case)?;

    //                 let names = out.locals.names();
    //                 out.locals.pop();
    //                 out.words.push(RecursiveWord {
    //                     inner: InnerWord::Branch(true_case, false_case),
    //                     span: builtin.span,
    //                     names,
    //                 });
    //                 Ok(())
    //             }
    //             "call" => {
    //                 let Ok(ir::BuiltinArg::Label(label)) = builtin.args.into_iter().exactly_one()
    //                 else {
    //                     return Err(Error::IncorrectBuiltinArguments {
    //                         location: builtin.span.location(ctx.sources).unwrap(),
    //                         name: name.to_owned(),
    //                     });
    //                 };

    //                 self.label_call(label)?;
    //                 Ok(())
    //             }
    //             _ => Err(Error::UnknownBuiltin {
    //                 location: builtin.span.location(ctx.sources).unwrap(),
    //                 name: name.to_owned(),
    //             }),
    //         }
    //     }
    // }

    // pub fn builtin(ctx:FileContext, span: FileSpan, builtin: flat::Builtin) {
    //     out.words.push(RecursiveWord {
    //         span,
    //         inner: InnerWord::Builtin(builtin),
    //         names: Some(out.locals.names()),
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
    //             out.locals.pop();
    //             out.locals.pop();
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::NsEmpty => {
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::NsGet => {
    //             let ns = out.locals.pop();
    //             out.locals.pop();
    //             out.locals.push_front(ns);
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::NsInsert | flat::Builtin::If => {
    //             out.locals.pop();
    //             out.locals.pop();
    //             out.locals.pop();
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::NsRemove => {
    //             let ns = out.locals.pop();
    //             out.locals.pop();
    //             out.locals.push_front(ns);
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::Not
    //         | flat::Builtin::SymbolLen
    //         | flat::Builtin::Deref
    //         | flat::Builtin::Ord => {
    //             out.locals.pop();
    //             out.locals.push_unnamed();
    //         }
    //         flat::Builtin::AssertEq => {
    //             out.locals.pop();
    //             out.locals.pop();
    //         }
    //         flat::Builtin::Snoc => {
    //             out.locals.pop();
    //             out.locals.push_unnamed();
    //             out.locals.push_unnamed();
    //         }
    //     }
    // }

    // fn fully_qualified_call(ctx:FileContext, span: FileSpan, name: QualifiedName) -> Result<(), Error> {
    //     out.words.push(RecursiveWord {
    //         span,
    //         inner: InnerWord::Call(self.normalize_path(name)),
    //         names: out.locals.names(),
    //     });
    //     out.locals.pop();
    //     out.locals.push_unnamed();
    //     Ok(())
    // }

    // fn normalize_path(&self, mut path: QualifiedName) -> QualifiedName {
    //     loop {
    //         let Some(super_idx) = path
    //             .0
    //             .iter()
    //             .position(|n| n.as_ref(&ctx.sources) == NameRef::User("super"))
    //         else {
    //             return path;
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
    //             location: l.span.location(ctx.sources).unwrap(),
    //             name: sentence_key.to_string(),
    //         })
    //         .copied()
    // }

    pub fn tuple(ctx: FileContext, span: FileSpan, size: usize, out: &mut Output) {
        out.words.push(RecursiveWord {
            inner: InnerWord::Tuple(size),
            span: span,
            names: out.locals.names(),
        });

        for _ in 0..size {
            let Name::Generated(_) = out.locals.pop() else {
                panic!("tried to tuple a named variable?")
            };
        }
        out.locals.push_unnamed();
    }

    pub fn untuple(ctx: FileContext, span: FileSpan, size: usize, out: &mut Output) -> Vec<Name> {
        out.words.push(RecursiveWord {
            inner: InnerWord::Untuple(size),
            span: span,
            names: out.locals.names(),
        });
        out.locals.pop();
        (0..size).map(|_| out.locals.push_unnamed()).collect()
    }

    // // fn func_call(ctx:FileContext, call: ast::Call<'t>) -> Result<usize, BuilderError<'t>> {
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

    // // fn value_expr(ctx:FileContext, expr: ir::ValueExpression) -> Result<(), Error> {
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

    fn eq(span: FileSpan, out: &mut Output) {
        out.words.push(RecursiveWord {
            span,
            inner: InnerWord::Builtin(flat::Builtin::Eq),
            names: out.locals.names(),
        });
        out.locals.pop();
        out.locals.pop();
        out.locals.push_unnamed();
    }
    fn assert_eq(span: FileSpan, out: &mut Output) {
        out.words.push(RecursiveWord {
            span,
            inner: InnerWord::Builtin(flat::Builtin::AssertEq),
            names: out.locals.names(),
        });
        out.locals.pop();
        out.locals.pop();
    }

    pub fn binding(ctx: FileContext, b: ast::Binding, out: &mut Output) -> Result<(), Error> {
        let span = b.span(ctx.file_idx);
        match b {
            ast::Binding::Literal(l) => {
                literal(ctx, l, out);
                assert_eq(span, out);
                Ok(())
            }
            ast::Binding::Drop(drop_binding) => {
                out.words.push(RecursiveWord {
                    inner: InnerWord::Drop(0),
                    span: span,
                    names: out.locals.names(),
                });
                out.locals.pop();
                Ok(())
            }
            ast::Binding::Tuple(tuple_binding) => {
                let tmp_names = untuple(ctx, span, tuple_binding.bindings.len(), out);

                for (name, b) in tmp_names.into_iter().zip_eq(tuple_binding.bindings) {
                    let () = builder::mv(ctx, span, name, out)?;
                    let () = binding(ctx, b, out)?;
                }
                Ok(())
            }
            ast::Binding::Identifier(identifier) => {
                out.locals.pop();
                out.locals.push_named(span);
                Ok(())
            }
        }
    }

    pub fn matches(
        ctx: FileContext,
        binding: &ast::Binding,
        out: &mut Output,
    ) -> Result<(), Error> {
        let span = binding.span(ctx.file_idx);
        match binding {
            ast::Binding::Drop(_) | ast::Binding::Identifier(_) => {
                drop_idx(ctx, span, 0, out);
                push_value(span, flat::Value::Bool(true), out);
                Ok(())
            }
            ast::Binding::Tuple(tuple_binding) => {
                let names = untuple(ctx, span, tuple_binding.bindings.len(), out);

                let mut true_case: Box<dyn FnOnce(&mut Output) -> Result<(), Error>> =
                    Box::new(|out: &mut Output| {
                        push_value(span, flat::Value::Bool(true), out);
                        Ok(())
                    });
                let mut true_case_consumes: Vec<Name> = vec![];
                for (name, binding) in names
                    .iter()
                    .rev()
                    .zip_eq(tuple_binding.bindings.iter().rev())
                {
                    let consumed_copy = true_case_consumes.clone();
                    true_case = Box::new(|out: &mut Output| {
                        let span = binding.span(ctx.file_idx);
                        mv(ctx, span, *name, out)?;
                        let () = matches(ctx, binding, out)?;
                        conditional(
                            ctx,
                            span,
                            span,
                            true_case,
                            span,
                            move |out| {
                                push_value(span, flat::Value::Bool(false), out);
                                for n in consumed_copy.iter() {
                                    drop(ctx, span, n.clone(), out)
                                }
                                Ok(())
                            },
                            out,
                        )
                    });
                    true_case_consumes.push(name.clone());
                }
                true_case(out)
            }
            ast::Binding::Literal(l) => {
                literal(ctx, l.clone(), out);
                eq(span, out);
                Ok(())
            }
        }
    }

    pub fn conditional(
        ctx: FileContext,
        span: FileSpan,
        true_span: FileSpan,
        true_case: impl FnOnce(&mut Output) -> Result<(), Error>,
        false_span: FileSpan,
        false_case: impl FnOnce(&mut Output) -> Result<(), Error>,
        out: &mut Output,
    ) -> Result<(), Error> {
        out.locals.pop();

        let names = out.locals.names();

        let mut true_out = Output {
            words: vec![],
            locals: out.locals.clone(),
        };
        let () = true_case(&mut true_out)?;

        let mut false_out = Output {
            words: vec![],
            locals: out.locals.clone(),
        };
        let () = false_case(&mut false_out)?;

        if !true_out.locals.compare(ctx.sources, &false_out.locals) {
            return Err(Error::BranchContractsDisagree {
                location: span.location(ctx.sources),
            });
        }
        if true_out.locals.terminal {
            out.locals = false_out.locals;
        } else {
            out.locals = true_out.locals;
        }

        let true_words = RecursiveSentence {
            span: true_span,
            words: true_out.words,
        };
        let false_words = RecursiveSentence {
            span: false_span,
            words: false_out.words,
        };

        out.words.push(RecursiveWord {
            span,
            inner: InnerWord::Branch(true_words, false_words),
            names,
        });
        Ok(())
    }

    pub fn unreachable(span: FileSpan, out: &mut Output) {
        out.words.push(RecursiveWord {
            span,
            inner: InnerWord::Builtin(flat::Builtin::Panic),
            names: out.locals.names(),
        });
        out.locals.terminal = true;
    }
}
