use clap::Arg;
use from_pest::FromPest;
use from_raw_ast::Spanner;
use pest_ast::FromPest;
use pest_derive::Parser;

use crate::source::{self, FileIndex, FileSpan};

#[derive(Parser)]
#[grammar = "hanoi.pest"]
pub struct HanoiParser;

fn span_into_str(span: pest::Span) -> &str {
    span.as_str()
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::identifier))]
pub struct Identifier<'t>(
    #[spanner]
    #[pest_ast(outer())]
    pub pest::Span<'t>,
);
impl<'t> Identifier<'t> {
    pub fn span(&self, file_idx: FileIndex) -> FileSpan {
        FileSpan::from_ast(file_idx, self.0)
    }
}

pub trait Spanner<'t> {
    fn pest_span(&self) -> pest::Span<'t>;
    fn span(&self, file_idx: FileIndex) -> FileSpan {
        FileSpan::from_ast(file_idx, self.pest_span())
    }
}

impl<'t> Spanner<'t> for pest::Span<'t> {
    fn pest_span(&self) -> pest::Span<'t> {
        *self
    }
}

// #[derive(Debug, FromPest)]
// #[pest_ast(rule(Rule::label))]
// pub struct Label<'t>(pub Identifier<'t>);

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::int))]
pub struct Int<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,

    #[pest_ast(outer(with(span_into_str), with(str::parse), with(Result::unwrap)))]
    pub value: usize,
}

fn span_into_string_literal(span: pest::Span) -> String {
    let str = span.as_str();
    let str = &str[1..str.len() - 1];
    str.replace("\\n", "\n").replace("\\\"", "\"")
}
#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::string))]
pub struct StringLiteral<'t> {
    #[spanner]
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,

    #[pest_ast(outer(with(span_into_string_literal)))]
    pub value: String,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::symbol))]
pub enum Symbol<'t> {
    Identifier(Identifier<'t>),
    String(StringLiteral<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::literal))]
pub enum Literal<'t> {
    Int(Int<'t>),
    Symbol(Symbol<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::copy))]
pub struct Copy<'t>(pub Identifier<'t>);

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::tuple_expr))]
pub struct Tuple<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub values: Vec<Expression<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin_arg))]
pub enum BuiltinArg<'t> {
    Int(Int<'t>),
    Label(QualifiedLabel<'t>),
    Sentence(Sentence<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin))]
pub struct Builtin<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub name: Identifier<'t>,
    pub args: Vec<BuiltinArg<'t>>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::qualified_label))]
pub struct QualifiedLabel<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub path: Vec<Identifier<'t>>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::binding))]
pub enum Binding<'t> {
    Drop(DropBinding<'t>),
    Tuple(TupleBinding<'t>),
    Literal(Literal<'t>),
    Identifier(Identifier<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::drop_binding))]
pub struct DropBinding<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::tuple_binding))]
pub struct TupleBinding<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub bindings: Vec<Binding<'t>>,
}

// #[derive(Debug, FromPest)]
// #[pest_ast(rule(Rule::expr))]
// pub enum ValueExpression<'t> {
//     Literal(Literal<'t>),
//     Move(Identifier<'t>),
//     Copy(Copy<'t>),
//     Tuple(Tuple<'t>),
// }

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::raw_word))]
pub enum Word<'t> {
    Builtin(Builtin<'t>),
    Literal(Literal<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::sentence))]
pub struct Sentence<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub words: Vec<Word<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::sentence_decl))]
pub struct SentenceDecl<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub name: Identifier<'t>,
    pub sentence: Sentence<'t>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::decl))]
pub enum Decl<'t> {
    SentenceDecl(SentenceDecl<'t>),
    Namespace(NamespaceDecl<'t>),
    Proc(ProcDecl<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::file))]
pub struct File<'t> {
    pub ns: Namespace<'t>,
    eoi: EOI,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::ns_decl))]
pub struct NamespaceDecl<'t> {
    pub name: Identifier<'t>,
    pub ns: Namespace<'t>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::namespace))]
pub struct Namespace<'t> {
    pub decl: Vec<Decl<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::proc_decl))]
pub struct ProcDecl<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub binding: Binding<'t>,
    pub name: Identifier<'t>,
    pub expression: Expression<'t>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::expr))]
pub struct Expression<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,

    pub root: RootExpression<'t>,
    pub transformers: Vec<Transformer<'t>>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::root_expr))]
pub enum RootExpression<'t> {
    Literal(Literal<'t>),
    Tuple(Tuple<'t>),
    Block(Block<'t>),
    Identifier(Identifier<'t>),
    Copy(Copy<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::transformer))]
pub enum Transformer<'t> {
    Call(QualifiedLabel<'t>),
    Match(Match<'t>),
    If(If<'t>),
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::block))]
pub struct Block<'t> {
    #[pest_ast(outer())]
    #[spanner]
    pub span: pest::Span<'t>,
    pub statements: Vec<Statement<'t>>,
    pub expression: Box<Expression<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::statement))]
pub enum Statement<'t> {
    Let(LetStatement<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::let_statement))]

pub struct LetStatement<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub binding: Binding<'t>,
    pub rhs: Expression<'t>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::if_expr))]

pub struct If<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub true_case: Box<Expression<'t>>,
    pub false_case: Box<Expression<'t>>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::match_expr))]

pub struct Match<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub cases: Vec<MatchCase<'t>>,
}

#[derive(Debug, FromPest, Spanner)]
#[pest_ast(rule(Rule::match_case))]

pub struct MatchCase<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub binding: Binding<'t>,
    pub rhs: Expression<'t>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::EOI))]
struct EOI;
