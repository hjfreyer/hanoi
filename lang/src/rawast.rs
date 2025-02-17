use from_pest::{FileIndex, FromPest};
use pest_ast::FromPest;
use pest_derive::Parser;

use crate::source::Span;

#[derive(Parser)]
#[grammar = "hanoi.pest"]
pub struct HanoiParser;

fn span_into_str(file_idx: FileIndex, span: pest::Span) -> &str {
    span.as_str()
}

fn span_into_usize(file_idx: FileIndex, span: pest::Span) -> usize {
    span.as_str().parse().unwrap()
}

fn pest_span_into_span(file_idx: FileIndex, span: pest::Span) -> Span {
    Span::File(::from_pest::FileSpan {
        file_idx,
        start: span.start(),
        end: span.end(),
    })
}
#[derive(Debug, FromPest, Clone)]
#[pest_ast(rule(Rule::identifier))]
pub struct Identifier(#[pest_ast(outer(with(pest_span_into_span)))] pub Span);

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::label))]
pub struct Label(pub Identifier);

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::int))]
pub struct Int {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,

    #[pest_ast(outer(with(span_into_usize)))]
    pub value: usize,
}

fn span_into_string_literal(file_idx: FileIndex, span: pest::Span) -> String {
    let str = span.as_str();
    let str = &str[1..str.len() - 1];
    str.replace("\\n", "\n").replace("\\\"", "\"")
}
#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::string))]
pub struct StringLiteral {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,

    #[pest_ast(outer(with(span_into_string_literal)))]
    pub value: String,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::symbol))]
pub enum Symbol {
    Identifier(Identifier),
    String(StringLiteral),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::literal))]
pub enum Literal {
    Int(Int),
    Symbol(Symbol),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::copy))]
pub struct Copy(pub Identifier);

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::tuple_expr))]
pub struct Tuple {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
    pub values: Vec<ValueExpression>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin_arg))]
pub enum BuiltinArg {
    Int(Int),
    Label(LabelCall),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin))]
pub struct Builtin {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
    pub name: Identifier,
    pub args: Vec<BuiltinArg>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::label_call))]
pub struct LabelCall {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
    pub path: Vec<Identifier>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::stack_bindings))]
pub struct StackBindings {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
    pub bindings: Vec<Binding>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::binding))]
pub enum Binding {
    Drop(DropBinding),
    // Tuple(TupleBinding),
    Literal(Literal),
    Identifier(Identifier),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::drop_binding))]
pub struct DropBinding {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
}

// #[derive(Debug, FromPest)]
// #[pest_ast(rule(Rule::tuple_binding))]
// pub struct TupleBinding {
//     #[pest_ast(outer(with(pest_span_into_span)))]
//     pub span: Span,
//     pub bindings: Vec<Binding>
// }

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::value_expr))]
pub enum ValueExpression {
    Literal(Literal),
    Move(Identifier),
    Copy(Copy),
    Tuple(Tuple),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::raw_word))]
pub enum Word {
    StackBindings(StackBindings),
    Builtin(Builtin),
    ValueExpression(ValueExpression),
    LabelCall(LabelCall),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::sentence))]
pub struct Sentence {
    pub words: Vec<Word>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::sentence_decl))]
pub struct SentenceDecl {
    #[pest_ast(outer(with(pest_span_into_span)))]
    pub span: Span,
    pub label: Label,
    pub sentence: Sentence,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::decl))]
pub enum Decl {
    SentenceDecl(SentenceDecl),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::file))]
pub struct File {
    pub decl: Vec<Decl>,
    eoi: EOI,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::EOI))]
struct EOI;
