use pest_ast::FromPest;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "hanoi.pest"]
pub struct HanoiParser;

fn span_into_str(span: pest::Span) -> &str {
    span.as_str()
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::identifier))]
pub struct Identifier<'t>(#[pest_ast(outer())] pub pest::Span<'t>);

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::label))]
pub struct Label<'t>(pub Identifier<'t>);

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::int))]
pub struct Int<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,

    #[pest_ast(outer(with(span_into_str), with(str::parse), with(Result::unwrap)))]
    pub value: usize,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::literal))]
pub enum Literal<'t> {
    Int(Int<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin_arg))]
pub enum BuiltinArg<'t> {
    Int(Int<'t>),
    Label(Label<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::builtin))]
pub struct Builtin<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub name: Identifier<'t>,
    pub args: Vec<BuiltinArg<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::raw_word))]
pub enum Word<'t> {
    Builtin(Builtin<'t>),
    Literal(Literal<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::sentence))]
pub struct Sentence<'t> {
    pub words: Vec<Word<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::sentence_decl))]
pub struct SentenceDecl<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub label: Label<'t>,
    pub sentence: Sentence<'t>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::decl))]
pub enum Decl<'t> {
    SentenceDecl(SentenceDecl<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::file))]
pub struct File<'t> {
    pub decl: Vec<Decl<'t>>,
    eoi: EOI,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::EOI))]
struct EOI;
