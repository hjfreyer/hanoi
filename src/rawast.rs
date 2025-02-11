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
#[pest_ast(rule(Rule::tuple_expr))]
pub struct Tuple<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub values: Vec<ValueExpression<'t>>,
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
#[pest_ast(rule(Rule::label_call))]
pub struct LabelCall<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub path: Vec<Identifier<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::stack_bindings))]
pub struct StackBindings<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
    pub bindings: Vec<Binding<'t>>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::binding))]
pub enum Binding<'t> {
    DropBinding(DropBinding<'t>),
    Literal(Literal<'t>),
    Identifier(Identifier<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::drop_binding))]
pub struct DropBinding<'t> {
    #[pest_ast(outer())]
    pub span: pest::Span<'t>,
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::value_expr))]
pub enum ValueExpression<'t> {
    Literal(Literal<'t>),
    Tuple(Tuple<'t>),
}

#[derive(Debug, FromPest)]
#[pest_ast(rule(Rule::raw_word))]
pub enum Word<'t> {
    StackBindings(StackBindings<'t>),
    Builtin(Builtin<'t>),
    ValueExpression(ValueExpression<'t>),
    LabelCall(LabelCall<'t>),
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
