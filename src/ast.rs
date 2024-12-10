use itertools::Itertools;
use pest::{iterators::Pair, Parser, Span};
use pest_derive::Parser;

use crate::flat::Value;

#[derive(Parser)]
#[grammar = "hanoi.pest"]
pub struct HanoiParser;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module<'t> {
    pub namespace: Namespace<'t>,
}

impl<'t> Module<'t> {
    pub fn from_str(text: &'t str) -> anyhow::Result<Self> {
        let file = HanoiParser::parse(Rule::file, text)?;

        let file = file.exactly_one().unwrap();
        assert_eq!(file.as_rule(), Rule::file);

        let (ns, eoi) = file.into_inner().collect_tuple().unwrap();
        assert_eq!(eoi.as_rule(), Rule::EOI);

        Ok(Module {
            namespace: Namespace::from_pair(ns),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Namespace<'t> {
    pub decls: Vec<Decl<'t>>,
    pub span: Span<'t>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier<'t>(pub Span<'t>);
impl <'t>Identifier<'t> {
    pub(crate) fn as_str(&self) -> &'t str {
        self.0.as_str()
    }
}

impl<'t> From<Pair<'t, Rule>> for Identifier<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        Self(ident_from_pair(value))
    }
}

pub fn ident_from_pair<'t>(p: pest::iterators::Pair<'t, Rule>) -> Span<'t> {
    assert_eq!(
        p.as_rule(),
        Rule::identifier,
        "at {:?}, expected identifier, got {:?}",
        p.as_span().start_pos().line_col(),
        p
    );
    p.as_span()
}

pub fn int_from_pair(p: pest::iterators::Pair<Rule>) -> usize {
    assert_eq!(p.as_rule(), Rule::int);
    p.as_str().parse().unwrap()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal<'t> {
    pub span: Span<'t>,
    pub value: Value,
}

impl<'t> From<Pair<'t, Rule>> for Literal<'t> {
    fn from(p: Pair<'t, Rule>) -> Self {
        let span = p.as_span();
        assert_eq!(p.as_rule(), Rule::literal);
        let literal = p.into_inner().exactly_one().unwrap();
        let value = match literal.as_rule() {
            Rule::int => Value::Usize(int_from_pair(literal)),
            Rule::bool => Value::Bool(literal.as_str().parse().unwrap()),
            Rule::char_lit => {
                let chr = literal.into_inner().exactly_one().unwrap();
                assert_eq!(Rule::lit_char, chr.as_rule());

                let c = match chr.as_str() {
                    "\\n" => '\n',
                    c => c.chars().exactly_one().unwrap(),
                };

                Value::Char(c)
            }

            Rule::symbol => {
                let ident = literal.into_inner().exactly_one().unwrap();
                match ident.as_rule() {
                    Rule::identifier => Value::Symbol(ident.as_str().to_owned()),
                    Rule::string => {
                        let inner = ident.into_inner().exactly_one().unwrap();
                        assert_eq!(inner.as_rule(), Rule::str_inner);

                        Value::Symbol(inner.as_str().replace("\\n", "\n").replace("\\\"", "\""))
                    }
                    _ => unreachable!(),
                }
            }

            Rule::nil => Value::Nil,
            _ => unreachable!("{:?}", literal),
        };
        Self { span, value }
    }
}

pub struct ProcMatchBlock<'t> {
    pub span: Span<'t>,
    pub expr: Pair<'t, Rule>,
    pub cases: Vec<ProcMatchCase<'t>>,
}

impl<'t> From<Pair<'t, Rule>> for ProcMatchBlock<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        assert_eq!(Rule::match_block, value.as_rule());

        let span = value.as_span();
        let (expr, cases) = value.into_inner().collect_tuple().unwrap();
        Self {
            span,
            expr,
            cases: cases.into_inner().map(|c| c.into()).collect(),
        }
    }
}

pub struct ProcMatchCase<'t> {
    pub span: Span<'t>,
    pub bindings: Bindings<'t>,
    pub body: Pair<'t, Rule>,
}

impl<'t> From<Pair<'t, Rule>> for ProcMatchCase<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        assert_eq!(Rule::match_case, value.as_rule());
        let span = value.as_span();
        let (bindings, body) = value.into_inner().collect_tuple().unwrap();

        Self {
            span,
            bindings: bindings.into(),
            body,
        }
    }
}

impl<'t> Namespace<'t> {
    fn from_pair(p: pest::iterators::Pair<'t, Rule>) -> Self {
        assert_eq!(p.as_rule(), Rule::namespace);

        let mut res = Self {
            decls: vec![],
            span: p.as_span(),
        };
        for decl in p.into_inner() {
            match decl.as_rule() {
                // Rule::code_decl => {
                //     let (ident, code) = decl.into_inner().collect_tuple().unwrap();
                //     assert_eq!(ident.as_rule(), Rule::identifier);
                //     let code = Code::from_pair(code);

                //     res.decls.push(Decl {
                //         name: ident.as_str().to_owned(),
                //         value: DeclValue::Code(code),
                //     })
                // }
                Rule::ns_decl => {
                    let (ident, ns) = decl.into_inner().collect_tuple().unwrap();
                    assert_eq!(ident.as_rule(), Rule::identifier);
                    let ns = Namespace::from_pair(ns);

                    res.decls.push(Decl {
                        name: ident.as_str().to_owned(),
                        value: DeclValue::Namespace(ns),
                    })
                }
                Rule::proc_decl => {
                    let (ident, args_and_body) = decl.into_inner().collect_tuple().unwrap();
                    assert_eq!(ident.as_rule(), Rule::identifier);

                    res.decls.push(Decl {
                        name: ident_from_pair(ident).as_str().to_owned(),
                        value: DeclValue::Proc(args_and_body.into()),
                    })
                }
                // Rule::match_proc_decl => {
                //     let (ident, cases) = decl.into_inner().collect_tuple().unwrap();
                //     assert_eq!(ident.as_rule(), Rule::identifier);

                //     res.decls.push(Decl {
                //         name: ident_from_pair(ident).as_str().to_owned(),
                //         value: DeclValue::MatchProc(MatchProc { cases }),
                //     })
                // }
                _ => unreachable!(),
            }
        }
        res
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl<'t> {
    pub name: String,
    pub value: DeclValue<'t>,
}

// impl<'t> Decl<'t> {
//     fn from_pair(p: Pair<'t, Rule>) -> Decl<'t> {
//         assert_eq!(p.as_rule(), Rule::decl);
//         let (ident, code) = p.into_inner().collect_tuple().unwrap();
//         assert_eq!(ident.as_rule(), Rule::identifier);
//         let code = Code::from_pair(code);

//         Decl {
//             name: ident.as_str().to_owned(),
//             value: DeclValue::Code(code),
//         }
//     }
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclValue<'t> {
    Namespace(Namespace<'t>),
    // Code(Code<'t>),
    Proc(Block<'t>),
    // MatchProc(MatchProc<'t>),
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct Proc<'t> {
//     // pub args: Bindings<'t>,
//     pub body: Block<'t>,
// }

// pub fn parse_proc_args_and_body<'t>(value: Pair<'t, Rule>) -> Block<'t> {
//     assert_eq!(value.as_rule(), Rule::proc_args_and_body);
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block<'t> {
    Bind {
        name: Span<'t>,
        inner: Box<Block<'t>>,
    },
    Call {
        span: Span<'t>,
        call: Call<'t>,
        next: Box<Block<'t>>,
    },
    Become {
        span: Span<'t>,
        call: Call<'t>,
    },
    // Statement {
    //     span: Span<'t>,
    //     statement: Statement<'t>,
    //     next: Box<Block<'t>>,
    // },
    // Endpoint{
    //     span: Span<'t>,
    //     endpoint: Endpoint<'t>,
    // }
    AssertEq {
        literal: Literal<'t>,
        inner: Box<Block<'t>>,
    },
    Match {
        span: Span<'t>,
        cases: Vec<MatchCase<'t>>,
        els: Option<Box<Block<'t>>>,
    },
    If {
        span: Span<'t>,
        true_case: Box<Block<'t>>,
        false_case: Box<Block<'t>>,
    },
    Raw {
        span: Span<'t>,
        words: Vec<RawWord<'t>>,
    },
    Unreachable {
        span: Span<'t>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchCase<'t> {
    pub span: Span<'t>,
    pub literal: Literal<'t>,
    pub body: Block<'t>,
}

impl<'t> Block<'t> {
    fn with_bindings(mut self, bindings: Bindings<'t>) -> Self {
        for arg in bindings.bindings.into_iter().rev() {
            match arg {
                Binding::Ident(i) => {
                    self = Self::Bind {
                        name: i,
                        inner: Box::new(self),
                    }
                }
                Binding::Literal(literal) => {
                    self = Self::AssertEq {
                        literal,
                        inner: Box::new(self),
                    }
                }
            };
        }
        self
    }
}
impl<'t> From<Pair<'t, Rule>> for Block<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        let span = value.as_span();

        match value.as_rule() {
            Rule::proc_args_and_body => {
                let (args, body) = value.into_inner().collect_tuple().unwrap();

                let args = Bindings::from(args);
                let res = Block::from(body);

                res.with_bindings(args)
            }

            Rule::block => {
                let (statements, endpoint) = value.into_inner().collect_tuple().unwrap();
                let mut res = Block::from(endpoint);

                for statement in statements.into_inner().rev() {
                    let statement_span = statement.as_span();
                    match statement.as_rule() {
                        Rule::let_statement => {
                            let (bindings, expr) = statement.into_inner().collect_tuple().unwrap();

                            res = res.with_bindings(bindings.into());

                            res = Block::Call {
                                span: statement_span,
                                call: Call::from(expr),
                                next: Box::new(res),
                            };
                        }
                        _ => unreachable!("unexpected rule: {:?}", statement),
                    }
                }

                res
            }
            Rule::raw_statement => Block::Raw {
                span,
                words: value.into_inner().map(RawWord::from).collect(),
            },
            Rule::if_endpoint => {
                let (expr, true_case,false_case) = value.into_inner().collect_tuple().unwrap();
                let if_block = Block::If {
                    span,
                    true_case: Box::new(true_case.into()),
                    false_case: Box::new(false_case.into()),
                };

                Block::Call {
                    span: expr.as_span(),
                    call: Call::from(expr),
                    next: Box::new(if_block),
                }
            }
            Rule::unreachable => Block::Unreachable { span },
            Rule::r#become => {
                let func_call = value.into_inner().exactly_one().unwrap();
                Block::Become {
                    span,
                    call: Call::from(func_call),
                }
            }

            _ => unreachable!("unexpected rule: {:?}", value),
        }
        // assert_eq!(value.as_rule(), Rule::block);
        // let (statements, endpoint) = value.into_inner().collect_tuple().unwrap();

        // let mut res = Block::Endpoint { span, endpoint: endpoint.into()};
        // for statement in statements.into_inner().rev() {
        //     res = Block::Statement {
        //         span,
        //         statement: Statement::from(statement),
        //         next: Box::new(res),
        //     };
        // }
        // res
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Endpoint<'t> {
    FuncCall { span: Span<'t> },
    Unreachable,
}

impl<'t> From<Pair<'t, Rule>> for Endpoint<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        assert_eq!(value.as_rule(), Rule::endpoint);
        let span = value.as_span();
        let inner = value.into_inner().exactly_one().unwrap();
        match inner.as_rule() {
            Rule::func_call => Endpoint::FuncCall { span },
            // Rule::if_endpoint => Endpoint::If {
            //     span,
            //     cond: inner.into_inner().next().unwrap(),
            //     true_case: inner.into_inner().next().unwrap(),
            //     false_case: inner.into_inner().next().unwrap(),
            // },
            // Rule::match_block => Endpoint::MatchBlock {
            //     span,
            //     block: inner.into(),
            // },
            Rule::unreachable => Endpoint::Unreachable,
            _ => unreachable!("{:?}", inner),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call<'t> {
    pub span: Span<'t>,
    pub func: PathOrIdent<'t>,
    pub args: Vec<ValueExpression<'t>>,
}

impl<'t> From<Pair<'t, Rule>> for Call<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        let span = value.as_span();
        match value.as_rule() {
            Rule::func_call => {
                let (func, args) = value.into_inner().collect_tuple().unwrap();
                Self {
                    span,
                    func: func.into(),
                    args: args.into_inner().map(ValueExpression::from).collect(),
                }
            }

            // assert_eq!(value.as_rule(), Rule::statement);
            // let inner = value.into_inner().exactly_one().unwrap();
            // match inner.as_rule() {
            //     Rule::let_statement => {
            //         let (bindings, expr) = inner.into_inner().collect_tuple().unwrap();
            //         Statement::Bind {
            //             name: ident_from_pair(bindings.into_inner().exactly_one().unwrap()),
            //             inner: Box::new(Statement::Other(expr)),
            //         }
            //     }
            //     _ => Statement::Other(inner),
            // }
            _ => unreachable!("{:?}", value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueExpression<'t> {
    Literal(Literal<'t>),
    Path(Path<'t>),
    Identifier(Identifier<'t>),
    Copy(Identifier<'t>),
}

impl<'t> From<Pair<'t, Rule>> for ValueExpression<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        let span = value.as_span();
        match value.as_rule() {
            Rule::literal => Self::Literal(value.into()),
            Rule::path => Self::Path(value.into()),
            Rule::identifier => Self::Identifier(value.into()),
            Rule::copy => {
                let ident = value.into_inner().exactly_one().unwrap();
                Self::Copy(ident.into())
            }
            _ => unreachable!("{:?}", value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawWord<'t> {
    pub span: Span<'t>,
    pub inner: RawWordInner<'t>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawWordInner<'t> {
    Literal(Literal<'t>),
    Builtin(Span<'t>),
    FunctionLike(Identifier<'t>, usize),
    This,
}

impl<'t> From<Pair<'t, Rule>> for RawWord<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        let span = value.as_span();
        let inner = value.into_inner().exactly_one().unwrap();
        match inner.as_rule() {
            Rule::literal => Self {
                span,
                inner: RawWordInner::Literal(inner.into()),
            },
            Rule::builtin => Self {
                span,
                inner: RawWordInner::Builtin(ident_from_pair(
                    inner.into_inner().exactly_one().unwrap(),
                )),
            },
            Rule::builtin_func_call => {
                let (fname, farg) = inner.into_inner().collect_tuple().unwrap();
                assert_eq!(farg.as_rule(), Rule::int);
                Self {
                    span,
                    inner: RawWordInner::FunctionLike(fname.into(), int_from_pair(farg)),
                }
            }
            Rule::this => Self {
                span,
                inner: RawWordInner::This,
            },
            _ => unreachable!("{:?}", inner),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path<'t> {
    pub span: Span<'t>,
    pub segments: Vec<Span<'t>>,
}

impl<'t> From<Pair<'t, Rule>> for Path<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        assert_eq!(value.as_rule(), Rule::path);
        let span = value.as_span();
        let segments = value.into_inner().map(ident_from_pair).collect();
        Self { span, segments }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathOrIdent<'t> {
    Path(Path<'t>),
    Ident(Identifier<'t>),
}

impl<'t> From<Pair<'t, Rule>> for PathOrIdent<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        match value.as_rule() {
            Rule::path => Self::Path(value.into()),
            Rule::identifier => Self::Ident(value.into()),
            _ => unreachable!("unexpected rule: {:?}", value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bindings<'t> {
    pub span: Span<'t>,
    pub bindings: Vec<Binding<'t>>,
}

impl<'t> From<Pair<'t, Rule>> for Bindings<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        assert_eq!(value.as_rule(), Rule::bindings);
        Self {
            span: value.as_span(),
            bindings: value.into_inner().map(Binding::from).collect_vec(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Binding<'t> {
    Literal(Literal<'t>),
    Ident(Span<'t>),
}

impl<'t> From<Pair<'t, Rule>> for Binding<'t> {
    fn from(value: Pair<'t, Rule>) -> Self {
        match value.as_rule() {
            Rule::literal => Self::Literal(value.into()),
            Rule::identifier => Self::Ident(value.as_span()),
            _ => unreachable!("unexpected rule: {:?}", value),
        }
    }
}
