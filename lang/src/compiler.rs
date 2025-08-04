use std::collections::BTreeMap;

use crate::ast::Spanner;
use builder::{FileContext, Output};
use from_raw_ast::Spanner;
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::flat::symbol;
use crate::flat::{self, tagged};
use crate::{
    ast::{self, NamespaceDecl},
    flat::SentenceIndex,
    linker::{self, Error},
    source::{self, FileIndex, FileSpan, Sources},
};

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

impl Crate {
    pub fn from_sources(sources: &Sources) -> Result<Self, linker::Error> {
        let mut compiler = Compiler::new(sources);
        for (file_idx, file) in sources.files.iter_enumerated() {
            let parsed_file = ast::File::from_source(&file.source).unwrap();
            compiler.add_file(file.mod_name.clone(), file_idx, parsed_file)?;
        }
        Ok(compiler.build())
    }
}

//
// x => {
//   let (y, (a, b), c) = 3 'pairup;
//   (*x + 1, {
//       let z = x;
//       z
//     } + true if { y + 1 } else { let ^ = y; 0 })
// }

// x=> 3 y=> ((*x, 1) 'add, ({x z=> z}, true if { y + 1 } else { y ^=> 0 }) 'add)

// x=> 3 y=> *x 1 tuple(2) 'add x z=> z true if { y 1 tuple(2) 'add } else { y ^=> 0 } tuple(2) 'add tuple(2)

// []
// x=> [x]
// 3   [x, ?]
// 'pairup  [x, ?]
// untuple(3) [x, t0, t1, t2]
// t0       [x, t1, t2, ?]
// y=>      [x, t1, t2, y]
// t1       [x, t2, y, ?]
// untuple(2) [x, t2, y, t3, t4]
// t3
// a=>      [x, t2, y, t3]
// y=>      [x, y]
// *x       [x, y, ?]
// 1        [x, y, ?, ?]
// tuple(2) [x, y, ?]
// 'add     [x, y, ?]
// x        [y, ?, ?]
// z=>      [y, ?, z]
// z=>      [y, ?, ?]
// true     [y, ?, ?, ?]
// if
//   - y    [?, ?, ?]
//     1    [?, ?, ?, ?]
//     tuple(2) [?, ?, ?]
//     'add [?, ?, ?]
//   - y    [?, ?, ?]
//     ^=>  [?, ?]
//     0    [?, ?, ?]
// tuple(2) [?, ?]
// 'add     [?, ?]
// tuple(2) [?]

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Transformer<'t> {
    Literal(ast::Literal<'t>),
    Move(ast::Identifier<'t>),
    MoveIdx {
        span: pest::Span<'t>,
        idx: usize,
    },
    Copy(ast::Identifier<'t>),
    CopyIdx {
        span: pest::Span<'t>,
        idx: usize,
    },
    Drop(pest::Span<'t>),
    Call(ast::QualifiedLabel<'t>),
    Binding(ast::Identifier<'t>),
    Tuple {
        span: pest::Span<'t>,
        size: usize,
    },
    Untuple {
        span: pest::Span<'t>,
        size: usize,
    },
    Branch {
        span: pest::Span<'t>,
        true_case: Box<Transformer<'t>>,
        false_case: Box<Transformer<'t>>,
    },
    Composition {
        span: pest::Span<'t>,
        children: Vec<Transformer<'t>>,
    },
    AssertEq(pest::Span<'t>),
    Panic(pest::Span<'t>),
    Eq(pest::Span<'t>),
}

impl<'t> Transformer<'t> {
    pub fn from_into_fn(into_fn: ast::IntoFn<'t>) -> Self {
        match into_fn {
            ast::IntoFn::QualifiedLabel(qualified_label) => {
                Self::from_transformer(ast::Transformer::Call(qualified_label))
            }
            ast::IntoFn::AnonFn(anon_fn) => Self::from_anon_fn(anon_fn),
            ast::IntoFn::AndThen(and_then_fn) => todo!(),
            ast::IntoFn::Await(await_fn) => todo!(),
            ast::IntoFn::Loop(loop_fn) => todo!(),
            ast::IntoFn::Do(do_fn) => todo!(),
            ast::IntoFn::If(if_fn) => todo!(),
        }
    }

    pub fn from_anon_fn(anon_fn: ast::AnonFn<'t>) -> Self {
        Self::Composition {
            span: anon_fn.span,
            children: vec![
                Self::from_binding(anon_fn.binding),
                Self::from_expression(*anon_fn.body),
            ],
        }
    }

    pub fn from_root(root: ast::RootExpression<'t>) -> Self {
        match root {
            ast::RootExpression::Literal(literal) => Self::Literal(literal),
            ast::RootExpression::Identifier(identifier) => Self::Move(identifier),
            ast::RootExpression::Copy(copy) => Self::Copy(copy.0),
            ast::RootExpression::Tuple(tuple) => Self::from_tuple(tuple),
            ast::RootExpression::Tagged(tagged) => Self::from_tuple(ast::Tuple {
                span: tagged.span,
                values: vec![
                    ast::Expression {
                        span: tagged.span,
                        root: ast::RootExpression::Literal(ast::Literal::Symbol(
                            ast::Symbol::Identifier(tagged.tag),
                        )),
                        transformers: vec![],
                    },
                    ast::Expression {
                        span: tagged.span,
                        root: ast::RootExpression::Tuple(ast::Tuple {
                            span: tagged.span,
                            values: tagged.values,
                        }),
                        transformers: vec![],
                    },
                ],
            }),
            ast::RootExpression::Block(block) => Self::Composition {
                span: block.span,
                children: vec![
                    Self::Composition {
                        span: block.span,
                        children: block
                            .statements
                            .into_iter()
                            .map(Self::from_statement)
                            .collect(),
                    },
                    Self::from_expression(*block.expression),
                ],
            },
        }
    }

    pub fn from_statement(statement: ast::Statement<'t>) -> Self {
        match statement {
            ast::Statement::Let(let_statement) => Self::Composition {
                span: let_statement._span,
                children: vec![
                    Self::from_expression(let_statement.rhs),
                    Self::from_binding(let_statement.binding),
                ],
            },
        }
    }

    pub fn from_binding(binding: ast::Binding<'t>) -> Self {
        fn from_tuple<'t>(
            span: pest::Span<'t>,
            bindings: Vec<ast::Binding<'t>>,
        ) -> (Transformer<'t>, i32) {
            let mut children = vec![Transformer::Untuple {
                span,
                size: bindings.len(),
            }];
            let mut stack_size = bindings.len() as i32;
            for binding in bindings {
                children.push(Transformer::MoveIdx {
                    span: binding.pest_span(),
                    idx: stack_size as usize - 1,
                });
                let (transformer, pushed) = helper(binding);
                children.push(transformer);
                stack_size += pushed;
            }
            (Transformer::Composition { span, children }, stack_size - 1)
        }

        fn helper<'t>(binding: ast::Binding<'t>) -> (Transformer<'t>, i32) {
            match binding {
                ast::Binding::Identifier(identifier) => (Transformer::Binding(identifier), 0),
                ast::Binding::Drop(drop) => (Transformer::Drop(drop.span), -1),
                ast::Binding::Tuple(tuple) => from_tuple(tuple.span, tuple.bindings),
                ast::Binding::Literal(literal) => {
                    let span = literal.pest_span();
                    (
                        Transformer::Composition {
                            span,
                            children: vec![
                                Transformer::Literal(literal),
                                Transformer::AssertEq(span),
                            ],
                        },
                        -1,
                    )
                }
                ast::Binding::Tagged(tagged) => from_tuple(
                    tagged.span,
                    vec![
                        ast::Binding::Literal(ast::Literal::Symbol(ast::Symbol::Identifier(
                            tagged.tag,
                        ))),
                        ast::Binding::Tuple(ast::TupleBinding {
                            span: tagged.span,
                            bindings: tagged.bindings,
                        }),
                    ],
                ),
            }
        }
        let (transformer, _) = helper(binding);
        transformer
    }

    pub fn from_expression(expression: ast::Expression<'t>) -> Self {
        Self::Composition {
            span: expression.span,
            children: vec![
                Self::from_root(expression.root),
                Self::Composition {
                    span: expression.span,
                    children: expression
                        .transformers
                        .into_iter()
                        .map(Self::from_transformer)
                        .collect(),
                },
            ],
        }
    }

    pub fn from_transformer(transformer: ast::Transformer<'t>) -> Self {
        match transformer {
            ast::Transformer::Call(call) => Self::Call(call),
            ast::Transformer::InlineCall(inline_call) => match inline_call {
                ast::IntoFn::QualifiedLabel(label) => Self::Call(label),
                ast::IntoFn::AnonFn(anon_fn) => Self::from_anon_fn(anon_fn),
                _ => {
                    todo!("inline call: {:?}", inline_call);
                }
            },
            ast::Transformer::Match(match_expression) => {
                let mut else_case = Self::Panic(match_expression.span);

                for case in match_expression.cases.into_iter().rev() {
                    else_case = Self::Composition {
                        span: case.span,
                        children: vec![
                            Self::CopyIdx {
                                span: case.span,
                                idx: 0,
                            },
                            Self::transformer_for_matching(&case.binding),
                            Self::Branch {
                                span: case.span,
                                true_case: Box::new(Self::Composition {
                                    span: case.span,
                                    children: vec![
                                        Self::from_binding(case.binding),
                                        Self::from_expression(case.rhs),
                                    ],
                                }),
                                false_case: Box::new(else_case),
                            },
                        ],
                    };
                }
                else_case
            }
            ast::Transformer::If(if_expression) => Self::Branch {
                span: if_expression.span,
                true_case: Box::new(Self::from_expression(*if_expression.true_case)),
                false_case: Box::new(Self::from_expression(*if_expression.false_case)),
            },
        }
    }

    pub fn from_tuple(tuple: ast::Tuple<'t>) -> Self {
        let size = tuple.values.len();
        let children = tuple
            .values
            .into_iter()
            .map(Self::from_expression)
            .collect::<Vec<_>>();
        Self::Composition {
            span: tuple.span,
            children: vec![
                Self::Composition {
                    span: tuple.span,
                    children,
                },
                Self::Tuple {
                    span: tuple.span,
                    size,
                },
            ],
        }
    }

    pub fn flatten(self) -> Self {
        match self {
            Transformer::Composition { span, children } => {
                let mut flattened_children = Vec::new();
                for child in children {
                    let flattened_child = child.flatten();
                    match flattened_child {
                        Transformer::Composition {
                            children: nested_children,
                            ..
                        } => {
                            flattened_children.extend(nested_children);
                        }
                        _ => {
                            flattened_children.push(flattened_child);
                        }
                    }
                }
                Transformer::Composition {
                    span,
                    children: flattened_children,
                }
            }
            Transformer::Branch {
                span,
                true_case,
                false_case,
            } => Transformer::Branch {
                span,
                true_case: Box::new(true_case.flatten()),
                false_case: Box::new(false_case.flatten()),
            },
            // For all other variants, return as-is since they don't contain nested Transformers
            other => other,
        }
    }

    pub fn transformer_for_matching(binding: &ast::Binding<'t>) -> Self {
        let span = binding.pest_span();
        match binding {
            ast::Binding::Drop(_) | ast::Binding::Identifier(_) => Self::Composition {
                span,
                children: vec![
                    Self::Drop(span),
                    Self::Literal(ast::Literal::Bool(ast::Bool { span, value: true })),
                ],
            },
            ast::Binding::Tuple(tuple_binding) => {
                let size = tuple_binding.bindings.len();

                let mut true_case =
                    Self::Literal(ast::Literal::Bool(ast::Bool { span, value: true }));
                for (i, binding) in tuple_binding.bindings.iter().enumerate().rev() {
                    let mut children = vec![];
                    let top = size - i - 1;
                    children.push(Self::MoveIdx { span, idx: top });
                    children.push(Self::transformer_for_matching(binding));

                    let mut false_case_children = vec![];
                    for i in 0..top {
                        false_case_children.push(Self::Drop(span));
                    }
                    false_case_children.push(Self::Literal(ast::Literal::Bool(ast::Bool {
                        span,
                        value: false,
                    })));

                    children.push(Self::Branch {
                        span,
                        true_case: Box::new(true_case),
                        false_case: Box::new(Self::Composition {
                            span: span,
                            children: false_case_children,
                        }),
                    });

                    true_case = Self::Composition { span, children };
                }
                Self::Composition {
                    span,
                    children: vec![Self::Untuple { span, size }, true_case],
                }
            }
            ast::Binding::Tagged(tagged_binding) => Self::transformer_for_matching(
                &ast::Binding::Tuple(builder::tagged_to_tuple(tagged_binding.clone())),
            ),
            ast::Binding::Literal(l) => Self::Composition {
                span,
                children: vec![Self::Literal(l.clone()), Self::Eq(span)],
            },
        }
    }

    fn into_recursive_sentence(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
        locals: &mut Locals,
    ) -> Result<RecursiveSentence, Error> {
        match self {
            Transformer::Literal(literal) => {
                let span = literal.span(ctx.file_idx);
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Push(literal.into_value())],
                ))
            }
            Transformer::Move(identifier) => {
                let span = identifier.span(ctx.file_idx);
                let Some(idx) = locals.find(
                    ctx.sources,
                    identifier.clone().into_ir(ctx.sources, ctx.file_idx),
                ) else {
                    return Err(Error::UnknownReference {
                        location: span.location(ctx.sources),
                        name: identifier.0.as_str().to_owned(),
                    });
                };
                locals.remove(idx);
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Move(idx)],
                ))
            }
            Transformer::MoveIdx { span, idx } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.remove(idx);
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Move(idx)],
                ))
            }
            Transformer::Copy(identifier) => {
                let span = identifier.span(ctx.file_idx);
                let Some(idx) = locals.find(
                    ctx.sources,
                    identifier.clone().into_ir(ctx.sources, ctx.file_idx),
                ) else {
                    return Err(Error::UnknownReference {
                        location: span.location(ctx.sources),
                        name: identifier.0.as_str().to_owned(),
                    });
                };
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Copy(idx)],
                ))
            }
            Transformer::CopyIdx { span, idx } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Copy(idx)],
                ))
            }
            Transformer::Drop(span) => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Drop(0)],
                ))
            }
            Transformer::Call(qualified_label) => {
                let span = qualified_label.span(ctx.file_idx);

                let qualified = symbol_table.resolve(
                    ctx.sources,
                    qualified_label.into_ir(ctx.sources, ctx.file_idx),
                );
                locals.pop();
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Call(qualified)],
                ))
            }
            Transformer::Binding(identifier) => {
                let span = identifier.span(ctx.file_idx);
                locals.pop();
                locals.push_named(identifier.span(ctx.file_idx));
                Ok(RecursiveSentence::single_span(span, vec![]))
            }
            Transformer::Tuple { span, size } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                for _ in 0..size {
                    locals.pop();
                }
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Tuple(size)],
                ))
            }
            Transformer::Untuple { span, size } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                for _ in 0..size {
                    locals.push_unnamed();
                }
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Untuple(size)],
                ))
            }
            Transformer::Branch {
                span,
                true_case,
                false_case,
            } => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);

                locals.pop();

                let mut true_locals = locals.clone();
                let mut false_locals = locals.clone();
                let true_sentence =
                    true_case.into_recursive_sentence(ctx, symbol_table, &mut true_locals)?;
                let false_sentence =
                    false_case.into_recursive_sentence(ctx, symbol_table, &mut false_locals)?;

                if !true_locals.compare(ctx.sources, &false_locals) {
                    return Err(Error::BranchContractsDisagree {
                        location: span.location(ctx.sources),
                        locals1: true_locals
                            .names()
                            .into_iter()
                            .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                            .collect(),
                        locals2: false_locals
                            .names()
                            .into_iter()
                            .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                            .collect(),
                    });
                }
                if true_locals.terminal {
                    *locals = false_locals;
                } else {
                    *locals = true_locals;
                }

                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Branch(true_sentence, false_sentence)],
                ))
            }
            Transformer::Composition { span, children } => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                let mut words = vec![];
                for child in children {
                    words.push(InnerWord::InlineCall(child.into_recursive_sentence(
                        ctx,
                        symbol_table,
                        locals,
                    )?));
                }
                Ok(RecursiveSentence::single_span(span, words))
            }
            Transformer::AssertEq(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                locals.pop();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Builtin(flat::Builtin::AssertEq)],
                ))
            }
            Transformer::Panic(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.terminal = true;
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Builtin(flat::Builtin::Panic)],
                ))
            }
            Transformer::Eq(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                locals.pop();
                locals.push_unnamed();
                Ok(RecursiveSentence::single_span(
                    span,
                    vec![InnerWord::Builtin(flat::Builtin::Eq)],
                ))
            }
        }
    }
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
        file: ast::File<'t>,
    ) -> Result<(), linker::Error> {
        self.visit_namespace(file_idx, &name_prefix, file.ns)
    }

    fn visit_namespace(
        &mut self,
        file_idx: FileIndex,
        name_prefix: &QualifiedName,
        ns: ast::Namespace<'t>,
    ) -> Result<(), linker::Error> {
        let mut symbol_table = SymbolTable {
            prefix: name_prefix.clone(),
            uses: BTreeMap::new(),
        };
        for r#use in ns.uses {
            let path = r#use.path.into_ir(self.sources, file_idx);

            symbol_table
                .uses
                .insert(path.0.last().unwrap().as_str(self.sources).unwrap(), path);
        }

        for decl in ns.decl {
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
                ast::Decl::Fn(ast::FnDecl {
                    span,
                    binding,
                    name,
                    expression,
                }) => {
                    let name = name_prefix.append(name.into_ir(self.sources, file_idx));
                    self.visit_fn(span, file_idx, &symbol_table, binding, name, expression)?;
                }
                ast::Decl::Def(ast::DefDecl {
                    span,
                    name,
                    transformer,
                }) => {
                    let name = name_prefix.append(name.into_ir(self.sources, file_idx));
                    self.visit_def(span, file_idx, &symbol_table, name, transformer)?;
                }
            }
        }
        Ok(())
    }

    fn visit_fn(
        &mut self,
        span: pest::Span<'t>,
        file_idx: FileIndex,
        symbol_table: &SymbolTable,
        binding: ast::Binding,
        name: QualifiedName,
        expression: ast::Expression,
    ) -> Result<(), linker::Error> {
        let ctx = FileContext {
            file_idx,
            sources: self.sources,
        };
        let anon = ast::AnonFn {
            span,
            binding: binding.clone(),
            body: Box::new(expression),
        };

        let transformer = Transformer::from_anon_fn(anon);

        let mut locals = Locals::default();
        locals.push_unnamed();
        let sentence = transformer.into_recursive_sentence(ctx, &symbol_table, &mut locals)?;

        let mut names = NameSequence {
            base: name,
            count: 0,
        };
        self.visit_recursive_sentence(&mut names, sentence);
        Ok(())
    }

    fn visit_def(
        &mut self,
        span: pest::Span<'t>,
        file_idx: FileIndex,
        symbol_table: &SymbolTable,
        name: QualifiedName,
        into_fn: ast::Transformer<'t>,
    ) -> Result<(), linker::Error> {
        let ctx = FileContext {
            file_idx,
            sources: self.sources,
        };

        let transformer = Transformer::from_transformer(into_fn);

        let mut locals = Locals::default();
        locals.push_unnamed();
        let sentence = transformer.into_recursive_sentence(ctx, &symbol_table, &mut locals)?;
        if locals.len() != 1 {
            locals.pop();
            match locals.pop() {
                Name::User(file_span) => {
                    return Err(linker::Error::UnusedVariable {
                        location: file_span.location(self.sources),
                        name: file_span.as_str(self.sources).to_owned(),
                    })
                }
                Name::Generated(idx) => panic!("Leaked generated variable?? ${}", idx),
            }
        }
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
            ast::Word::Builtin(builtin) => Ok(Word {
                span: builtin.span.into_ir(self.sources, file_idx),
                inner: self.convert_builtin(file_idx, builtin)?,
                names: vec![],
            }),
            ast::Word::Literal(literal) => Ok(Word {
                span: literal.span(file_idx),
                inner: InnerWord::Push(literal.into_value()),
                names: vec![],
            }),
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
            InnerWord::InlineCall(sentence) => {
                let name = self.visit_recursive_sentence(names, sentence);
                InnerWord::InlineCall(name)
            }
            InnerWord::Branch(true_case, false_case) => InnerWord::Branch(
                self.visit_recursive_sentence(names, true_case),
                self.visit_recursive_sentence(names, false_case),
            ),
            InnerWord::JumpTable(jump_table) => InnerWord::JumpTable(
                jump_table
                    .into_iter()
                    .map(|sentence| self.visit_recursive_sentence(names, sentence))
                    .collect(),
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
            .map(|(_scope, name)| name)
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

    fn _push_scope(&mut self) -> usize {
        assert!(!self.terminal);
        self.scope += 1;
        self.scope
    }

    fn _collapse_scope(&mut self) {
        assert!(!self.terminal);
        assert!(!self.stack.iter().any(|(s, _)| *s == self.scope - 1));
        for (s, _) in self.stack.iter_mut() {
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

    fn _check_consumed(&mut self, sources: &Sources, name: FileSpan) -> Result<(), Error> {
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

    fn _prev_scope(&self) -> Vec<Name> {
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
            .position(|(_, n)| n.as_ref(sources) == name.as_ref(sources))?;
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
    InlineCall {
        span: pest::Span<'t>,
        arg: Box<Expression<'t>>,
        into_fn: IntoFn<'t>,
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
            Some(ast::Transformer::InlineCall(into_fn)) => Self::InlineCall {
                span: a.span,
                into_fn: IntoFn::from_ast(into_fn),
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
            ast::RootExpression::Tagged(tagged) => {
                let values = vec![
                    Self::Literal(ast::Literal::Symbol(ast::Symbol::Identifier(tagged.tag))),
                    Self::Tuple {
                        span: tagged.span,
                        values: tagged
                            .values
                            .into_iter()
                            .map(Expression::from_ast)
                            .collect(),
                    },
                ];

                Self::Tuple {
                    span: tagged.span,
                    values,
                }
            }
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
        symbol_table: &SymbolTable,
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
                span: _,
                binding,
                rhs,
                inner,
            } => {
                let () = rhs.compilation(ctx, symbol_table, out)?;

                let () = builder::binding(ctx, binding, out)?;

                let () = inner.compilation(ctx, symbol_table, out)?;
                // TODO: Check scope leakage?
                Ok(())
            }
            Expression::Tuple { span, values } => {
                let span = span.span(ctx.file_idx);

                let len = values.len();
                for v in values {
                    let () = v.compilation(ctx, symbol_table, out)?;
                }
                builder::tuple(ctx, span, len, out);
                Ok(())
            }
            Expression::Call { span, arg, label } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                let () = arg.compilation(ctx, symbol_table, out)?;

                let qualified =
                    symbol_table.resolve(ctx.sources, label.into_ir(ctx.sources, ctx.file_idx));
                out.words.push(RecursiveWord {
                    span,
                    inner: InnerWord::Call(qualified),
                    names: out.locals.names(),
                });

                out.locals.pop();
                out.locals.push_unnamed();

                Ok(())
            }
            Expression::InlineCall { span, arg, into_fn } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                let () = arg.compilation(ctx, symbol_table, out)?;

                let sentence = into_fn.compilation(ctx, symbol_table)?;
                out.words.push(RecursiveWord {
                    span,
                    inner: InnerWord::InlineCall(sentence),
                    names: out.locals.names(),
                });
                out.locals.pop();
                out.locals.push_unnamed();

                Ok(())
            }
            Expression::Match { span, arg, cases } => {
                let span = span.span(ctx.file_idx);
                let () = arg.compilation(ctx, symbol_table, out)?;

                let mut else_case_out: Box<dyn FnOnce(&mut Output) -> Result<(), Error>> =
                    Box::new(|out: &mut Output| {
                        let () = builder::unreachable(span, out);
                        Ok(())
                    });

                for case in cases.into_iter().rev() {
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
                                case.rhs.compilation(ctx, symbol_table, out)
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

                let () = cond.compilation(ctx, symbol_table, out)?;

                builder::conditional(
                    ctx,
                    span,
                    true_span,
                    |out| true_case.compilation(ctx, symbol_table, out),
                    false_span,
                    |out| false_case.compilation(ctx, symbol_table, out),
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
            Expression::LetBlock { span, .. } => *span,
            Expression::Tuple { span, .. } => *span,
            Expression::Call { span, .. } => *span,
            Expression::InlineCall { span, .. } => *span,
            Expression::Match { span, .. } => *span,
            Expression::If { span, .. } => *span,
        }
    }
}

#[derive(Debug)]
pub enum IntoFn<'t> {
    AnonFn(AnonFn<'t>),
    AndThen(AndThenFn<'t>),
    Await(AwaitFn<'t>),
    Do(DoFn<'t>),
    Loop(LoopFn<'t>),
    If(IfFn<'t>),
}
impl<'t> IntoFn<'t> {
    pub fn from_ast(into_fn: ast::IntoFn<'t>) -> Self {
        match into_fn {
            ast::IntoFn::QualifiedLabel(label) => unreachable!(),
            ast::IntoFn::AnonFn(anon_fn) => IntoFn::AnonFn(AnonFn {
                span: anon_fn.span,
                binding: anon_fn.binding,
                body: Box::new(Expression::from_ast(*anon_fn.body)),
            }),
            ast::IntoFn::AndThen(ast::AndThenFn {
                span,
                first,
                second,
            }) => IntoFn::AndThen(AndThenFn {
                span,
                first: Box::new(IntoFn::from_ast(*first)),
                second: Box::new(IntoFn::from_ast(*second)),
            }),
            ast::IntoFn::Await(ast::AwaitFn { span, body }) => IntoFn::Await(AwaitFn {
                span,
                body: Box::new(IntoFn::from_ast(*body)),
            }),
            ast::IntoFn::Do(do_fn) => IntoFn::Do(DoFn {
                span: do_fn.span,
                body: Box::new(IntoFn::from_ast(*do_fn.body)),
            }),
            ast::IntoFn::Loop(ast::LoopFn { span, body }) => IntoFn::Loop(LoopFn {
                span,
                body: Box::new(IntoFn::from_ast(*body)),
            }),
            ast::IntoFn::If(ast::IfFn {
                span,
                true_case,
                false_case,
            }) => IntoFn::If(IfFn {
                span,
                true_case: Box::new(IntoFn::from_ast(*true_case)),
                false_case: Box::new(IntoFn::from_ast(*false_case)),
            }),
        }
    }

    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        match self {
            IntoFn::AnonFn(anon_fn) => anon_fn.compilation(ctx, symbol_table),
            IntoFn::AndThen(and_then_fn) => and_then_fn.compilation(ctx, symbol_table),
            IntoFn::Await(await_fn) => await_fn.compilation(ctx, symbol_table),
            IntoFn::Do(do_fn) => do_fn.compilation(ctx, symbol_table),
            IntoFn::Loop(loop_fn) => loop_fn.compilation(ctx, symbol_table),
            IntoFn::If(if_fn) => if_fn.compilation(ctx, symbol_table),
        }
    }
}

#[derive(Debug, Spanner)]
pub struct AnonFn<'t> {
    pub span: pest::Span<'t>,
    pub binding: ast::Binding<'t>,
    pub body: Box<Expression<'t>>,
}

impl<'t> AnonFn<'t> {
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span: FileSpan = self.span(ctx.file_idx);

        let mut out = Output {
            words: vec![],
            locals: Locals::default(),
        };
        out.locals.push_unnamed();
        let () = builder::binding(ctx, self.binding, &mut out)?;

        let () = self.body.compilation(ctx, symbol_table, &mut out)?;

        if out.locals.len() != 1 {
            let Name::User(name) = out.locals.names()[1] else {
                panic!("unused generated name?")
            };
            return Err(Error::UnusedVariable {
                location: name.location(ctx.sources),
                name: name.as_str(ctx.sources).to_owned(),
            });
        }

        Ok(RecursiveSentence {
            span,
            words: out.words,
        })
    }
}

#[derive(Debug, Spanner)]
pub struct AndThenFn<'t> {
    pub span: pest::Span<'t>,
    pub first: Box<IntoFn<'t>>,
    pub second: Box<IntoFn<'t>>,
}

macro_rules! word {
    (push(@ $sym:ident)) => {
        InnerWord::Push(flat::Value::Symbol(stringify!($sym).to_owned()))
    };
    (push($val:expr)) => {
        InnerWord::Push(flat::Value::from($val))
    };
    (tuple($val:expr)) => {
        InnerWord::Tuple($val)
    };
    (untuple($val:expr)) => {
        InnerWord::Untuple($val)
    };
    (mv($val:expr)) => {
        InnerWord::Move($val)
    };
    (cp($val:expr)) => {
        InnerWord::Copy($val)
    };
    (inline_call($call:expr)) => {
        InnerWord::InlineCall($call)
    };
    (branch($true_case:expr, $false_case:expr)) => {
        InnerWord::Branch($true_case, $false_case)
    };
    (jump_table($cases:expr)) => {
        InnerWord::JumpTable($cases)
    };
    ($tag:ident) => {
        InnerWord::Builtin(flat::Builtin::$tag)
    };
}

macro_rules! sentence {
    [$($tag:ident$(($($args:tt)*))?,)*] => {vec![$(word!($tag$(($($args)*))?),)*]};
}

impl<'t> AndThenFn<'t> {
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span = self.span(ctx.file_idx);

        let call_b_if_req = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (state, msg) @req
                push(@req), AssertEq, untuple(2),

                // Stack: state msg
                mv(1), push(1), tuple(2),

                // Stack: msg (state, 1)
                mv(1), tuple(2), push(@req), tuple(2),
            ],
        );
        let call_b_if_resp = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (val) @resp
                push(@resp), AssertEq,
                // Stack: (val)
                push(@resp), tuple(2),
            ],
        );

        let call_b = RecursiveSentence::single_span(
            span,
            sentence![
                inline_call(self.second.compilation(ctx, symbol_table)?),
                untuple(2),
                // Stack: (?, @req|@resp)
                cp(0),
                push(@req),
                Eq,
                branch(call_b_if_req, call_b_if_resp),
            ],
        );

        let call_a_if_req = RecursiveSentence::single_span(
            span,
            vec![
                // Stack: (state, msg) @req
                InnerWord::Push(flat::Value::Symbol("req".to_owned())),
                InnerWord::Builtin(flat::Builtin::AssertEq),
                InnerWord::Untuple(2),
                // Stack: state msg
                InnerWord::Move(1),
                InnerWord::Push(flat::Value::Usize(0)),
                InnerWord::Tuple(2),
                // Stack: msg (state, 0)
                InnerWord::Move(1),
                InnerWord::Tuple(2),
                InnerWord::Push(flat::Value::Symbol("req".to_owned())),
                InnerWord::Tuple(2),
            ],
        );
        let call_a_if_resp = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (val) @resp
                push(@resp), AssertEq,
                // Stack: (val)
                push(@resp), tuple(2),
                inline_call(call_b.clone()),
            ],
        );

        let call_a = RecursiveSentence::single_span(
            span,
            vec![
                InnerWord::InlineCall(self.first.compilation(ctx, symbol_table)?),
                // Stack: (?, @req|@resp)
                InnerWord::Untuple(2),
                InnerWord::Copy(0),
                InnerWord::Push(flat::Value::Symbol("req".to_owned())),
                InnerWord::Builtin(flat::Builtin::Eq),
                InnerWord::Branch(call_a_if_req, call_a_if_resp),
            ],
        );

        let if_call = RecursiveSentence::single_span(
            span,
            vec![
                // Stack: args @call
                InnerWord::Push(flat::Value::Symbol("call".to_owned())),
                InnerWord::Builtin(flat::Builtin::AssertEq),
                InnerWord::Push(flat::Value::Symbol("call".to_owned())),
                InnerWord::Tuple(2),
                InnerWord::InlineCall(call_a.clone()),
            ],
        );

        let if_reply = RecursiveSentence::single_span(
            span,
            vec![
                // Stack: ((state, case), msg) @reply
                InnerWord::Push(flat::Value::Symbol("reply".to_owned())),
                InnerWord::Builtin(flat::Builtin::AssertEq),
                // Stack: ((state, case), msg)
                InnerWord::Untuple(2),
                InnerWord::Move(1),
                InnerWord::Untuple(2),
                // Stack: msg state case
                InnerWord::Move(2),
                InnerWord::Move(2),
                InnerWord::Move(1),
                // Stack: case state msg
                InnerWord::Tuple(2),
                InnerWord::Push(flat::Value::Symbol("reply".to_owned())),
                InnerWord::Tuple(2),
                InnerWord::Move(1),
                // Stack: (state, msg) case
                InnerWord::JumpTable(vec![call_a, call_b]),
            ],
        );

        Ok(RecursiveSentence::single_span(
            span,
            vec![
                // Stack: (?, @call|@reply)
                InnerWord::Untuple(2),
                InnerWord::Copy(0),
                InnerWord::Push(flat::Value::Symbol("call".to_owned())),
                InnerWord::Builtin(flat::Builtin::Eq),
                InnerWord::Branch(if_call, if_reply),
            ],
        ))
    }
}

#[derive(Debug, Spanner)]
pub struct AwaitFn<'t> {
    pub span: pest::Span<'t>,
    pub body: Box<IntoFn<'t>>,
}

impl<'t> AwaitFn<'t> {
    // fn await<T> = match {
    //     #call{args} => args T
    //     #reply{state, msg} => #resp{state, msg},
    //   }
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span = self.span(ctx.file_idx);
        let if_call = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (args) @call
                push(@call), AssertEq, untuple(1),
                inline_call(self.body.compilation(ctx, symbol_table)?),
            ],
        );

        let if_reply = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (state, msg) @reply
                push(@reply), AssertEq,
                // Stack: (state, msg)
                tuple(1), push(@resp), tuple(2),
            ],
        );

        Ok(RecursiveSentence::single_span(
            span,
            sentence![
                untuple(2),
                // Stack: (?, @call|@reply)
                cp(0),
                push(@call),
                Eq,
                branch(if_call, if_reply),
            ],
        ))
    }
}

#[derive(Debug, Spanner)]
pub struct DoFn<'t> {
    pub span: pest::Span<'t>,
    pub body: Box<IntoFn<'t>>,
}

impl<'t> DoFn<'t> {
    // fn args do<T> => {
    //   let #call{args} = args;
    //   #resp{args T}
    // }
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span = self.span(ctx.file_idx);
        Ok(RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: #call{args}
                untuple(2), push(@call), AssertEq,
                // Stack: (args)
                untuple(1), inline_call(self.body.compilation(ctx, symbol_table)?),
                // Stack: resp
                tuple(1), push(@resp), tuple(2),
            ],
        ))
    }
}

#[derive(Debug, Spanner)]
pub struct LoopFn<'t> {
    pub span: pest::Span<'t>,
    pub body: Box<IntoFn<'t>>,
}
impl<'t> LoopFn<'t> {
    // fn loop<T> => match {
    //   #call{args} => #call{args} T {
    //     #req{state, msg} => #req{(state, 0), msg},
    //     #resp{#break{val}} => #resp{val},
    //     #resp{#continue{state}} => #req{((), 1), #stall{state}},
    //   }
    //   #reply{(state, 0), msg} => #reply{state, msg} T ...
    //   #reply{((), 1), state} => #call{state} T ...
    // }
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span = self.span(ctx.file_idx);

        let call_body_if_req = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (state, msg) @req
                push(@req), AssertEq, untuple(2),
                // Stack: state msg
                mv(1), push(0), tuple(2),
                // Stack: msg (state, 0)
                mv(1), tuple(2),
                // Stack: ((state, 0), msg)
                push(@req), tuple(2),
            ],
        );
        let call_body_if_resp_break = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (val) @break
                push(@break), AssertEq,
                // Stack: (val)
                push(@resp), tuple(2),
            ],
        );
        let call_body_if_resp_continue = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (state) @continue
                push(@continue), AssertEq, untuple(1),
                // Stack: state
                tuple(1), push(@stall), tuple(2),
                // Stack: #stall{state}
                tuple(0), push(1), tuple(2), mv(1),
                // Stack: ((), 1) #stall{state}
                tuple(2), push(@req), tuple(2),
                // Stack: #req{((), 1), #stall{state}}
            ],
        );

        let call_body_if_resp = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: ((?, @break|@continue)) @resp
                push(@resp), AssertEq, untuple(1), untuple(2),
                // Stack: ? @break|@continue
                cp(0), push(@break), Eq, branch(
                    call_body_if_resp_break,
                    call_body_if_resp_continue
                ),
            ],
        );
        let call_body = RecursiveSentence::single_span(
            span,
            sentence![
                inline_call(self.body.compilation(ctx, symbol_table)?),
                // Stack: (?, @req|@resp)
                untuple(2),
                cp(0),
                push(@req),
                Eq,
                branch(call_body_if_req, call_body_if_resp),
            ],
        );

        let if_call = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (args) @call
                cp(0), push(@call), AssertEq, tuple(2),
                inline_call(call_body.clone()),
            ],
        );
        let if_reply_to_req = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: msg state
                mv(1), tuple(2), push(@reply), tuple(2),
                // Stack: #reply{state, msg}
                inline_call(call_body.clone()),
            ],
        );

        let if_reply_to_stall = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: state ()
                untuple(0),
                // state
                tuple(1), push(@call), tuple(2),
                // Stack: #call{state}
                inline_call(call_body),
            ],
        );

        let if_reply = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: ((?, case), msg) @reply
                push(@reply), AssertEq, untuple(2),
                // Stack: (?, case) msg
                mv(1), untuple(2),
                // Stack: msg ? case
                jump_table(vec![
                    if_reply_to_req,
                    if_reply_to_stall,
                ]),
            ],
        );

        Ok(RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (?, @call|@reply)
                untuple(2),
                cp(0),
                push(@call),
                Eq,
                branch(if_call, if_reply),
            ],
        ))
    }
}

#[derive(Debug, Spanner)]
pub struct IfFn<'t> {
    pub span: pest::Span<'t>,
    pub true_case: Box<IntoFn<'t>>,
    pub false_case: Box<IntoFn<'t>>,
}

impl<'t> IfFn<'t> {
    // fn if<T, F> => match {
    //   #call{(arg, cond)} => cond if {
    //     arg T match {
    //         #req{state, msg} => #req{(state, true), msg},
    //         #resp{msg} => #resp{msg},
    //     }
    //   } else {
    //     arg F match {
    //         #req{state, msg} => #req{(state, false), msg},
    //         #resp{msg} => #resp{msg},
    //     }
    //   }
    //   #reply{(state, true), msg} => #reply{state, msg} T ...,
    //   #reply{(state, false), msg} => #reply{state, msg} F ...,
    // }
    fn compilation(
        self,
        ctx: FileContext,
        symbol_table: &SymbolTable,
    ) -> Result<RecursiveSentence, Error> {
        let span = self.span(ctx.file_idx);

        fn call_if_req(span: FileSpan, cond: bool) -> RecursiveSentence {
            RecursiveSentence::single_span(
                span,
                sentence![
                    // Stack: (state, msg) @req
                    push(@req), AssertEq, untuple(2),
                    // Stack: state msg
                    mv(1), push(cond), tuple(2),
                    // Stack: msg (state, cond)
                    mv(1), tuple(2),
                    // Stack: ((state, cond), msg)
                    push(@req), tuple(2),
                    // Stack: #req{(state, cond), msg}
                ],
            )
        }
        let call_either_if_resp = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (val) @resp
                push(@resp), AssertEq,
                // Stack: (val)
                push(@resp), tuple(2),
            ],
        );

        let call_true = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: args
                inline_call(self.true_case.compilation(ctx, symbol_table)?),
                untuple(2),
                // Stack: ? @req|@resp
                cp(0), push(@req), Eq,
                branch(call_if_req(span, true), call_either_if_resp.clone()),
            ],
        );

        let call_false = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: args
                inline_call(self.false_case.compilation(ctx, symbol_table)?),
                untuple(2),
                // Stack: ? @req|@resp
                cp(0), push(@req), Eq,
                branch(call_if_req(span, false), call_either_if_resp),
            ],
        );

        let if_reply_and_true = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: msg state
                mv(1), tuple(2), push(@reply), tuple(2),
                // Stack: #reply{state, msg}
                inline_call(call_true.clone()),
            ],
        );

        let if_reply_and_false = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: msg state
                mv(1), tuple(2), push(@reply), tuple(2),
                // Stack: #reply{state, msg}
                inline_call(call_false.clone()),
            ],
        );

        let if_reply = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: ((state, cond), msg) @reply
                push(@reply), AssertEq, untuple(2),
                // Stack: (state, cond) msg
                mv(1), untuple(2),
                // Stack: msg state cond
                branch(
                    if_reply_and_true,
                    if_reply_and_false
                ),
            ],
        );

        let if_call = RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (arg, cond) @call
                push(@call), AssertEq, untuple(1), untuple(2), mv(1),

                // Stack: cond arg
                tuple(1), push(@call), tuple(2), mv(1),

                // Stack: #call{arg} cond
                branch(
                    call_true,
                    call_false
                ),
            ],
        );

        Ok(RecursiveSentence::single_span(
            span,
            sentence![
                // Stack: (?, @call|@reply)
                untuple(2),
                cp(0),
                push(@call),
                Eq,
                branch(if_call, if_reply),
            ],
        ))
    }
}

struct SymbolTable<'t> {
    prefix: QualifiedName,
    uses: BTreeMap<&'t str, QualifiedName>,
}

impl<'t> SymbolTable<'t> {
    pub fn resolve(&self, sources: &Sources, name: QualifiedName) -> QualifiedName {
        let mut path = if let Some(resolved) = self
            .uses
            .get(name.0.first().unwrap().as_ref(sources).as_str().unwrap())
        {
            resolved.join(QualifiedName(name.0.into_iter().skip(1).collect()))
        } else {
            self.prefix.join(name)
        };

        let path = loop {
            let Some(super_idx) = path
                .0
                .iter()
                .position(|n| n.as_ref(sources) == NameRef::User("super"))
            else {
                break path;
            };
            path.0.remove(super_idx - 1);
            path.0.remove(super_idx - 1);
        };
        let path = if let Some(crate_idx) = path
            .0
            .iter()
            .position(|n| n.as_ref(sources) == NameRef::User("crate"))
        {
            QualifiedName(path.0.iter().skip(crate_idx + 1).cloned().collect())
        } else {
            path
        };
        path.append(Name::Generated(0))
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

impl RecursiveSentence {
    fn single_span(
        span: FileSpan,
        words: impl IntoIterator<Item = InnerWord<RecursiveSentence>>,
    ) -> Self {
        Self {
            span,
            words: words
                .into_iter()
                .map(|inner| RecursiveWord {
                    span,
                    inner,
                    names: vec![],
                })
                .collect(),
        }
    }
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
    InlineCall(BranchRepr),
    Branch(BranchRepr, BranchRepr),
    JumpTable(Vec<BranchRepr>),
}

pub trait IntoIr<'t, I> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> I;
}

impl<'t> IntoIr<'t, source::FileSpan> for pest::Span<'_> {
    fn into_ir(self, _sources: &'t Sources, file_idx: FileIndex) -> source::FileSpan {
        source::FileSpan::from_ast(file_idx, self)
    }
}
impl<'t> IntoIr<'t, source::Location> for pest::Span<'_> {
    fn into_ir(self, sources: &'t Sources, file_idx: FileIndex) -> source::Location {
        source::FileSpan::from_ast(file_idx, self).location(sources)
    }
}

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

    pub fn literal(ctx: FileContext, value: ast::Literal, output: &mut Output) {
        let span = value.span(ctx.file_idx);
        push_value(span, value.into_value(), output)
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
        FileContext { sources, .. }: FileContext,
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
        locals.remove(idx);
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

    pub fn cp_idx(_ctx: FileContext, span: FileSpan, idx: usize, out: &mut Output) {
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

    pub fn drop_idx(_ctx: FileContext, span: FileSpan, idx: usize, out: &mut Output) {
        let names = out.locals.names();
        out.locals.remove(idx);

        out.words.push(RecursiveWord {
            inner: InnerWord::Drop(idx),
            span,
            names,
        });
    }

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
            ast::Binding::Drop(_) => {
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

                for (name, b) in tmp_names
                    .into_iter()
                    .zip_eq(tuple_binding.bindings)
                    .collect_vec()
                    .into_iter()
                    .rev()
                {
                    let () = builder::mv(ctx, span, name, out)?;
                    let () = binding(ctx, b, out)?;
                }
                Ok(())
            }
            ast::Binding::Tagged(tagged_binding) => {
                let tuple = tagged_to_tuple(tagged_binding.clone());
                binding(ctx, ast::Binding::Tuple(tuple), out)
            }
            ast::Binding::Identifier(_) => {
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
                    .zip_eq(tuple_binding.bindings.iter())
                    .collect_vec()
                    .into_iter()
                    .rev()
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
            ast::Binding::Tagged(tagged_binding) => {
                let tuple = tagged_to_tuple(tagged_binding.clone());
                matches(ctx, &ast::Binding::Tuple(tuple), out)
            }
            ast::Binding::Literal(l) => {
                literal(ctx, l.clone(), out);
                eq(span, out);
                Ok(())
            }
        }
    }

    pub fn tagged_to_tuple(tagged_binding: ast::TaggedBinding) -> ast::TupleBinding {
        let inner_binding = ast::TupleBinding {
            span: tagged_binding.span,
            bindings: tagged_binding.bindings.clone(),
        };
        ast::TupleBinding {
            span: tagged_binding.span,
            bindings: vec![
                ast::Binding::Literal(ast::Literal::Symbol(ast::Symbol::Identifier(
                    tagged_binding.tag.clone(),
                ))),
                ast::Binding::Tuple(inner_binding),
            ],
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
                locals1: true_out
                    .locals
                    .names()
                    .into_iter()
                    .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                    .collect(),
                locals2: false_out
                    .locals
                    .names()
                    .into_iter()
                    .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                    .collect(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::HanoiParser;
    use from_pest::FromPest;
    use insta::{assert_debug_snapshot, assert_snapshot};
    use pest::Parser;

    #[test]
    fn test_fn_decl_to_transformer() {
        // Test function: fn args new => args match { ... }
        let fn_decl_str = "fn args new => args match {
            (state, (#pass{}, #pass{})) => (state, (#pass{}, #pass{})),
            (#start{}, (#in{capacity}, #pass{})) => {
                (#await_malloc{*capacity}, (#pass{}, #malloc{capacity}))
            },
            (#await_malloc{capacity},(#pass{}, #out{array})) => {
                (#end{}, (#out{(0, capacity, array)}, #pass{}))
            },
        }";

        // Parse the function declaration
        let mut pairs = HanoiParser::parse(crate::ast::Rule::fn_decl, fn_decl_str)
            .expect("Failed to parse function declaration");

        let fn_decl =
            ast::FnDecl::from_pest(&mut pairs).expect("Failed to convert pest pairs to FnDecl");

        // Clone the binding for later use in assertions
        let binding_clone = fn_decl.binding.clone();

        // Create an AnonFn from the FnDecl
        let anon_fn = ast::AnonFn {
            span: fn_decl.span,
            binding: fn_decl.binding,
            body: Box::new(fn_decl.expression),
        };

        // Convert to Transformer
        let transformer = Transformer::from_anon_fn(anon_fn);

        // Flatten the transformer
        assert_snapshot!(transformer.flatten());
    }
}

impl<'t> Transformer<'t> {
    fn format_indented(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        for _ in 0..indent {
            write!(f, "  ")?;
        }
        match self {
            Transformer::Literal(literal) => match literal {
                ast::Literal::Int(int) => writeln!(f, "{}", int.value),
                ast::Literal::Char(char_lit) => writeln!(f, "'{}'", char_lit.value),
                ast::Literal::Bool(bool_lit) => writeln!(f, "{}", bool_lit.value),
                ast::Literal::Symbol(symbol) => match symbol {
                    ast::Symbol::Identifier(identifier) => {
                        writeln!(f, "@{}", identifier.0.as_str())
                    }
                    ast::Symbol::String(string_lit) => writeln!(f, "@\"{}\"", string_lit.value),
                },
            },
            Transformer::Move(identifier) => writeln!(f, "{}", identifier.0.as_str()),
            Transformer::MoveIdx { idx, .. } => writeln!(f, "mv({})", idx),
            Transformer::Copy(identifier) => writeln!(f, "*{}", identifier.0.as_str()),
            Transformer::CopyIdx { idx, .. } => writeln!(f, "cp({})", idx),
            Transformer::Drop(_) => writeln!(f, "^"),
            Transformer::Call(qualified_label) => {
                write!(f, "'")?;
                for (i, identifier) in qualified_label.path.iter().enumerate() {
                    if i > 0 {
                        write!(f, "::")?;
                    }
                    write!(f, "{}", identifier.0.as_str())?;
                }
                Ok(())
            }
            Transformer::Binding(identifier) => writeln!(f, "{}=>", identifier.0.as_str()),
            Transformer::Tuple { size, .. } => writeln!(f, "tuple({})", size),
            Transformer::Untuple { size, .. } => writeln!(f, "untuple({})", size),
            Transformer::Branch {
                true_case,
                false_case,
                ..
            } => {
                writeln!(f, "if {{")?;
                true_case.format_indented(f, indent + 1)?;
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                writeln!(f, "}} else {{")?;
                false_case.format_indented(f, indent + 1)?;
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                writeln!(f, "}}")
            }
            Transformer::Composition { children, .. } => {
                for (i, child) in children.iter().enumerate() {
                    child.format_indented(f, if i == 0 { 0 } else { indent })?;
                }
                Ok(())
            }
            Transformer::AssertEq(_) => writeln!(f, "assert_eq"),
            Transformer::Panic(_) => writeln!(f, "panic"),
            Transformer::Eq(_) => writeln!(f, "eq"),
        }
    }
}

impl<'t> std::fmt::Display for Transformer<'t> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.format_indented(f, 0)
    }
}
