use std::collections::BTreeMap;

use crate::ast::Spanner;
use crate::pen::{Pen, PenRef, PennedBy};
use builder::FileContext;
use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::flat::{self};
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

#[derive(Debug, From, Into, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TransformerRef(usize);

impl<'t> PenRef<Transformer<'t>> for TransformerRef {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Transformer<'t> {
    Literal(ast::Literal<'t>),
    Value {
        span: pest::Span<'t>,
        value: flat::Value,
    },
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
        true_case: TransformerRef,
        false_case: TransformerRef,
    },
    Composition {
        span: pest::Span<'t>,
        children: Vec<TransformerRef>,
    },
    AssertEq(pest::Span<'t>),
    Panic(pest::Span<'t>),
    Eq(pest::Span<'t>),
}

impl<'t> PennedBy for Transformer<'t> {
    type Ref = TransformerRef;
}

impl<'t> Transformer<'t> {}

struct TransformerFactory<'a, 't>(&'a mut Pen<Transformer<'t>>);

impl<'a, 't> TransformerFactory<'a, 't> {
    pub fn from_anon_fn(&mut self, anon_fn: ast::AnonFn<'t>) -> TransformerRef {
        Transformer::Composition {
            span: anon_fn.span,
            children: vec![
                self.from_binding(anon_fn.binding),
                self.from_expression(*anon_fn.body),
            ],
        }
        .into_pen(self.0)
    }

    pub fn from_root(&mut self, root: ast::RootExpression<'t>) -> TransformerRef {
        match root {
            ast::RootExpression::Literal(literal) => Transformer::Literal(literal).into_pen(self.0),
            ast::RootExpression::Identifier(identifier) => {
                Transformer::Move(identifier).into_pen(self.0)
            }
            ast::RootExpression::Copy(copy) => Transformer::Copy(copy.0).into_pen(self.0),
            ast::RootExpression::Tuple(tuple) => self.from_tuple(tuple),
            ast::RootExpression::Tagged(tagged) => self.from_tuple(ast::Tuple {
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
            ast::RootExpression::Block(block) => Transformer::Composition {
                span: block.span,
                children: vec![
                    Transformer::Composition {
                        span: block.span,
                        children: block
                            .statements
                            .into_iter()
                            .map(|s| self.from_statement(s))
                            .collect(),
                    }
                    .into_pen(self.0),
                    self.from_expression(*block.expression),
                ],
            }
            .into_pen(self.0),
        }
    }

    pub fn from_statement(&mut self, statement: ast::Statement<'t>) -> TransformerRef {
        match statement {
            ast::Statement::Let(let_statement) => Transformer::Composition {
                span: let_statement._span,
                children: vec![
                    self.from_expression(let_statement.rhs),
                    self.from_binding(let_statement.binding),
                ],
            }
            .into_pen(self.0),
        }
    }

    pub fn from_binding(&mut self, binding: ast::Binding<'t>) -> TransformerRef {
        fn from_tuple<'t>(
            p: &mut Pen<Transformer<'t>>,
            span: pest::Span<'t>,
            bindings: Vec<ast::Binding<'t>>,
        ) -> (Transformer<'t>, i32) {
            let mut children = vec![Transformer::Untuple {
                span,
                size: bindings.len(),
            }
            .into_pen(p)];
            let mut stack_size = bindings.len() as i32;
            for binding in bindings {
                children.push(
                    Transformer::MoveIdx {
                        span: binding.pest_span(),
                        idx: stack_size as usize - 1,
                    }
                    .into_pen(p),
                );
                let (transformer, pushed) = helper(p, binding);
                children.push(transformer.into_pen(p));
                stack_size += pushed;
            }
            (Transformer::Composition { span, children }, stack_size - 1)
        }

        fn helper<'t>(
            p: &mut Pen<Transformer<'t>>,
            binding: ast::Binding<'t>,
        ) -> (Transformer<'t>, i32) {
            match binding {
                ast::Binding::Identifier(identifier) => (Transformer::Binding(identifier), 0),
                ast::Binding::Drop(drop) => (Transformer::Drop(drop.span), -1),
                ast::Binding::Tuple(tuple) => from_tuple(p, tuple.span, tuple.bindings),
                ast::Binding::Literal(literal) => {
                    let span = literal.pest_span();
                    (
                        Transformer::Composition {
                            span,
                            children: vec![
                                Transformer::Literal(literal).into_pen(p),
                                Transformer::AssertEq(span).into_pen(p),
                            ],
                        },
                        -1,
                    )
                }
                ast::Binding::Tagged(tagged) => from_tuple(
                    p,
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
        let (transformer, _) = helper(self.0, binding);
        transformer.into_pen(self.0)
    }

    pub fn from_expression(&mut self, expression: ast::Expression<'t>) -> TransformerRef {
        Transformer::Composition {
            span: expression.span,
            children: vec![
                self.from_root(expression.root),
                Transformer::Composition {
                    span: expression.span,
                    children: expression
                        .transformers
                        .into_iter()
                        .map(|t| self.from_transformer(t))
                        .collect(),
                }
                .into_pen(self.0),
            ],
        }
        .into_pen(self.0)
    }

    pub fn from_transformer(&mut self, transformer: ast::Transformer<'t>) -> TransformerRef {
        match transformer {
            ast::Transformer::Call(call) => Transformer::Call(call).into_pen(self.0),
            ast::Transformer::InlineCall(anon_fn) => self.from_anon_fn(anon_fn),
            ast::Transformer::Match(match_expression) => {
                let mut else_case = Transformer::Panic(match_expression.span).into_pen(self.0);

                for case in match_expression.cases.into_iter().rev() {
                    else_case = Transformer::Composition {
                        span: case.span,
                        children: vec![
                            Transformer::CopyIdx {
                                span: case.span,
                                idx: 0,
                            }
                            .into_pen(self.0),
                            self.transformer_for_matching(&case.binding),
                            Transformer::Branch {
                                span: case.span,
                                true_case: Transformer::Composition {
                                    span: case.span,
                                    children: vec![
                                        self.from_binding(case.binding),
                                        self.from_expression(case.rhs),
                                    ],
                                }
                                .into_pen(self.0),
                                false_case: else_case,
                            }
                            .into_pen(self.0),
                        ],
                    }
                    .into_pen(self.0);
                }
                else_case
            }
            ast::Transformer::If(if_expression) => Transformer::Branch {
                span: if_expression.span,
                true_case: self.from_expression(*if_expression.true_case),
                false_case: self.from_expression(*if_expression.false_case),
            }
            .into_pen(self.0),
            ast::Transformer::Then(mut then) => {
                let span = then.span;
                if then.transformers.len() == 1 {
                    self.from_transformer(then.transformers.remove(0))
                } else {
                    let first = self.from_transformer(then.transformers.remove(0));
                    let rest = Transformer::Composition {
                        span,
                        children: vec![self.from_transformer(ast::Transformer::Then(then)), {
                            let end_case = Transformer::Composition {
                                span,
                                children: vec![
                                    // result
                                    self.make_tag(span, "end", 1),
                                ],
                            };
                            let cont_case = Transformer::Composition {
                                span,
                                children: vec![
                                    self.tag_unwrapper(span, "cont", 2),
                                    // rest_state args
                                    Transformer::Value {
                                        span,
                                        value: flat::Value::Bool(true),
                                    }
                                    .into_pen(self.0),
                                    // rest_state args true
                                    Transformer::MoveIdx { span, idx: 2 }.into_pen(self.0),
                                    // args true rest_state
                                    Transformer::Tuple { span, size: 2 }.into_pen(self.0),
                                    // args (true, rest_state)
                                    Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                                    self.make_tag(span, "cont", 2),
                                    // #cont{(true, rest_state), args}
                                ],
                            };
                            self.tag_tester(span, "end", 1, end_case, cont_case)
                        }],
                    }
                    .into_pen(self.0);

                    let first = Transformer::Composition {
                        span,
                        children: vec![first, {
                            let end_case = Transformer::Composition {
                                span,
                                children: vec![
                                    // result
                                    self.make_tag(span, "start", 1),
                                    rest,
                                ],
                            };
                            let cont_case = Transformer::Composition {
                                span,
                                children: vec![
                                    self.tag_unwrapper(span, "cont", 2),
                                    // first_state args
                                    Transformer::Value {
                                        span,
                                        value: flat::Value::Bool(false),
                                    }
                                    .into_pen(self.0),
                                    // first_state args false
                                    Transformer::MoveIdx { span, idx: 2 }.into_pen(self.0),
                                    // args false first_state
                                    Transformer::Tuple { span, size: 2 }.into_pen(self.0),
                                    // args (false, first_state)
                                    Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                                    // (false, first_state) args
                                    self.make_tag(span, "cont", 2),
                                    // #cont{(false, first_state), args}
                                ],
                            };
                            self.tag_tester(span, "end", 1, end_case, cont_case)
                        }],
                    }
                    .into_pen(self.0);

                    let start_case = Transformer::Composition {
                        span,
                        children: vec![
                            // start_arg
                            self.make_tag(span, "start", 1),
                            first,
                        ],
                    };
                    let cont_case = Transformer::Composition {
                        span,
                        children: vec![
                            self.tag_unwrapper(span, "cont", 2),
                            // (first/rest, inner_state) args
                            Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                            // args (first/rest, inner_state)
                            Transformer::Untuple { span, size: 2 }.into_pen(self.0),
                            // args first/rest inner_state
                            Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                            // args inner_state first/rest
                            Transformer::Branch {
                                span,
                                false_case: Transformer::Composition {
                                    span,
                                    children: vec![
                                        // args inner_state
                                        Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                                        // inner_state args
                                        self.make_tag(span, "cont", 2),
                                        first,
                                    ],
                                }
                                .into_pen(self.0),
                                true_case: Transformer::Composition {
                                    span,
                                    children: vec![
                                        // args inner_state
                                        Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                                        // inner_state args
                                        self.make_tag(span, "cont", 2),
                                        rest,
                                    ],
                                }
                                .into_pen(self.0),
                            }
                            .into_pen(self.0),
                        ],
                    };
                    self.tag_tester(span, "start", 1, start_case, cont_case)
                }
            }
            ast::Transformer::Do(do_fn) => Transformer::Composition {
                span: do_fn.span,
                children: vec![
                    self.tag_unwrapper(do_fn.span, "start", 1),
                    self.from_transformer(*do_fn.transformer),
                    self.make_tag(do_fn.span, "end", 1),
                ],
            }
            .into_pen(self.0),
        }
    }

    pub fn from_tuple(&mut self, tuple: ast::Tuple<'t>) -> TransformerRef {
        let size = tuple.values.len();
        let children = tuple
            .values
            .into_iter()
            .map(|e| self.from_expression(e))
            .collect::<Vec<_>>();
        Transformer::Composition {
            span: tuple.span,
            children: vec![
                Transformer::Composition {
                    span: tuple.span,
                    children,
                }
                .into_pen(self.0),
                Transformer::Tuple {
                    span: tuple.span,
                    size,
                }
                .into_pen(self.0),
            ],
        }
        .into_pen(self.0)
    }

    #[allow(unused)]
    pub fn flatten(&mut self, r: TransformerRef) -> Transformer<'t> {
        match r.get(self.0).clone() {
            Transformer::Composition { span, children } => {
                let mut flattened_children = Vec::new();
                for child in children {
                    let flattened_child = self.flatten(child);
                    match flattened_child {
                        Transformer::Composition {
                            children: nested_children,
                            ..
                        } => {
                            flattened_children.extend(nested_children);
                        }
                        _ => {
                            flattened_children.push(flattened_child.into_pen(self.0));
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
                true_case: self.flatten(true_case).into_pen(self.0),
                false_case: self.flatten(false_case).into_pen(self.0),
            },
            // For all other variants, return as-is since they don't contain nested Transformers
            other => other.clone(),
        }
    }

    pub fn transformer_for_matching(&mut self, binding: &ast::Binding<'t>) -> TransformerRef {
        let span = binding.pest_span();
        match binding {
            ast::Binding::Drop(_) | ast::Binding::Identifier(_) => Transformer::Composition {
                span,
                children: vec![
                    Transformer::Drop(span).into_pen(self.0),
                    Transformer::Literal(ast::Literal::Bool(ast::Bool { span, value: true }))
                        .into_pen(self.0),
                ],
            }
            .into_pen(self.0),
            ast::Binding::Tuple(tuple_binding) => {
                let size = tuple_binding.bindings.len();

                let mut true_case =
                    Transformer::Literal(ast::Literal::Bool(ast::Bool { span, value: true }))
                        .into_pen(self.0);
                for (i, binding) in tuple_binding.bindings.iter().enumerate().rev() {
                    let mut children = vec![];
                    let top = size - i - 1;
                    children.push(Transformer::MoveIdx { span, idx: top }.into_pen(self.0));
                    children.push(self.transformer_for_matching(binding));

                    let mut false_case_children = vec![];
                    for _ in 0..top {
                        false_case_children.push(Transformer::Drop(span).into_pen(self.0));
                    }
                    false_case_children.push(
                        Transformer::Literal(ast::Literal::Bool(ast::Bool { span, value: false }))
                            .into_pen(self.0),
                    );

                    children.push(
                        Transformer::Branch {
                            span,
                            true_case: true_case,
                            false_case: Transformer::Composition {
                                span: span,
                                children: false_case_children,
                            }
                            .into_pen(self.0),
                        }
                        .into_pen(self.0),
                    );

                    true_case = Transformer::Composition { span, children }.into_pen(self.0);
                }
                Transformer::Composition {
                    span,
                    children: vec![
                        Transformer::Untuple { span, size }.into_pen(self.0),
                        true_case,
                    ],
                }
                .into_pen(self.0)
            }
            ast::Binding::Tagged(tagged_binding) => self.transformer_for_matching(
                &ast::Binding::Tuple(builder::tagged_to_tuple(tagged_binding.clone())),
            ),
            ast::Binding::Literal(l) => Transformer::Composition {
                span,
                children: vec![
                    Transformer::Literal(l.clone()).into_pen(self.0),
                    Transformer::Eq(span).into_pen(self.0),
                ],
            }
            .into_pen(self.0),
        }
    }

    fn tag_tester(
        &mut self,
        span: pest::Span<'t>,
        tag: &str,
        size: usize,
        true_case: Transformer<'t>,
        false_case: Transformer<'t>,
    ) -> TransformerRef {
        Transformer::Composition {
            span,
            children: vec![
                // (tag, args)
                Transformer::Untuple { span, size: 2 }.into_pen(self.0),
                // tag args
                Transformer::CopyIdx { span, idx: 1 }.into_pen(self.0),
                // tag args tag
                Transformer::Value {
                    span,
                    value: flat::Value::Symbol(tag.to_owned()),
                }
                .into_pen(self.0),
                Transformer::Eq(span).into_pen(self.0),
                // tag args bool
                Transformer::Branch {
                    span,
                    true_case: Transformer::Composition {
                        span,
                        children: vec![
                            Transformer::Tuple { span, size: 2 }.into_pen(self.0),
                            self.tag_unwrapper(span, tag, size),
                            true_case.into_pen(self.0),
                        ],
                    }
                    .into_pen(self.0),
                    false_case: Transformer::Composition {
                        span,
                        children: vec![
                            Transformer::Tuple { span, size: 2 }.into_pen(self.0),
                            false_case.into_pen(self.0),
                        ],
                    }
                    .into_pen(self.0),
                }
                .into_pen(self.0),
            ],
        }
        .into_pen(self.0)
    }

    fn make_tag(&mut self, span: pest::Span<'t>, tag: &str, size: usize) -> TransformerRef {
        Transformer::Composition {
            span,
            children: vec![
                Transformer::Tuple { span, size }.into_pen(self.0),
                // args
                Transformer::Value {
                    span,
                    value: flat::Value::Symbol(tag.to_owned()),
                }
                .into_pen(self.0),
                // args tag
                Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                // tag args
                Transformer::Tuple { span, size: 2 }.into_pen(self.0),
            ],
        }
        .into_pen(self.0)
    }

    fn tag_unwrapper(&mut self, span: pest::Span<'t>, tag: &str, size: usize) -> TransformerRef {
        Transformer::Composition {
            span,
            children: vec![
                Transformer::Untuple { span, size: 2 }.into_pen(self.0),
                Transformer::MoveIdx { span, idx: 1 }.into_pen(self.0),
                Transformer::Value {
                    span,
                    value: flat::Value::Symbol(tag.to_owned()),
                }
                .into_pen(self.0),
                Transformer::AssertEq(span).into_pen(self.0),
                Transformer::Untuple { span, size: size }.into_pen(self.0),
            ],
        }
        .into_pen(self.0)
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

        let mut pen = Pen::new();
        let mut factory = TransformerFactory(&mut pen);

        let transformer = factory.from_anon_fn(anon);

        let mut word_pen = Pen::new();
        let mut word_factory = WordFactory(&mut word_pen);

        let mut locals = Locals::default();
        locals.push_unnamed();
        let mut already_visited = BTreeMap::new();
        let sentence = word_factory.into_recursive_word(
            &mut already_visited,
            &mut pen,
            ctx,
            &symbol_table,
            &mut locals,
            transformer,
        )?;
        let root_span = sentence.get(&word_pen).span;

        let mut names = NameSequence {
            base: name,
            count: 0,
        };
        let reserved_first = names.next();
        let mut already_visited = BTreeMap::new();
        for (word_ref, word) in word_pen.into_iter() {
            self.visit_recursive_word(&mut names, &mut already_visited, word_ref, word);
        }
        self.res.sentences.push(Sentence {
            span: root_span,
            name: reserved_first,
            words: vec![Word {
                span: root_span,
                inner: InnerWord::Call(
                    already_visited
                        .get(&sentence)
                        .expect(format!("should already be visited: {sentence:?}").as_str())
                        .clone(),
                ),
                names: vec![],
            }],
        });
        Ok(())
    }

    fn visit_def(
        &mut self,
        _span: pest::Span<'t>,
        file_idx: FileIndex,
        symbol_table: &SymbolTable,
        name: QualifiedName,
        into_fn: ast::Transformer<'t>,
    ) -> Result<(), linker::Error> {
        let ctx = FileContext {
            file_idx,
            sources: self.sources,
        };
        let mut pen = Pen::new();
        let mut factory = TransformerFactory(&mut pen);

        let transformer = factory.from_transformer(into_fn);

        let mut word_pen = Pen::new();
        let mut word_factory = WordFactory(&mut word_pen);

        let mut locals = Locals::default();
        locals.push_unnamed();
        let mut already_visited = BTreeMap::new();
        let sentence = word_factory.into_recursive_word(
            &mut already_visited,
            &mut pen,
            ctx,
            &symbol_table,
            &mut locals,
            transformer,
        )?;
        let root_span = sentence.get(&word_pen).span;
        if !locals.terminal && locals.len() != 1 {
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
        let reserved_first = names.next();
        let mut already_visited = BTreeMap::new();
        for (word_ref, word) in word_pen.into_iter() {
            self.visit_recursive_word(&mut names, &mut already_visited, word_ref, word);
        }
        self.res.sentences.push(Sentence {
            span: root_span,
            name: reserved_first,
            words: vec![Word {
                span: root_span,
                inner: InnerWord::Call(
                    already_visited
                        .get(&sentence)
                        .expect(format!("should already be visited: {sentence:?}").as_str())
                        .clone(),
                ),
                names: vec![],
            }],
        });
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

    fn visit_recursive_word(
        &mut self,
        names: &mut NameSequence,
        already_visited: &mut BTreeMap<WordRef, QualifiedName>,
        word_ref: WordRef,
        word: RecursiveWord,
    ) {
        let span = word.span;
        let words = match word.inner {
            InnerWord::Push(value) => vec![Word {
                span,
                inner: InnerWord::Push(value),
                names: word.names.clone(),
            }],
            InnerWord::Builtin(builtin) => vec![Word {
                span,
                inner: InnerWord::Builtin(builtin),
                names: word.names.clone(),
            }],
            InnerWord::Copy(idx) => vec![Word {
                span,
                inner: InnerWord::Copy(idx),
                names: word.names.clone(),
            }],
            InnerWord::Drop(idx) => vec![Word {
                span,
                inner: InnerWord::Drop(idx),
                names: word.names.clone(),
            }],
            InnerWord::Move(idx) => vec![Word {
                span,
                inner: InnerWord::Move(idx),
                names: word.names.clone(),
            }],
            InnerWord::Tuple(idx) => vec![Word {
                span,
                inner: InnerWord::Tuple(idx),
                names: word.names.clone(),
            }],
            InnerWord::Untuple(idx) => vec![Word {
                span,
                inner: InnerWord::Untuple(idx),
                names: word.names.clone(),
            }],
            InnerWord::Call(qualified_name) => vec![Word {
                span,
                inner: InnerWord::Call(qualified_name),
                names: word.names.clone(),
            }],
            InnerWord::Composition(children) => children
                .into_iter()
                .map(|child| {
                    let name = already_visited
                        .get(&child)
                        .expect(format!("should already be visited: {child:?}").as_str())
                        .clone();
                    Word {
                        span,
                        inner: InnerWord::Call(name),
                        names: word.names.clone(),
                    }
                })
                .collect(),
            InnerWord::Branch(true_case, false_case) => {
                let true_name = already_visited
                    .get(&true_case)
                    .expect(format!("should already be visited: {true_case:?}").as_str())
                    .clone();
                let false_name = already_visited
                    .get(&false_case)
                    .expect(format!("should already be visited: {false_case:?}").as_str())
                    .clone();
                vec![Word {
                    span,
                    inner: InnerWord::Branch(true_name, false_name),
                    names: word.names.clone(),
                }]
            }
            InnerWord::JumpTable(jump_table) => vec![Word {
                span,
                inner: InnerWord::JumpTable(
                    jump_table
                        .into_iter()
                        .map(|sentence| {
                            let name = already_visited
                                .get(&sentence)
                                .expect(format!("should already be visited: {sentence:?}").as_str())
                                .clone();
                            name
                        })
                        .collect(),
                ),
                names: word.names.clone(),
            }],
        };

        let res = names.next();
        self.res.sentences.push(Sentence {
            span,
            name: res.clone(),
            words,
        });

        already_visited.insert(word_ref, res);
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

    #[allow(unused)]
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

struct WordFactory<'a>(&'a mut Pen<RecursiveWord>);

impl<'a> WordFactory<'a> {
    fn single_span(
        &mut self,
        span: FileSpan,
        words: impl IntoIterator<Item = InnerWord<WordRef>>,
    ) -> WordRef {
        RecursiveWord {
            span,
            inner: InnerWord::Composition(
                words
                    .into_iter()
                    .map(|inner| {
                        RecursiveWord {
                            span,
                            inner,
                            names: vec![],
                        }
                        .into_pen(self.0)
                    })
                    .collect(),
            ),
            names: vec![],
        }
        .into_pen(self.0)
    }

    fn into_recursive_word<'t>(
        &mut self,
        already_visited: &mut BTreeMap<TransformerRef, (Locals, WordRef, Locals)>,
        p: &mut Pen<Transformer<'t>>,
        ctx: FileContext,
        symbol_table: &SymbolTable,
        locals: &mut Locals,
        root_ref: TransformerRef,
    ) -> Result<WordRef, Error> {
        if let Some((prev_locals, prev_word, new_locals)) = already_visited.get(&root_ref) {
            if !locals.compare(ctx.sources, new_locals) {
                let span = prev_word.get(self.0).span;
                return Err(Error::BranchContractsDisagree {
                    location: span.location(ctx.sources),
                    locals1: prev_locals
                        .names()
                        .into_iter()
                        .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                        .collect(),
                    locals2: locals
                        .names()
                        .into_iter()
                        .map(|n| format!("{:?}", n.as_ref(ctx.sources)))
                        .collect(),
                });
            }
            *locals = new_locals.clone();
            return Ok(*prev_word);
        }

        let mut old_locals = locals.clone();
        let root = root_ref.take(p);
        let res = self
            .into_recursive_word_helper(
                already_visited,
                p,
                ctx,
                symbol_table,
                locals,
                root_ref,
                root,
            )?
            .into_pen(self.0);
        already_visited.insert(root_ref, (old_locals, res, locals.clone()));
        Ok(res)
    }

    fn into_recursive_word_helper<'t>(
        &mut self,
        already_visited: &mut BTreeMap<TransformerRef, (Locals, WordRef, Locals)>,
        p: &mut Pen<Transformer<'t>>,
        ctx: FileContext,
        symbol_table: &SymbolTable,
        locals: &mut Locals,
        root_ref: TransformerRef,
        root: Transformer<'t>,
    ) -> Result<RecursiveWord, Error> {
        match root {
            Transformer::Literal(literal) => {
                let span = literal.span(ctx.file_idx);
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Push(literal.into_value()),
                    names: locals.names(),
                })
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
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Move(idx),
                    names: locals.names(),
                })
            }
            Transformer::MoveIdx { span, idx } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.remove(idx);
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Move(idx),
                    names: locals.names(),
                })
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
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Copy(idx),
                    names: locals.names(),
                })
            }
            Transformer::CopyIdx { span, idx } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Copy(idx),
                    names: locals.names(),
                })
            }
            Transformer::Drop(span) => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Drop(0),
                    names: locals.names(),
                })
            }
            Transformer::Call(qualified_label) => {
                let span = qualified_label.span(ctx.file_idx);

                let qualified = symbol_table.resolve(
                    ctx.sources,
                    qualified_label.into_ir(ctx.sources, ctx.file_idx),
                );
                locals.pop();
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Call(qualified),
                    names: locals.names(),
                })
            }
            Transformer::Binding(identifier) => {
                let span = identifier.span(ctx.file_idx);
                locals.pop();
                locals.push_named(identifier.span(ctx.file_idx));
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Composition(vec![]),
                    names: locals.names(),
                })
            }
            Transformer::Tuple { span, size } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                for _ in 0..size {
                    locals.pop();
                }
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Tuple(size),
                    names: locals.names(),
                })
            }
            Transformer::Untuple { span, size } => {
                let span = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                for _ in 0..size {
                    locals.push_unnamed();
                }
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Untuple(size),
                    names: locals.names(),
                })
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
                let true_sentence = self.into_recursive_word(
                    already_visited,
                    p,
                    ctx,
                    symbol_table,
                    &mut true_locals,
                    true_case,
                )?;
                let false_sentence = self.into_recursive_word(
                    already_visited,
                    p,
                    ctx,
                    symbol_table,
                    &mut false_locals,
                    false_case,
                )?;

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

                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Branch(true_sentence, false_sentence),
                    names: locals.names(),
                })
            }
            Transformer::Composition { span, children } => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                let words: Result<Vec<WordRef>, Error> = children
                    .into_iter()
                    .map(|child| {
                        self.into_recursive_word(
                            already_visited,
                            p,
                            ctx,
                            symbol_table,
                            locals,
                            child,
                        )
                    })
                    .collect();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Composition(words?),
                    names: locals.names(),
                })
            }
            Transformer::AssertEq(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                locals.pop();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Builtin(flat::Builtin::AssertEq),
                    names: locals.names(),
                })
            }
            Transformer::Panic(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.terminal = true;
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Builtin(flat::Builtin::Panic),
                    names: vec![],
                })
            }
            Transformer::Eq(span) => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.pop();
                locals.pop();
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Builtin(flat::Builtin::Eq),
                    names: locals.names(),
                })
            }
            Transformer::Value { span, value } => {
                let span: FileSpan = span.into_ir(ctx.sources, ctx.file_idx);
                locals.push_unnamed();
                Ok(RecursiveWord {
                    span,
                    inner: InnerWord::Push(value),
                    names: locals.names(),
                })
            }
        }
    }
}

#[derive(Debug, From, Into, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WordRef(usize);

impl PenRef<RecursiveWord> for WordRef {}

impl PennedBy for RecursiveWord {
    type Ref = WordRef;
}

#[derive(Debug, Clone)]
pub struct RecursiveWord {
    pub span: FileSpan,
    pub inner: InnerWord<WordRef>,
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
    Composition(Vec<BranchRepr>),
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::HanoiParser;
    use from_pest::FromPest;
    use insta::assert_snapshot;
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

        // Create an AnonFn from the FnDecl
        let anon_fn = ast::AnonFn {
            span: fn_decl.span,
            binding: fn_decl.binding,
            body: Box::new(fn_decl.expression),
        };

        let mut pen = Pen::new();
        let mut factory = TransformerFactory(&mut pen);

        // Convert to Transformer
        let transformer = factory.from_anon_fn(anon_fn);

        let flattened = factory.flatten(transformer).into_pen(&mut pen);
        // Flatten the transformer
        assert_snapshot!(BoundTransformerRef(&mut pen, flattened));
    }
}

impl TransformerRef {
    fn format_indented<'t>(
        &self,
        pen: &Pen<Transformer<'t>>,
        f: &mut std::fmt::Formatter<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        for _ in 0..indent {
            write!(f, "  ")?;
        }
        match self.get(pen) {
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
                true_case.format_indented(pen, f, indent + 1)?;
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                writeln!(f, "}} else {{")?;
                false_case.format_indented(pen, f, indent + 1)?;
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                writeln!(f, "}}")
            }
            Transformer::Composition { children, .. } => {
                for (i, child) in children.iter().enumerate() {
                    child.format_indented(pen, f, if i == 0 { 0 } else { indent })?;
                }
                Ok(())
            }
            Transformer::AssertEq(_) => writeln!(f, "assert_eq"),
            Transformer::Panic(_) => writeln!(f, "panic"),
            Transformer::Eq(_) => writeln!(f, "eq"),
            Transformer::Value { value, .. } => writeln!(f, "{:?}", value),
        }
    }
}

pub struct BoundTransformerRef<'a, 't>(&'a Pen<Transformer<'t>>, TransformerRef);

impl<'a, 't> std::fmt::Display for BoundTransformerRef<'a, 't> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.format_indented(self.0, f, 0)
    }
}
