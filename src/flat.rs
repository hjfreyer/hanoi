use std::{collections::VecDeque, usize};

use derive_more::derive::{From, Into};
use itertools::Itertools;
use pest::{iterators::Pair, Span};
use typed_index_collections::TiVec;

use crate::ast::{
    self, ident_from_pair, Bindings, Identifier, Literal, Path, PathOrIdent, ProcMatchBlock,
    ProcMatchCase, Rule, ValueExpression,
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq)]
pub struct SentenceIndex(usize);

impl SentenceIndex {
    pub const TRAP: Self = SentenceIndex(usize::MAX);
}

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq)]
pub struct NamespaceIndex(usize);

#[derive(Debug, Clone, Default)]
pub struct Library<'t> {
    pub namespaces: TiVec<NamespaceIndex, Namespace>,
    pub sentences: TiVec<SentenceIndex, Sentence<'t>>,
}

#[derive(Debug, Clone, Default)]
pub struct Namespace(pub Vec<(String, Entry)>);

impl Namespace {
    pub fn get(&self, name: &str) -> Option<&Entry> {
        self.0
            .iter()
            .find_map(|(k, v)| if k == name { Some(v) } else { None })
    }
}

#[derive(Debug, Clone)]
pub enum Entry {
    Value(Value),
    Namespace(NamespaceIndex),
}

impl<'t> Library<'t> {
    pub fn from_ast(lib: ast::Namespace<'t>) -> Result<Self, BuilderError<'t>> {
        let mut res = Self::default();
        res.visit_ns(lib, None)?;
        Ok(res)
    }

    pub fn root_namespace(&self) -> &Namespace {
        self.namespaces.first().unwrap()
    }

    fn visit_ns(
        &mut self,
        ns: ast::Namespace<'t>,
        parent: Option<NamespaceIndex>,
    ) -> Result<NamespaceIndex, BuilderError<'t>> {
        let ns_idx = self.namespaces.push_and_get_key(Namespace::default());

        if let Some(parent) = parent {
            self.namespaces[ns_idx]
                .0
                .push(("super".to_owned(), Entry::Namespace(parent)));
        }

        for decl in ns.decls {
            match decl.value {
                ast::DeclValue::Namespace(namespace) => {
                    let subns = self.visit_ns(namespace, Some(ns_idx))?;
                    self.namespaces[ns_idx]
                        .0
                        .push((decl.name, Entry::Namespace(subns)));
                }
                // ast::DeclValue::Code(code) => {
                //     let sentence_idx = self.visit_code(&decl.name, ns_idx, VecDeque::new(), code);
                //     self.namespaces[ns_idx].0.push((
                //         decl.name,
                //         Entry::Value(Value::Pointer(Closure(vec![], sentence_idx))),
                //     ));
                // }
                ast::DeclValue::Proc(p) => {
                    let sentence_idx = self.visit_block(&decl.name, ns_idx, VecDeque::new(), p)?;
                    self.namespaces[ns_idx].0.push((
                        decl.name,
                        Entry::Value(Value::Pointer(Closure(vec![], sentence_idx))),
                    ));
                }
            }
        }
        Ok(ns_idx)
    }

    fn visit_block(
        &mut self,
        name: &str,
        ns_idx: NamespaceIndex,
        mut names: VecDeque<Option<String>>,
        block: ast::Block<'t>,
    ) -> Result<SentenceIndex, BuilderError<'t>> {
        match block {
            ast::Block::Bind {
                name: bind_name,
                inner,
            } => {
                names.push_back(Some(bind_name.as_str().to_owned()));
                self.visit_block(name, ns_idx, names, *inner)
            }
            ast::Block::Call { span, call, next } => {
                let mut builder = SentenceBuilder::new(Some(name.to_owned()), ns_idx, names);
                let argc = builder.func_call(call)?;

                let mut leftover_names: VecDeque<Option<String>> =
                    builder.names.iter().skip(argc + 1).cloned().collect();

                let next = self.visit_block(name, ns_idx, leftover_names, *next)?;

                builder.sentence_idx(span, next);
                // Stack: (leftovers) (args) to_call next

                while builder.names.len() > argc + 2 {
                    builder.mv_idx(span, argc + 2);
                    builder.mv_idx(span, 1);
                    builder.builtin(span, Builtin::Curry);
                }
                // Stack: (args) to_call next
                builder.mv_idx(span, 1);
                builder.symbol(span, "exec");

                Ok(self.sentences.push_and_get_key(builder.build()))
            }
            ast::Block::Raw { span, words } => {
                let sentence = Sentence {
                    name: Some(name.to_owned()),
                    words: words
                        .into_iter()
                        .map(|w| self.convert_raw_word(ns_idx, w))
                        .collect_vec(),
                };
                Ok(self.sentences.push_and_get_key(sentence))
            }
            ast::Block::AssertEq { literal, inner } => {
                let next = self.visit_block(name, ns_idx, names.clone(), *inner)?;
                let assert_idx = names.len();
                names.push_back(None);

                let mut builder = SentenceBuilder::new(Some(name.to_owned()), ns_idx, names);
                builder.mv_idx(literal.span, assert_idx);
                builder.literal(literal.span, literal.value);
                builder.builtin(literal.span, Builtin::AssertEq);
                builder.sentence_idx(literal.span, next);
                builder.symbol(literal.span, "exec");
                Ok(self.sentences.push_and_get_key(builder.build()))
            }
            ast::Block::Match { span, cases, els } => {
                todo!()
                //            let els = if let Some(els) = els {
                //             let mut panic_builder =   SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());
                //             panic_builder.symbol(span, "panic");
                //             self.sentences.push_and_get_key(panic_builder.build())
                //             } else {
                //                 todo!()
                //             };

                //     let mut next_case = els;

                //     let if_case_matches_names: VecDeque<Option<String>> = bindings
                //     .bindings
                //     .iter()
                //     .map(|b| match b {
                //         ast::Binding::Literal(literal) => None,
                //         ast::Binding::Ident(i) => Some(i.as_str().to_owned()),
                //     })
                //     .collect();
                //     for case in cases.into_iter().rev() {

                // //         let if_case_matches_idx =
                // //             {
                // //                 let this = &mut *self;
                // //                 let mut names = if_case_matches_names;
                // //                 let (statements, endpoint) = body.into_inner().collect_tuple().unwrap();

                // //                 assert_eq!(statements.as_rule(), Rule::statements);
                // //                 let statements = statements.into_inner().collect();
                // //                 this.visit_block(name, ns_idx, names, statements, endpoint)
                // //             }?;

                // //         let mut case_builder =
                // //             SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());

                // //         case_builder.literal(case_span, true.into());

                // //         for (idx, b) in bindings.bindings.into_iter().enumerate() {
                // //             match b {
                // //                 ast::Binding::Literal(literal) => {
                // //                     case_builder.cp_idx(case_span, idx + 1); // +1 for the "true"
                // //                     case_builder.literal(literal.span, literal.value);
                // //                     case_builder.builtin(case_span, Builtin::Eq);
                // //                     case_builder.builtin(case_span, Builtin::And);
                // //                 }
                // //                 ast::Binding::Ident(span) => continue,
                // //             }
                // //         }
                // //         case_builder.literal(
                // //             case_span,
                // //             Value::Pointer(Closure(vec![], if_case_matches_idx)),
                // //         );
                // //         case_builder.literal(case_span, Value::Pointer(Closure(vec![], next_case)));
                // //         case_builder.symbol(case_span, "if");
                // //         next_case = self.sentences.push_and_get_key(case_builder.build());
                // //     }

                // //     Ok(next_case)
                //   }
            }
            ast::Block::Unreachable { span } => {
                let mut panic_builder =
                    SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());
                panic_builder.symbol(span, "panic");
                Ok(self.sentences.push_and_get_key(panic_builder.build()))
            }
        }
        // let mut names: VecDeque<Option<String>> = bindings
        //     .bindings
        //     .into_iter()
        //     .map(|p| match p {
        //         ast::Binding::Ident(i) => Some(i.as_str().to_owned()),
        //         ast::Binding::Literal(_) => todo!(),
        //     })
        //     // .chain(["caller".to_owned()])
        //     .collect();
        // self.visit_block_pair(name, ns_idx, names, body)
    }

    // fn visit_endpoint(
    //     &mut self,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     names: VecDeque<Option<String>>,
    //     endpoint: Pair<'t, Rule>,
    // ) -> Result<SentenceIndex, BuilderError<'t>> {
    //     assert_eq!(endpoint.as_rule(), Rule::endpoint);
    //     let endpoint = endpoint.into_inner().exactly_one().unwrap();

    //     match endpoint.as_rule() {
    //         Rule::func_call => {
    //             let span = endpoint.as_span();

    //             let mut builder =
    //                 SentenceBuilder::new(Some(name.to_owned()), ns_idx, names.clone());

    //             let argc = builder.func_call(endpoint)?;

    //             while builder.names.len() > argc + 1 {
    //                 builder.drop_idx(span, argc + 1);
    //             }
    //             builder.literal(span, Value::Symbol("exec".to_owned()));

    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         Rule::if_endpoint => {
    //             let span = endpoint.as_span();
    //             let (cond, true_case, false_case) = endpoint.into_inner().collect_tuple().unwrap();

    //             let cond = ident_from_pair(cond);

    //             let mut builder =
    //                 SentenceBuilder::new(Some(name.to_owned()), ns_idx, names.clone());
    //             builder.mv(cond, cond.as_str());

    //             let mut case_names = builder.names.clone();
    //             case_names.pop_front();

    //             let true_case =
    //                 {
    //                     let this = &mut *self;
    //                     let mut names = case_names.clone();
    //                     let (statements, endpoint) = true_case.into_inner().collect_tuple().unwrap();

    //                     assert_eq!(statements.as_rule(), Rule::statements);
    //                     let statements = statements.into_inner().collect();
    //                     this.visit_block(name, ns_idx, names, statements, endpoint)
    //                 }?;
    //             let false_case =
    //                 {
    //                     let this = &mut *self;
    //                     let mut names = case_names;
    //                     let (statements, endpoint) = false_case.into_inner().collect_tuple().unwrap();

    //                     assert_eq!(statements.as_rule(), Rule::statements);
    //                     let statements = statements.into_inner().collect();
    //                     this.visit_block(name, ns_idx, names, statements, endpoint)
    //                 }?;

    //             builder.literal(span, Value::Pointer(Closure(vec![], true_case)));
    //             builder.literal(span, Value::Pointer(Closure(vec![], false_case)));
    //             builder.literal(span, Value::Symbol("if".to_owned()));

    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         Rule::match_block => {
    //             self.visit_match_block(name, ns_idx, names, endpoint.into())
    //         }
    //         Rule::unreachable => {
    //             let mut panic_builder =
    //                 SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());
    //             panic_builder.symbol(endpoint.as_span(), "panic");
    //             Ok(self.sentences.push_and_get_key(panic_builder.build()))
    //         }
    //         _ => unreachable!("Unexpected rule: {:?}", endpoint),
    //     }
    // }

    // fn visit_match_block(
    //     &mut self,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     names: VecDeque<Option<String>>,
    //     block: ast::ProcMatchBlock<'t>,
    // ) -> Result<SentenceIndex, BuilderError<'t>> {
    //     let mut builder = SentenceBuilder::new(Some(name.to_owned()), ns_idx, names.clone());

    //     let argc = builder.expr(block.expr)?;
    //     // Stack: (leftover names) (args) to_call

    //     let mut leftover_names: VecDeque<Option<String>> =
    //         builder.names.iter().skip(argc + 1).cloned().collect();

    //     let mut panic_builder =
    //         SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());
    //     panic_builder.symbol(block.span, "panic");
    //     let panic_idx = self.sentences.push_and_get_key(panic_builder.build());

    //     let mut next_case = panic_idx;
    //     for case in block.cases.into_iter().rev() {
    //         let if_case_matches_names :VecDeque<Option<String>> =
    //             // Preserved names from before the call.
    //             leftover_names.iter().cloned()
    //             // Then the bindings.
    //             .chain(
    //                 case.bindings.bindings
    //                 .iter()
    //                 .map(|b| match b{
    //                     ast::Binding::Literal(literal) => None,
    //                     ast::Binding::Ident(span) => Some(span.as_str().to_owned()),
    //                 })
    //             ).collect();

    //         let if_case_matches_idx =
    //             {
    //                 let this = &mut *self;
    //                 let mut names = if_case_matches_names;
    //                 let body = case.body;
    //                 let (statements, endpoint) = body.into_inner().collect_tuple().unwrap();

    //                 assert_eq!(statements.as_rule(), Rule::statements);
    //                 let statements = statements.into_inner().collect();
    //                 this.visit_block(name, ns_idx, names, statements, endpoint)
    //             }?;

    //         let mut case_builder =
    //             SentenceBuilder::new(Some(name.to_owned()), ns_idx, VecDeque::new());

    //         case_builder.literal(case.span, true.into());

    //         for (idx, b) in case.bindings.bindings.into_iter().enumerate() {
    //             match b {
    //                 ast::Binding::Literal(literal) => {
    //                     case_builder.cp_idx(case.span, leftover_names.len() + idx + 1); // +1 for "true"
    //                     case_builder.literal(literal.span, literal.value);
    //                     case_builder.builtin(case.span, Builtin::Eq);
    //                     case_builder.builtin(case.span, Builtin::And);
    //                 }
    //                 ast::Binding::Ident(span) => continue,
    //             }
    //         }
    //         case_builder.literal(
    //             case.span,
    //             Value::Pointer(Closure(vec![], if_case_matches_idx)),
    //         );
    //         case_builder.literal(case.span, Value::Pointer(Closure(vec![], next_case)));
    //         case_builder.symbol(case.span, "if");
    //         next_case = self.sentences.push_and_get_key(case_builder.build());
    //     }

    //     builder.literal(block.span, Value::Pointer(Closure(vec![], next_case)));
    //     // Stack: (leftovers) (args) to_call match_beginning

    //     while builder.names.len() > argc + 2 {
    //         builder.mv_idx(block.span, argc + 2);
    //         builder.mv_idx(block.span, 1);
    //         builder.builtin(block.span, Builtin::Curry);
    //     }
    //     // Stack: (args) to_call match_beginning
    //     builder.mv_idx(block.span, 1);
    //     builder.symbol(block.span, "exec");

    //     Ok(self.sentences.push_and_get_key(builder.build()))
    // }

    // fn visit_code(
    //     &mut self,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     names: VecDeque<Option<String>>,
    //     code: ast::Code<'t>,
    // ) -> SentenceIndex {
    //     match code {
    //         ast::Code::Sentence(sentence) => self.visit_sentence(name, ns_idx, names, sentence),
    //         ast::Code::AndThen(sentence, code) => {
    //             let init = self.convert_sentence(name, ns_idx, names, sentence);
    //             let and_then = self.visit_code(name, ns_idx, VecDeque::new(), *code);

    //             self.sentences.push_and_get_key(Sentence {
    //                 name: init.name,
    //                 words: std::iter::once(
    //                     InnerWord::Push(Value::Pointer(Closure(vec![], and_then))).into(),
    //                 )
    //                 .chain(init.words.into_iter())
    //                 .collect(),
    //             })
    //         }
    //         ast::Code::If {
    //             cond,
    //             true_case,
    //             false_case,
    //         } => {
    //             let cond = self.convert_sentence(name, ns_idx, names, cond);
    //             let true_case = self.visit_code(name, ns_idx, VecDeque::new(), *true_case);
    //             let false_case = self.visit_code(name, ns_idx, VecDeque::new(), *false_case);

    //             self.sentences.push_and_get_key(Sentence {
    //                 name: cond.name,
    //                 words: cond
    //                     .words
    //                     .into_iter()
    //                     .chain([
    //                         Value::Pointer(Closure(vec![], true_case)).into(),
    //                         Value::Pointer(Closure(vec![], false_case)).into(),
    //                         Value::Symbol("if".to_owned()).into(),
    //                     ])
    //                     .collect(),
    //             })
    //         }
    //         ast::Code::Bind {
    //             name: var_name,
    //             inner,
    //             span,
    //         } => self.visit_code(
    //             name,
    //             ns_idx,
    //             [Some(var_name.as_str().to_owned())]
    //                 .into_iter()
    //                 .chain(names)
    //                 .collect(),
    //             *inner,
    //         ),
    //         ast::Code::Match {
    //             idx,
    //             cases,
    //             els,
    //             span: _,
    //         } => {
    //             let mut next_case = self.visit_code(name, ns_idx, names.clone(), *els);

    //             for case in cases.into_iter().rev() {
    //                 let body = self.visit_code(name, ns_idx, names.clone(), case.body);
    //                 let cond = Sentence {
    //                     name: Some(name.to_owned()),
    //                     words: vec![
    //                         InnerWord::Copy(idx).into(),
    //                         case.value.into(),
    //                         InnerWord::Builtin(Builtin::Eq).into(),
    //                         Value::Pointer(Closure(vec![], body)).into(),
    //                         Value::Pointer(Closure(vec![], next_case)).into(),
    //                         Value::Symbol("if".to_owned()).into(),
    //                     ],
    //                 };

    //                 next_case = self.sentences.push_and_get_key(cond);
    //             }
    //             next_case
    //         }
    //     }
    // }

    fn convert_raw_word(&self, ns_idx: NamespaceIndex, raw_word: ast::RawWord<'t>) -> Word<'t> {
        Word {
            span: Some(raw_word.span),
            inner: match raw_word.inner {
                ast::RawWordInner::Literal(v) => InnerWord::Push(v.value),

                ast::RawWordInner::FunctionLike(f, idx) => match f.0.as_str() {
                    "cp" => InnerWord::Copy(idx),
                    "drop" => InnerWord::Drop(idx),
                    "mv" => InnerWord::Move(idx),
                    "sd" => InnerWord::Send(idx),
                    "ref" => InnerWord::Ref(idx),
                    _ => panic!("unknown reference: {:?}", f),
                },
                ast::RawWordInner::Builtin(name) => {
                    if let Some(builtin) = Builtin::ALL
                        .iter()
                        .find(|builtin| builtin.name() == name.as_str())
                    {
                        InnerWord::Builtin(*builtin)
                    } else {
                        panic!("unknown builtin: {:?}", name)
                    }
                }
                ast::RawWordInner::This => InnerWord::Push(Value::Namespace(ns_idx)),
            },
            names: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Sentence<'t> {
    pub name: Option<String>,
    pub words: Vec<Word<'t>>,
}

macro_rules! builtins {
    {
        $(($ident:ident, $name:ident),)*
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Builtin {
            $($ident,)*
        }

        impl Builtin {
            pub const ALL: &[Builtin] = &[
                $(Builtin::$ident,)*
            ];

            pub fn name(self) -> &'static str {
                match self {
                    $(Builtin::$ident => stringify!($name),)*
                }
            }
        }
    };
}

pub struct SentenceBuilder<'t> {
    pub name: Option<String>,
    pub ns_idx: NamespaceIndex,
    pub names: VecDeque<Option<String>>,
    pub words: Vec<Word<'t>>,
}

#[derive(thiserror::Error, Debug)]
pub enum BuilderError<'t> {
    #[error("Unknown reference at {span:?}: {name}")]
    UnknownReference { span: Span<'t>, name: String },
}

impl<'t> SentenceBuilder<'t> {
    pub fn new(
        name: Option<String>,
        ns_idx: NamespaceIndex,
        names: VecDeque<Option<String>>,
    ) -> Self {
        Self {
            name,
            ns_idx,
            names,
            words: vec![],
        }
    }

    pub fn build(self) -> Sentence<'t> {
        Sentence {
            name: self.name,
            words: self.words,
        }
    }

    pub fn literal(&mut self, span: Span<'t>, value: Value) {
        self.words.push(Word {
            inner: InnerWord::Push(value),
            span: Some(span),
            names: Some(self.names.clone()),
        });
        self.names.push_front(None);
    }

    pub fn sentence_idx(&mut self, span: Span<'t>, sentence_idx: SentenceIndex) {
        self.words.push(Word {
            inner: InnerWord::Push(Value::Pointer(Closure(vec![], sentence_idx))),
            span: Some(span),
            names: Some(self.names.clone()),
        });
        self.names.push_front(None);
    }

    pub fn symbol(&mut self, span: Span<'t>, symbol: &str) {
        self.literal(span, Value::Symbol(symbol.to_owned()))
    }

    pub fn mv(&mut self, ident: Identifier<'t>) -> Result<(), BuilderError<'t>> {
        let Some(idx) = self.names.iter().position(|n| match n {
            Some(n) => n.as_str() == ident.0.as_str(),
            None => false,
        }) else {
            return Err(BuilderError::UnknownReference {
                span: ident.0,
                name: ident.0.as_str().to_owned(),
            });
        };
        Ok(self.mv_idx(ident.0, idx))
    }

    pub fn mv_idx(&mut self, span: Span<'t>, idx: usize) {
        let names = self.names.clone();
        let declared = self.names.remove(idx).unwrap();
        self.names.push_front(declared);

        self.words.push(Word {
            inner: InnerWord::Move(idx),
            span: Some(span),
            names: Some(names),
        });
    }

    pub fn cp(&mut self, span: Span<'t>, name: &str) -> Result<(), BuilderError<'t>> {
        let Some(idx) = self.names.iter().position(|n| match n {
            Some(n) => n.as_str() == name,
            None => false,
        }) else {
            return Err(BuilderError::UnknownReference {
                span,
                name: name.to_owned(),
            });
        };
        Ok(self.cp_idx(span, idx))
    }

    pub fn cp_idx(&mut self, span: Span<'t>, idx: usize) {
        let names = self.names.clone();
        self.names.push_front(None);

        self.words.push(Word {
            inner: InnerWord::Copy(idx),
            span: Some(span),
            names: Some(names),
        });
    }

    pub fn sd_idx(&mut self, span: Span<'t>, idx: usize) {
        let names = self.names.clone();

        let declared = self.names.pop_front().unwrap();
        self.names.insert(idx, declared);

        self.words.push(Word {
            inner: InnerWord::Send(idx),
            span: Some(span),
            names: Some(names),
        });
    }
    pub fn sd_top(&mut self, span: Span<'t>) {
        self.sd_idx(span, self.names.len() - 1)
    }

    pub fn drop_idx(&mut self, span: Span<'t>, idx: usize) {
        let names = self.names.clone();
        let declared = self.names.remove(idx).unwrap();

        self.words.push(Word {
            inner: InnerWord::Drop(idx),
            span: Some(span),
            names: Some(names),
        });
    }

    pub fn path(&mut self, Path { span, segments }: Path<'t>) {
        for segment in segments.iter() {
            self.literal(*segment, Value::Symbol(segment.as_str().to_owned()));
        }
        self.literal(span, Value::Namespace(self.ns_idx));
        for segment in segments {
            self.builtin(segment, Builtin::Get);
        }
    }

    pub fn builtin(&mut self, span: Span<'t>, builtin: Builtin) {
        self.words.push(Word {
            inner: InnerWord::Builtin(builtin),
            span: Some(span),
            names: Some(self.names.clone()),
        });
        match builtin {
            Builtin::Add
            | Builtin::Eq
            | Builtin::Curry
            | Builtin::Or
            | Builtin::And
            | Builtin::Get
            | Builtin::SymbolCharAt
            | Builtin::Cons => {
                self.names.pop_front();
                self.names.pop_front();
                self.names.push_front(None);
            }
            Builtin::NsEmpty => {
                self.names.push_front(None);
            }
            Builtin::NsGet => {
                let ns = self.names.pop_front().unwrap();
                self.names.pop_front();
                self.names.push_front(ns);
                self.names.push_front(None);
            }
            Builtin::NsInsert => {
                self.names.pop_front();
                self.names.pop_front();
                self.names.pop_front();
                self.names.push_front(None);
            }
            Builtin::NsRemove => {
                let ns = self.names.pop_front().unwrap();
                self.names.pop_front();
                self.names.push_front(ns);
                self.names.push_front(None);
            }
            Builtin::Not | Builtin::SymbolLen | Builtin::Deref => {
                self.names.pop_front();
                self.names.push_front(None);
            }
            Builtin::AssertEq => {
                self.names.pop_front();
                self.names.pop_front();
            }
            Builtin::Snoc => {
                self.names.pop_front();
                self.names.push_front(None);
                self.names.push_front(None);
            }
            Builtin::Stash => {
                todo!()
            }
            Builtin::Unstash => {
                todo!()
            }
        }
    }

    fn func_call(&mut self, call: ast::Call<'t>) -> Result<usize, BuilderError<'t>> {
        let argc = call.args.len();

        for arg in call.args.into_iter().rev() {
            self.value_expr(arg);
        }

        match call.func {
            ast::PathOrIdent::Path(p) => self.path(p),
            ast::PathOrIdent::Ident(i) => self.mv(i)?,
        }
        Ok(argc)
    }

    fn value_expr(&mut self, expr: ValueExpression<'t>) -> Result<(), BuilderError<'t>> {
        match expr {
            ValueExpression::Literal(literal) => Ok(self.literal(literal.span, literal.value)),
            ValueExpression::Path(path) => Ok(self.path(path)),
            ValueExpression::Identifier(identifier) => self.mv(identifier),
        }
    }
}

builtins! {
    (Add, add),
    (Eq, eq),
    (AssertEq, assert_eq),
    (Curry, curry),
    (Or, or),
    (And, and),
    (Not, not),
    (Get, get),
    (SymbolCharAt, symbol_char_at),
    (SymbolLen, symbol_len),

    (NsEmpty, ns_empty),
    (NsInsert, ns_insert),
    (NsGet, ns_get),
    (NsRemove, ns_remove),

    (Cons, cons),
    (Snoc, snoc),

    (Deref, deref),

    (Stash, stash),
    (Unstash, unstash),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Word<'t> {
    pub inner: InnerWord,
    pub span: Option<Span<'t>>,
    pub names: Option<VecDeque<Option<String>>>,
}

impl<'t> From<InnerWord> for Word<'t> {
    fn from(value: InnerWord) -> Self {
        Self {
            inner: value,
            span: None,
            names: None,
        }
    }
}
impl<'t> From<Value> for Word<'t> {
    fn from(value: Value) -> Self {
        Self {
            inner: InnerWord::Push(value),
            span: None,
            names: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InnerWord {
    Push(Value),
    Copy(usize),
    Drop(usize),
    Move(usize),
    Send(usize),
    Ref(usize),
    Builtin(Builtin),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value {
    Symbol(String),
    Usize(usize),
    List(Vec<Value>),
    Pointer(Closure),
    Handle(usize),
    Bool(bool),
    Char(char),
    Namespace(NamespaceIndex),
    Namespace2(Namespace2),
    Nil,
    Cons(Box<Value>, Box<Value>),
    Ref(usize),
}

impl Value {
    pub fn is_small(&self) -> bool {
        match self {
            Value::Nil
            | Value::Symbol(_)
            | Value::Usize(_)
            | Value::Char(_)
            | Value::Bool(_)
            | Value::Ref(_) => true,
            Value::Namespace(namespace_index) => todo!(),
            Value::Pointer(Closure(vec, _)) => true,
            Value::List(_) | Value::Handle(_) | Value::Namespace2(_) | Value::Cons(_, _) => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Closure(pub Vec<Value>, pub SentenceIndex);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Namespace2 {
    pub items: Vec<(String, Value)>,
}

pub struct ValueView<'a, 't> {
    pub lib: &'a Library<'t>,
    pub value: &'a Value,
}

impl<'a, 't> std::fmt::Display for ValueView<'a, 't> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Value::Symbol(arg0) => write!(f, "@{}", arg0.replace("\n", "\\n")),
            Value::Usize(arg0) => write!(f, "{}", arg0),
            Value::List(arg0) => todo!(),
            Value::Handle(arg0) => todo!(),
            Value::Namespace(arg0) => write!(f, "ns({})", arg0.0),
            Value::Namespace2(arg0) => write!(f, "ns(TODO)"),
            Value::Bool(arg0) => write!(f, "{}", arg0),
            Value::Nil => write!(f, "nil"),
            Value::Cons(car, cdr) => write!(
                f,
                "cons({}, {})",
                ValueView {
                    lib: self.lib,
                    value: car
                },
                ValueView {
                    lib: self.lib,
                    value: cdr
                }
            ),
            Value::Ref(arg0) => write!(f, "ref({})", arg0),
            Value::Char(arg0) => write!(f, "'{}'", arg0),
            Value::Pointer(Closure(values, ptr)) => {
                write!(
                    f,
                    "[{}]{}#{}",
                    values
                        .iter()
                        .map(|v| ValueView {
                            lib: self.lib,
                            value: v
                        })
                        .join(", "),
                    if *ptr == SentenceIndex::TRAP {
                        "TRAP"
                    } else {
                        if let Some(name) = &self.lib.sentences[*ptr].name {
                            name
                        } else {
                            "UNKNOWN"
                        }
                    },
                    ptr.0
                )
            }
        }
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Self::Usize(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<char> for Value {
    fn from(value: char) -> Self {
        Self::Char(value)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Judgement {
    Eq(usize, usize),
    OutExact(usize, Value),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Type {
    pub arity_in: usize,
    pub arity_out: usize,
    pub judgements: Vec<Judgement>,
}

impl Type {
    const NULL: Self = Type {
        arity_in: 0,
        arity_out: 0,
        judgements: vec![],
    };

    fn pad(&self) -> Self {
        Type {
            arity_in: self.arity_in + 1,
            arity_out: self.arity_out + 1,
            judgements: self
                .judgements
                .iter()
                .cloned()
                .chain(std::iter::once(Judgement::Eq(
                    self.arity_in,
                    self.arity_out,
                )))
                .collect(),
        }
    }

    pub fn compose(mut self, mut other: Self) -> Self {
        while self.arity_out < other.arity_in {
            self = self.pad()
        }
        while other.arity_in < self.arity_out {
            other = other.pad()
        }

        let mut res: Vec<Judgement> = vec![];
        for j1 in self.judgements {
            match j1 {
                Judgement::Eq(i1, o1) => {
                    for j2 in other.judgements.iter() {
                        match j2 {
                            Judgement::Eq(i2, o2) => {
                                if o1 == *i2 {
                                    res.push(Judgement::Eq(i1, *o2));
                                }
                            }
                            Judgement::OutExact(_, _) => {}
                        }
                    }
                }
                Judgement::OutExact(o1, value) => {
                    for j2 in other.judgements.iter() {
                        match j2 {
                            Judgement::Eq(i2, o2) => {
                                if o1 == *i2 {
                                    res.push(Judgement::OutExact(*o2, value.clone()));
                                }
                            }
                            Judgement::OutExact(_, _) => {}
                        }
                    }
                }
            }
        }

        for j2 in other.judgements {
            match j2 {
                Judgement::Eq(i2, o2) => {}
                Judgement::OutExact(o, value) => res.push(Judgement::OutExact(o, value)),
            }
        }

        Type {
            arity_in: self.arity_in,
            arity_out: other.arity_out,
            judgements: res,
        }
    }
}

#[cfg(test)]
mod tests {}
