use std::{
    collections::{BTreeMap, VecDeque},
    fmt::Display,
    path::{Path, PathBuf},
    usize,
};

use derive_more::derive::{From, Into};
use itertools::Itertools;
use pest::iterators::Pair;
use thiserror::Error;
use typed_index_collections::TiVec;

use crate::{
    ir::{self, QualifiedName},
    ast,
    source::{self, Span},
};

// use crate::ast::{
//     self, ident_from_pair, Bindings, Identifier, Literal, PathOrIdent, ProcMatchBlock,
//     ProcMatchCase, Rule, ValueExpression,
// };

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SentenceIndex(usize);

impl SentenceIndex {
    pub const TRAP: Self = SentenceIndex(usize::MAX);
}

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NamespaceIndex(usize);

#[derive(Debug, Clone, Default)]
pub struct Library {
    pub namespaces: TiVec<NamespaceIndex, Namespace>,
    pub sentences: TiVec<SentenceIndex, Sentence>,

    pub exports: BTreeMap<String, SentenceIndex>,
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

#[derive(Debug, Error)]

pub struct LoadError {
    pub path: PathBuf,
    pub error: LoadErrorInner,
}

impl Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "In file {}, error: {}", self.path.display(), self.error)
    }
}

#[derive(Debug, Error)]

pub enum LoadErrorInner {
    #[error("error reading file")]
    IO(#[from] anyhow::Error),
    #[error("duplicate path")]
    DuplicatePath,
    #[error("error parsing file:\n{0}")]
    Parse(#[from] pest::error::Error<ast::Rule>),
    #[error("error compiling file: {0}")]
    Compile(CompileError),
}

impl Library {
    // pub fn root_namespace(&self) -> &Namespace {
    //     &self.namespaces[self.root_ns.unwrap()]
    // }

    pub fn main(&self) -> Option<SentenceIndex> {
        self.exports.get("main").cloned()
    }

    // pub fn load(loader: &'t mut ast::Loader, name: &'t str) -> Result<Self, LoadError> {
    //     Self::load_srcs(loader, name)?;

    //     let mut res = Self {
    //         namespaces: TiVec::new(),
    //         sentences: TiVec::new(),
    //         root_ns: None,
    //         code: loader.get(name).unwrap(),
    //     };
    //     res.root_ns = Some(res.visit_module(loader, name, None)?);
    //     Ok(res)
    // }

    // fn load_srcs(loader: &mut ast::Loader, name: &str) -> Result<(), LoadError> {
    //     loader.load(name)?;
    //     let contents = loader.get(name).unwrap();

    //     let module = ast::Module::from_str(contents).map_err(|e| {
    //         let path = loader.path(name).clone();
    //         LoadError {
    //             error: LoadErrorInner::Parse(e.with_path(path.to_str().unwrap())),
    //             path,
    //         }
    //     })?;
    //     let names = module
    //         .imports
    //         .into_iter()
    //         .map(|i| i.as_str().to_owned())
    //         .collect_vec();
    //     for name in names {
    //         Self::load_srcs(loader, &name)?
    //     }
    //     Ok(())
    // }

    // fn visit_module(
    //     &mut self,
    //     loader: &'t ast::Loader,
    //     name: &'t str,
    //     parent: Option<NamespaceIndex>,
    // ) -> Result<NamespaceIndex, LoadError> {
    //     let contents = loader.get(name).unwrap();
    //     let path = loader.path(name);

    //     let module = ast::Module::from_str(contents).map_err(|e| {
    //         let path = loader.path(name).clone();
    //         LoadError {
    //             error: LoadErrorInner::Parse(e.with_path(path.to_str().unwrap())),
    //             path,
    //         }
    //     })?;
    //     let mod_ns = self
    //         .visit_ns(&path, module.namespace, parent)
    //         .map_err(|e| match e {
    //             BuilderError::UnknownReference(i) => LoadError {
    //                 path: loader.path(name).clone(),
    //                 error: LoadErrorInner::Compile(CompileError::UnknownReference {
    //                     location: SourceLocation {
    //                         file: loader.path(name),
    //                         line: i.0.start_pos().line_col().0,
    //                         col: i.0.start_pos().line_col().1,
    //                     },
    //                     name: i.as_str().to_owned(),
    //                 }),
    //             },
    //         })?;
    //     for name in module.imports.into_iter() {
    //         let submod = self.visit_module(loader, name.as_str(), Some(mod_ns))?;

    //         self.namespaces[mod_ns]
    //             .0
    //             .push((name.as_str().to_owned(), Entry::Namespace(submod)));
    //     }
    //     Ok(mod_ns)
    // }

    // fn visit_ns(
    //     &mut self,
    //     modname: &Path,
    //     ns: ast::Namespace<'t>,
    //     parent: Option<NamespaceIndex>,
    // ) -> Result<NamespaceIndex, BuilderError<'t>> {
    //     let ns_idx = self.namespaces.push_and_get_key(Namespace::default());

    //     if let Some(parent) = parent {
    //         self.namespaces[ns_idx]
    //             .0
    //             .push(("super".to_owned(), Entry::Namespace(parent)));
    //     }

    //     for decl in ns.decls {
    //         match decl.value {
    //             ast::DeclValue::Namespace(namespace) => {
    //                 let subns = self.visit_ns(modname, namespace, Some(ns_idx))?;
    //                 self.namespaces[ns_idx]
    //                     .0
    //                     .push((decl.name, Entry::Namespace(subns)));
    //             }
    //             // ast::DeclValue::Code(code) => {
    //             //     let sentence_idx = self.visit_code(&decl.name, ns_idx, VecDeque::new(), code);
    //             //     self.namespaces[ns_idx].0.push((
    //             //         decl.name,
    //             //         Entry::Value(Value::Pointer(Closure(vec![], sentence_idx))),
    //             //     ));
    //             // }
    //             ast::DeclValue::Proc(p) => {
    //                 let sentence_idx =
    //                     self.visit_block(modname, &decl.name, ns_idx, VecDeque::new(), p)?;
    //                 self.namespaces[ns_idx].0.push((
    //                     decl.name,
    //                     Entry::Value(Value::Pointer(Closure(vec![], sentence_idx))),
    //                 ));
    //             }
    //         }
    //     }
    //     Ok(ns_idx)
    // }

    // fn visit_block(
    //     &mut self,
    //     modname: &Path,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     mut names: VecDeque<Option<String>>,
    //     block: ast::Block<'t>,
    // ) -> Result<SentenceIndex, BuilderError<'t>> {
    //     match block {
    //         ast::Block::Bind {
    //             name: bind_name,
    //             inner,
    //         } => {
    //             names.push_back(Some(bind_name.as_str().to_owned()));
    //             self.visit_block(modname, name, ns_idx, names, *inner)
    //         }
    //         ast::Block::Expression {
    //             span,
    //             expr: ast::Expression::Call(call),
    //             next,
    //         } => {
    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names);
    //             let kind = call.kind;
    //             let argc = builder.func_call(call)?;

    //             let mut leftover_names: VecDeque<Option<String>> =
    //                 builder.names.iter().skip(argc + 1).cloned().collect();

    //             let next = self.visit_block(modname, name, ns_idx, leftover_names, *next)?;

    //             builder.sentence_idx(span, next);
    //             // Stack: (leftovers) (args) to_call next

    //             while builder.names.len() > argc + 2 {
    //                 builder.mv_idx(span, argc + 2);
    //                 builder.mv_idx(span, 1);
    //                 builder.builtin(span, Builtin::Curry);
    //             }
    //             // Stack: (args) to_call next
    //             builder.mv_idx(span, 1);
    //             // Stack: (args) next to_call

    //             match kind {
    //                 ast::CallKind::Standard => {}
    //                 ast::CallKind::Request => {
    //                     builder.symbol(span, "req");
    //                     builder.mv_idx(span, 1);
    //                 }
    //                 ast::CallKind::Response => {
    //                     builder.symbol(span, "resp");
    //                     builder.mv_idx(span, 1);
    //                 }
    //             }
    //             builder.symbol(span, "exec");

    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::Expression {
    //             span,
    //             expr: ast::Expression::Value(value_expr),
    //             next,
    //         } => {
    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names);
    //             let argc = builder.value_expr(value_expr)?;

    //             let mut leftover_names: VecDeque<Option<String>> =
    //                 builder.names.iter().skip(1).cloned().collect();

    //             let next = self.visit_block(modname, name, ns_idx, leftover_names, *next)?;

    //             builder.sentence_idx(span, next);
    //             // Stack: (leftovers) value next

    //             while builder.names.len() > 2 {
    //                 builder.mv_idx(span, 2);
    //                 builder.mv_idx(span, 1);
    //                 builder.builtin(span, Builtin::Curry);
    //             }
    //             // Stack: value next
    //             builder.symbol(span, "exec");

    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::Become { span, call } => {
    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names);
    //             let argc = builder.func_call(call)?;

    //             // Stack: (leftovers) (args) to_call

    //             while builder.names.len() > argc + 1 {
    //                 builder.drop_idx(span, argc + 1);
    //             }
    //             builder.literal_split(span, Value::Symbol("exec".to_owned()));

    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::Raw(sentence) => self.visit_sentence(modname, name, ns_idx, sentence),
    //         ast::Block::AssertEq { literal, inner } => {
    //             let next = self.visit_block(modname, name, ns_idx, names.clone(), *inner)?;
    //             let assert_idx = names.len();
    //             names.push_back(None);

    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names);
    //             builder.mv_idx(literal.span, assert_idx);
    //             builder.literal_split(literal.span, literal.value);
    //             builder.builtin(literal.span, Builtin::AssertEq);
    //             builder.sentence_idx(literal.span, next);
    //             builder.symbol(literal.span, "exec");
    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::Drop { span, inner } => {
    //             let next = self.visit_block(modname, name, ns_idx, names.clone(), *inner)?;
    //             let drop_idx = names.len();
    //             names.push_back(None);

    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names);
    //             builder.drop_idx(span, drop_idx);
    //             builder.sentence_idx(span, next);
    //             builder.symbol(span, "exec");
    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::If {
    //             span,
    //             expr,
    //             true_case,
    //             false_case,
    //         } => {
    //             let mut builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names.clone());
    //             builder.value_expr(expr)?;

    //             let mut subnames = builder.names.clone();
    //             subnames.pop_front(); // Drop the boolean.

    //             let true_case =
    //                 self.visit_block(modname, name, ns_idx, subnames.clone(), *true_case)?;
    //             let false_case =
    //                 self.visit_block(modname, name, ns_idx, subnames.clone(), *false_case)?;

    //             builder.sentence_idx(span, true_case);
    //             builder.sentence_idx(span, false_case);
    //             builder.builtin(span, Builtin::If);
    //             builder.symbol(span, "exec");
    //             Ok(self.sentences.push_and_get_key(builder.build()))
    //         }
    //         ast::Block::Match { span, cases, els } => {
    //             let els = if let Some(els) = els {
    //                 self.visit_block(modname, name, ns_idx, names.clone(), *els)?
    //             } else {
    //                 let mut panic_builder = SentenceBuilder::new(
    //                     modname,
    //                     Some(name.to_owned()),
    //                     ns_idx,
    //                     VecDeque::new(),
    //                 );
    //                 panic_builder.symbol(span, "panic");
    //                 self.sentences.push_and_get_key(panic_builder.build())
    //             };

    //             let mut next_case = els;

    //             let discrim_idx = names.len();
    //             for case in cases.into_iter().rev() {
    //                 let case_span = case.span;

    //                 let if_case_matches_idx =
    //                     self.visit_block(modname, name, ns_idx, names.clone(), case.body)?;

    //                 let mut case_builder = SentenceBuilder::new(
    //                     modname,
    //                     Some(name.to_owned()),
    //                     ns_idx,
    //                     VecDeque::new(),
    //                 );
    //                 case_builder.cp_idx(case.span, discrim_idx);
    //                 case_builder.literal_split(case.span, case.value);
    //                 case_builder.builtin(case_span, Builtin::Eq);

    //                 case_builder.sentence_idx(case_span, if_case_matches_idx);
    //                 case_builder.sentence_idx(case_span, next_case);
    //                 case_builder.builtin(case_span, Builtin::If);

    //                 case_builder.symbol(case_span, "exec");
    //                 next_case = self.sentences.push_and_get_key(case_builder.build());
    //             }

    //             Ok(next_case)
    //         }
    //         ast::Block::Unreachable { span } => {
    //             let mut panic_builder =
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, VecDeque::new());
    //             panic_builder.symbol(span, "panic");
    //             Ok(self.sentences.push_and_get_key(panic_builder.build()))
    //         }
    //     }
    //     // let mut names: VecDeque<Option<String>> = bindings
    //     //     .bindings
    //     //     .into_iter()
    //     //     .map(|p| match p {
    //     //         ast::Binding::Ident(i) => Some(i.as_str().to_owned()),
    //     //         ast::Binding::Literal(_) => todo!(),
    //     //     })
    //     //     // .chain(["caller".to_owned()])
    //     //     .collect();
    //     // self.visit_block_pair(name, ns_idx, names, body)
    // }

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
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names.clone());

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
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names.clone());
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
    //                 SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, VecDeque::new());
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
    //     let mut builder = SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, names.clone());

    //     let argc = builder.expr(block.expr)?;
    //     // Stack: (leftover names) (args) to_call

    //     let mut leftover_names: VecDeque<Option<String>> =
    //         builder.names.iter().skip(argc + 1).cloned().collect();

    //     let mut panic_builder =
    //         SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, VecDeque::new());
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
    //             SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, VecDeque::new());

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

    // fn visit_sentence(
    //     &mut self,
    //     modname: &Path,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     sentence: ast::RawSentence<'t>,
    // ) -> Result<SentenceIndex, BuilderError<'t>> {
    //     let mut builder =
    //         SentenceBuilder::new(modname, Some(name.to_owned()), ns_idx, VecDeque::new());

    //     for word in sentence.words {
    //         self.visit_raw_word(modname, name, ns_idx, &mut builder, word)?;
    //     }
    //     Ok(self.sentences.push_and_get_key(builder.build()))
    // }

    // fn visit_raw_word(
    //     &mut self,
    //     modname: &Path,
    //     name: &str,
    //     ns_idx: NamespaceIndex,
    //     builder: &mut SentenceBuilder<'t>,
    //     raw_word: ast::RawWord<'t>,
    // ) -> Result<(), BuilderError<'t>> {
    //     match raw_word.inner {
    //         ast::RawWordInner::Expression(expr) => builder.value_expr(expr),
    //         ast::RawWordInner::Bindings(b) => {
    //             builder.bindings(b);
    //             Ok(())
    //         }
    //         // ast::RawWordInner::Literal(v) => builder.literal(v.span, v.value),
    //         ast::RawWordInner::FunctionLike(f, idx) => {
    //             match f.0.as_str() {
    //                 "tuple" => Ok(builder.tuple(raw_word.span, idx)),
    //                 "untuple" => Ok(builder.untuple(raw_word.span, idx)),
    //                 //     "cp" => InnerWord::Copy(idx),
    //                 //     "drop" => InnerWord::Drop(idx),
    //                 //     "mv" => InnerWord::Move(idx),
    //                 //     "sd" => InnerWord::Send(idx),
    //                 //     "ref" => InnerWord::Ref(idx),
    //                 _ => panic!("unknown reference: {:?}", f),
    //             }
    //         }
    //         ast::RawWordInner::Builtin(name) => {
    //             if let Some(builtin) = Builtin::ALL
    //                 .iter()
    //                 .find(|builtin| builtin.name() == name.as_str())
    //             {
    //                 builder.builtin(raw_word.span, *builtin);
    //                 Ok(())
    //             } else {
    //                 panic!("unknown builtin: {:?}", name)
    //             }
    //         }
    //         ast::RawWordInner::Sentence(s) => {
    //             let sentence_idx = self.visit_sentence(modname, name, ns_idx, s)?;
    //             builder.sentence_idx(raw_word.span, sentence_idx);
    //             Ok(())
    //         }
    //     }
    // }
}

#[derive(Debug, Clone)]
pub struct Sentence {
    pub name: QualifiedName,
    pub words: Vec<Word>,
}

macro_rules! builtins {
    {
        $(($ident:ident, $name:literal),)*
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
                    $(Builtin::$ident => $name,)*
                }
            }
        }
    };
}

#[derive(Debug, thiserror::Error)]
pub enum CompileError {
    #[error("At {location}, unknown reference: {name}")]
    UnknownReference {
        location: source::Location,
        name: String,
    },
}

#[derive(Debug)]
pub enum BuilderError {
    UnknownReference(ir::Identifier),
}

builtins! {
    (Add, "add"),
    (Sub, "sub"),
    (Prod, "prod"),
    (Eq, "eq"),
    (AssertEq, "assert_eq"),
    (Curry, "curry"),
    (Or, "or"),
    (And, "and"),
    (Not, "not"),
    (Get, "get"),
    (SymbolCharAt, "symbol_char_at"),
    (SymbolLen, "symbol_len"),

    (Lt, "lt"),

    (NsEmpty, "ns_empty"),
    (NsInsert, "ns_insert"),
    (NsGet, "ns_get"),
    (NsRemove, "ns_remove"),

    (Cons, "cons"),
    (Snoc, "snoc"),

    (Deref, "deref"),

    (If, "if"),

    (Ord, "ord"),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Word {
    pub inner: InnerWord,
    // pub modname: PathBuf,
    pub span: Span,
    pub names: Option<VecDeque<Option<String>>>,
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
    Tuple(usize),
    Untuple(usize),
    Call(SentenceIndex),
    Branch(SentenceIndex, SentenceIndex),
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Value {
    Symbol(String),
    Usize(usize),
    List(Vec<Value>),
    Tuple(Vec<Value>),
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

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Closure(pub Vec<Value>, pub SentenceIndex);

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Namespace2 {
    pub items: Vec<(String, Value)>,
}

pub struct ValueView<'a> {
    pub sources: &'a source::Sources,
    pub value: &'a Value,
}

impl<'a> std::fmt::Display for ValueView<'a> {
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
                    sources: self.sources,
                    value: car
                },
                ValueView {
                    sources: self.sources,
                    value: cdr
                }
            ),
            Value::Tuple(values) => write!(
                f,
                "({})",
                values
                    .iter()
                    .map(|v| ValueView {
                        sources: self.sources,
                        value: v
                    })
                    .join(", ")
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
                            sources: self.sources,
                            value: v
                        })
                        .join(", "),
                    if *ptr == SentenceIndex::TRAP {
                        "TRAP"
                    } else {
                        // if let Some(name) = &self.sources.sentences[*ptr].name {
                        //     name
                        // } else {
                        "UNKNOWN"
                        // }
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
