use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    bytecode,
    compiler2::{
        ast::{self},
        unlinked,
    },
    parser::{self, source},
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, debug_with::DebugWith)]
#[debug_with(passthrough)]
pub struct ModuleIndex(usize);

#[derive(Debug, Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct ConstDecl {
    pub name: parser::Identifier,
    pub value: ast::ConstRefIndex,
}

#[derive(Debug, Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct SentenceDecl {
    pub name: parser::Identifier,
    pub sentence: ast::SentenceDefIndex,
}

#[derive(Debug, Clone, Default, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Module {
    pub submodules: Vec<ModuleDecl>,
    pub const_decls: Vec<ConstDecl>,
    pub sentence_decls: Vec<SentenceDecl>,
}

#[derive(Debug, Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct ModuleDecl {
    pub name: parser::Identifier,
    pub module: ModuleIndex,
}

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Library {
    pub root_module: ModuleIndex,
    pub modules: TiVec<ModuleIndex, Module>,
    pub symbol_defs: TiVec<bytecode::SymbolIndex, ast::SymbolDef>,
    pub const_refs: TiVec<ast::ConstRefIndex, ast::ConstRef>,
    pub const_decls: Vec<ConstDecl>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, FancySentence>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, unlinked::SentenceRef>,
}

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
struct FancySentence {
    words: Vec<FancyWord>,
}

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
struct FancyWord {
    inner: FancyWordInner,
    span: source::Span,
}

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
enum FancyWordInner {
    Word(ast::WordInner),
    FnInit,
    Local(parser::Identifier),
    BindVar(parser::Identifier),
    CopyVar(parser::Identifier),
    MoveVar(parser::Identifier),
    Tuple(usize),
}

struct Builder<'a> {
    sources: &'a source::Sources,
    res: Library,
}

impl<'a> Builder<'a> {
    fn build(self) -> Library {
        self.res
    }

    fn visit_file(&mut self, file: parser::File) -> ModuleIndex {
        self.visit_module(file.namespace)
    }

    fn visit_module(&mut self, namespace: parser::Namespace) -> ModuleIndex {
        let mut module = Module::default();
        for decl in namespace.decls {
            match decl {
                parser::Decl::ModuleDecl(module_decl) => {
                    module.submodules.push(ModuleDecl {
                        name: module_decl.name,
                        module: self.visit_module(module_decl.namespace),
                    });
                }
                parser::Decl::ConstDecl(const_decl) => {
                    module.const_decls.push(ConstDecl {
                        name: const_decl.name,
                        value: self.visit_const_expr(const_decl.value),
                    });
                }
                parser::Decl::SentenceDecl(sentence_decl) => {
                    module.sentence_decls.push(SentenceDecl {
                        name: sentence_decl.name,
                        sentence: self.visit_sentence_def(sentence_decl.sentence),
                    });
                }
                parser::Decl::SymbolDecl(symbol_decl) => {
                    let symbol_def_index = self
                        .res
                        .symbol_defs
                        .push_and_get_key(ast::SymbolDef(symbol_decl.name.0));
                    let const_ref_index = self.res.const_refs.push_and_get_key(
                        ast::ConstRef::Inline(bytecode::PrimitiveValue::Symbol(symbol_def_index)),
                    );
                    module.const_decls.push(ConstDecl {
                        name: symbol_decl.name,
                        value: const_ref_index,
                    });
                }
            }
        }
        self.res.modules.push_and_get_key(module)
    }

    fn visit_const_expr(&mut self, const_expr: parser::ConstExpr) -> ast::ConstRefIndex {
        self.res.const_refs.push_and_get_key(match const_expr {
            parser::ConstExpr::Literal(literal) => {
                ast::ConstRef::Inline(literal.into_value(self.sources))
            }
            parser::ConstExpr::Path(path) => {
                ast::ConstRef::Path(ast::Path(path.segments.iter().map(|i| i.0).collect()))
            }
        })
    }

    fn visit_sentence_def(&mut self, sentence: parser::Sentence) -> ast::SentenceDefIndex {
        let words = sentence
            .words
            .into_iter()
            .map(|w| self.visit_fancy_word(w))
            .collect();
        self.res
            .sentence_defs
            .push_and_get_key(FancySentence { words })
    }

    fn visit_word(&mut self, word: parser::Word) -> ast::Word {
        let inner = match word.operator.0.as_str(self.sources) {
            "push" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Push(
                    self.visit_word_arg_const_expr(arg),
                ))
            }
            "cp" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Copy(
                    self.visit_word_arg_variable(arg),
                ))
            }
            "mv" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Move(
                    self.visit_word_arg_variable(arg),
                ))
            }
            "drop" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Drop(
                    self.visit_word_arg_variable(arg),
                ))
            }
            "tuple" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Tuple(
                    self.visit_word_arg_usize(arg),
                ))
            }
            "untuple" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::StackOperation(ast::StackOperation::Untuple(
                    self.visit_word_arg_usize(arg),
                ))
            }
            "call" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                ast::WordInner::Call(self.visit_word_arg_sentence(arg))
            }
            _ => {
                if let Some(builtin) = bytecode::Builtin::ALL
                    .iter()
                    .find(|b| b.name() == word.operator.0.as_str(self.sources))
                {
                    ast::WordInner::StackOperation(ast::StackOperation::Builtin(*builtin))
                } else {
                    panic!("unknown word: {}", word.operator.0.as_str(self.sources))
                }
            }
        };
        ast::Word {
            inner,
            span: word.span,
        }
    }

    fn visit_fancy_word(&mut self, word: parser::Word) -> FancyWord {
        let span = word.span;
        let inner = match word.operator.0.as_str(self.sources) {
            "fn_init" => FancyWordInner::FnInit,
            "bind_var" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                let parser::WordArg::Identifier(identifier) = arg else {
                    panic!("expected identifier: {:?}", arg);
                };
                FancyWordInner::BindVar(identifier)
            }
            "copy_var" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                let parser::WordArg::Identifier(identifier) = arg else {
                    panic!("expected identifier: {:?}", arg);
                };
                FancyWordInner::CopyVar(identifier)
            }
            "move_var" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                let parser::WordArg::Identifier(identifier) = arg else {
                    panic!("expected identifier: {:?}", arg);
                };
                FancyWordInner::MoveVar(identifier)
            }
            "local" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                let parser::WordArg::Identifier(identifier) = arg else {
                    panic!("expected identifier: {:?}", arg);
                };
                FancyWordInner::Local(identifier)
            }
            "fancy_tuple" => {
                let arg = word.args.into_iter().exactly_one().unwrap();
                FancyWordInner::Tuple(self.visit_word_arg_usize(arg))
            }
            _ => FancyWordInner::Word(self.visit_word(word).inner),
        };
        FancyWord { inner, span }
    }

    fn visit_word_arg_const_expr(&mut self, word_arg: parser::WordArg) -> ast::ConstRefIndex {
        let result: ast::ConstRef = match word_arg {
            parser::WordArg::Literal(literal) => {
                ast::ConstRef::Inline(literal.into_value(self.sources))
            }
            parser::WordArg::Path(path) => ast::ConstRef::Path(convert_path(path)),
            _ => panic!("expected literal or path: {:?}", word_arg),
        };
        self.res.const_refs.push_and_get_key(result)
    }

    fn visit_word_arg_sentence(&mut self, word_arg: parser::WordArg) -> ast::SentenceRefIndex {
        let result: unlinked::SentenceRef = match word_arg {
            parser::WordArg::Sentence(sentence) => {
                unlinked::SentenceRef::Inline(self.visit_sentence_def(sentence))
            }
            parser::WordArg::Path(path) => unlinked::SentenceRef::Path(convert_path(path)),
            _ => panic!("expected sentence or path: {:?}", word_arg),
        };
        self.res.sentence_refs.push_and_get_key(result)
    }

    fn visit_word_arg_variable(&mut self, word_arg: parser::WordArg) -> usize {
        match word_arg {
            parser::WordArg::Literal(literal) => match literal.into_value(self.sources) {
                bytecode::PrimitiveValue::Usize(value) => value,
                _ => panic!("expected usize: {:?}", literal),
            },
            _ => panic!("expected variable: {:?}", word_arg),
        }
    }

    fn visit_word_arg_usize(&mut self, word_arg: parser::WordArg) -> usize {
        match word_arg {
            parser::WordArg::Literal(literal) => match literal.into_value(self.sources) {
                bytecode::PrimitiveValue::Usize(value) => value,
                _ => panic!("expected usize: {:?}", literal),
            },
            _ => panic!("expected usize: {:?}", word_arg),
        }
    }
}

impl Library {
    pub fn from_parsed(sources: &source::Sources, parsed_library: parser::Library) -> Self {
        let mut builder = Builder {
            sources,
            res: Library {
                root_module: ModuleIndex(0),
                modules: TiVec::new(),
                symbol_defs: TiVec::new(),
                const_refs: TiVec::new(),
                const_decls: vec![],
                sentence_defs: TiVec::new(),
                sentence_refs: TiVec::new(),
            },
        };

        let mut file_modules: Vec<(ast::Path, ModuleIndex)> = vec![];
        for file in parsed_library.files.into_iter() {
            let mod_path = ast::Path(file.mod_path.clone());
            let module_index = builder.visit_file(file);
            file_modules.push((mod_path, module_index));
        }
        let root_module_index = file_modules
            .iter()
            .find(|(mod_path, _)| mod_path.0.is_empty())
            .unwrap()
            .1;
        builder.res.root_module = root_module_index;
        for (parent_mod_path, parent_index) in file_modules.iter() {
            for (child_mod_path, child_index) in file_modules.iter() {
                if parent_mod_path.0.len() + 1 == child_mod_path.0.len()
                    && parent_mod_path.0.iter().zip(child_mod_path.0.iter()).all(
                        |(parent_segment, child_segment)| {
                            parent_segment.as_str(sources) == child_segment.as_str(sources)
                        },
                    )
                {
                    let parent = &mut builder.res.modules[*parent_index];
                    parent.submodules.push(ModuleDecl {
                        name: parser::Identifier(child_mod_path.0.last().unwrap().clone()),
                        module: *child_index,
                    });
                }
            }
        }
        builder.build()
    }

    pub fn resolve(
        mut self,
        sources: &source::Sources,
    ) -> Result<unlinked::Library, anyhow::Error> {
        self.update_paths(sources, self.root_module, ast::Path(vec![]));
        let const_decls = self.get_const_decls(sources, self.root_module, ast::Path(vec![]));
        let sentence_decls = self.get_sentence_decls(sources, self.root_module, ast::Path(vec![]));

        let sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef> = self
            .sentence_defs
            .into_iter()
            .map(|sentence| {
                Self::compile_sentence_def(
                    sources,
                    &mut self.symbol_defs,
                    &mut self.const_refs,
                    sentence,
                )
            })
            .collect();
        Ok(unlinked::Library {
            const_refs: self.const_refs,
            const_decls,
            symbol_defs: self.symbol_defs,
            sentence_defs,
            sentence_refs: self.sentence_refs,
            sentence_decls,
        })
    }

    fn get_const_decls(
        &self,
        sources: &source::Sources,
        module_index: ModuleIndex,
        module_path: ast::Path,
    ) -> Vec<unlinked::ConstDecl> {
        let module = &self.modules[module_index];
        let mut result = Vec::new();
        for const_decl in module.const_decls.iter() {
            result.push(unlinked::ConstDecl {
                name: module_path.join(const_decl.name.0),
                value: const_decl.value,
            });
        }
        for submodule in module.submodules.iter() {
            result.extend(self.get_const_decls(
                sources,
                submodule.module,
                module_path.join(submodule.name.0),
            ));
        }
        result
    }

    fn get_sentence_decls(
        &self,
        sources: &source::Sources,
        module_index: ModuleIndex,
        module_path: ast::Path,
    ) -> Vec<unlinked::SentenceDecl> {
        let module = &self.modules[module_index];
        let mut result = Vec::new();
        for sentence_decl in module.sentence_decls.iter() {
            result.push(unlinked::SentenceDecl {
                name: module_path.join(sentence_decl.name.0),
                value: sentence_decl.sentence,
            });
        }
        for submodule in module.submodules.iter() {
            result.extend(self.get_sentence_decls(
                sources,
                submodule.module,
                module_path.join(submodule.name.0),
            ));
        }
        result
    }

    fn compile_sentence_def(
        sources: &source::Sources,
        symbol_defs: &mut TiVec<bytecode::SymbolIndex, ast::SymbolDef>,
        const_refs: &mut TiVec<ast::ConstRefIndex, ast::ConstRef>,
        sentence: FancySentence,
    ) -> ast::SentenceDef {
        let mut words: Vec<ast::Word> = Vec::new();
        let mut locals: BTreeMap<&str, ast::ConstRefIndex> = BTreeMap::new();
        for word in sentence.words.into_iter() {
            let inners: Vec<ast::WordInner> = match word.inner {
                FancyWordInner::Tuple(size) => {
                    todo!()
                    // let mut result = vec![ast::WordInner::StackOperation(ast::StackOperation::Untuple(2))];
                    // for _ in 0..size {
                    //     result.push(ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)));
                    //     result.push(ast::WordInner::StackOperation(ast::StackOperation::Move(1)));
                    // }
                    // result.push(ast::WordInner::StackOperation(ast::StackOperation::Tuple(size)));
                    // result.push(ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)));
                    // result.push(ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)));
                    // result
                }
                FancyWordInner::Word(inner) => {
                    vec![inner]
                }
                FancyWordInner::Local(identifier) => {
                    let symbol = bytecode::PrimitiveValue::Symbol(
                        symbol_defs.push_and_get_key(ast::SymbolDef(identifier.0)),
                    );
                    let const_ref = const_refs.push_and_get_key(ast::ConstRef::Inline(symbol));
                    locals.insert(identifier.0.as_str(sources), const_ref);
                    vec![]
                }
                FancyWordInner::BindVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());
                    Self::bind_var(*symbol)
                }
                FancyWordInner::CopyVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());

                    Self::move_var(*symbol)
                        .into_iter()
                        .chain([
                            // Stack: ({}, ((), x))
                            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
                            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
                            ast::WordInner::StackOperation(ast::StackOperation::Copy(0)),
                            // Stack: {} () x x
                            ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
                            ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
                            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                            // Stack: {} x ((), x)
                            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                        ])
                        .chain(Self::bind_var(*symbol))
                        .collect()
                }
                FancyWordInner::MoveVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());

                    Self::move_var(*symbol)
                }
                FancyWordInner::FnInit => {
                    vec![
                        ast::WordInner::StackOperation(ast::StackOperation::Tuple(0)),
                        ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                        ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                            bytecode::Builtin::MapNew,
                        )),
                        ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                    ]
                }
            };
            words.extend(inners.into_iter().map(|inner| ast::Word {
                inner,
                span: word.span,
            }));
        }

        ast::SentenceDef { words }
    }

    fn bind_var(local: ast::ConstRefIndex) -> Vec<ast::WordInner> {
        vec![
            // Stack: ({}, ((), x))
            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
            // Stack: {} () x
            ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Push(local)),
            // Stack: () {} x 'x
            ast::WordInner::StackOperation(ast::StackOperation::Builtin(bytecode::Builtin::MapSet)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
        ]
    }

    fn move_var(local: ast::ConstRefIndex) -> Vec<ast::WordInner> {
        vec![
            // Stack: ({'x: x}, ())
            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Push(local)),
            ast::WordInner::StackOperation(ast::StackOperation::Builtin(bytecode::Builtin::MapGet)),
            // Stack: () {} x
            ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
            // Stack: {} ((), x)
            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
        ]
    }

    fn update_paths(
        &mut self,
        sources: &source::Sources,
        module_index: ModuleIndex,
        module_path: ast::Path,
    ) {
        for submodule in self.modules[module_index].submodules.clone().iter() {
            self.update_paths(
                sources,
                submodule.module,
                module_path.join(submodule.name.0),
            );
        }

        let module = &self.modules[module_index];
        for const_decl in module.const_decls.iter() {
            let const_ref = &mut self.const_refs[const_decl.value];
            match const_ref {
                ast::ConstRef::Path(path) => {
                    *path = module_path.join(path.clone());
                }
                _ => {}
            }
        }
        for sentence_decl in module.sentence_decls.iter() {
            let sentence_def = &mut self.sentence_defs[sentence_decl.sentence];
            for word in sentence_def.words.iter_mut() {
                match &word.inner {
                    FancyWordInner::Word(ast::WordInner::Call(sentence_ref_index)) => {
                        let sentence_ref = &mut self.sentence_refs[*sentence_ref_index];
                        match sentence_ref {
                            unlinked::SentenceRef::Path(path) => {
                                *path = module_path.join(path.clone());
                            }
                            _ => {}
                        }
                    }
                    FancyWordInner::Word(ast::WordInner::StackOperation(stack_operation)) => {
                        match stack_operation {
                            ast::StackOperation::Push(const_ref_index) => {
                                let const_ref = &mut self.const_refs[*const_ref_index];
                                match const_ref {
                                    ast::ConstRef::Path(path) => {
                                        *path = module_path.join(path.clone());
                                    }
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                    FancyWordInner::Word(ast::WordInner::Branch(
                        sentence_ref_index,
                        sentence_ref_index1,
                    )) => {
                        let sentence_ref = &mut self.sentence_refs[*sentence_ref_index];
                        match sentence_ref {
                            unlinked::SentenceRef::Path(path) => {
                                *path = module_path.join(path.clone());
                            }
                            _ => {}
                        }
                        let sentence_ref = &mut self.sentence_refs[*sentence_ref_index1];
                        match sentence_ref {
                            unlinked::SentenceRef::Path(path) => {
                                *path = module_path.join(path.clone());
                            }
                            _ => {}
                        }
                    }
                    FancyWordInner::Word(ast::WordInner::JumpTable(items)) => {
                        for item in items.iter() {
                            let sentence_ref = &mut self.sentence_refs[*item];
                            match sentence_ref {
                                unlinked::SentenceRef::Path(path) => {
                                    *path = module_path.join(path.clone());
                                }
                                _ => {}
                            }
                        }
                    }
                    FancyWordInner::FnInit => {}
                    FancyWordInner::Local(identifier) => {}
                    FancyWordInner::BindVar(identifier) => {}
                    FancyWordInner::CopyVar(identifier) => {}
                    FancyWordInner::MoveVar(identifier) => {}
                    FancyWordInner::Tuple(size) => {}
                }
            }
        }
    }
}

fn convert_path(path: parser::Path) -> ast::Path {
    ast::Path(path.segments.iter().map(|i| i.0).collect())
}
