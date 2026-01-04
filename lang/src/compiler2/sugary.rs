use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    bytecode,
    compiler2::{
        ast::{self},
        unlinked, unresolved,
    },
    parser::{self, source},
};

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Library {
    pub root_module: unresolved::ModuleIndex,
    pub modules: TiVec<unresolved::ModuleIndex, unresolved::Module>,
    pub symbol_defs: TiVec<bytecode::SymbolIndex, ast::SymbolDef>,
    pub const_refs: TiVec<ast::ConstRefIndex, unresolved::ConstRef>,
    pub const_decls: Vec<unresolved::ConstDecl>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, FancySentence>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, unresolved::SentenceRef>,
}

#[derive(Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct FancySentence {
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

    fn visit_file(&mut self, file: parser::File) -> unresolved::ModuleIndex {
        self.visit_module(file.namespace)
    }

    fn visit_module(&mut self, namespace: parser::Namespace) -> unresolved::ModuleIndex {
        let mut module = unresolved::Module::default();
        for decl in namespace.decls {
            match decl {
                parser::Decl::ModuleDecl(module_decl) => {
                    module.submodules.push(unresolved::ModuleDecl {
                        name: module_decl.name,
                        module: self.visit_module(module_decl.namespace),
                    });
                }
                parser::Decl::ConstDecl(const_decl) => {
                    module.const_decls.push(unresolved::ConstDecl {
                        name: const_decl.name,
                        value: self.visit_const_expr(const_decl.value),
                    });
                }
                parser::Decl::SentenceDecl(sentence_decl) => {
                    module.sentence_decls.push(unresolved::SentenceDecl {
                        name: sentence_decl.name,
                        sentence: self.visit_sentence_def(sentence_decl.sentence),
                    });
                }
                parser::Decl::SymbolDecl(symbol_decl) => {
                    let symbol_def_index = self
                        .res
                        .symbol_defs
                        .push_and_get_key(ast::SymbolDef(symbol_decl.name.0));
                    let const_ref_index =
                        self.res
                            .const_refs
                            .push_and_get_key(unresolved::ConstRef::Inline(
                                bytecode::PrimitiveValue::Symbol(symbol_def_index),
                            ));
                    module.const_decls.push(unresolved::ConstDecl {
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
                unresolved::ConstRef::Inline(literal.into_value(self.sources))
            }
            parser::ConstExpr::Path(path) => unresolved::ConstRef::Path(convert_path(path)),
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
        let result: unresolved::ConstRef = match word_arg {
            parser::WordArg::Literal(literal) => {
                unresolved::ConstRef::Inline(literal.into_value(self.sources))
            }
            parser::WordArg::Path(path) => unresolved::ConstRef::Path(convert_path(path)),
            _ => panic!("expected literal or path: {:?}", word_arg),
        };
        self.res.const_refs.push_and_get_key(result)
    }

    fn visit_word_arg_sentence(&mut self, word_arg: parser::WordArg) -> ast::SentenceRefIndex {
        let result: unresolved::SentenceRef = match word_arg {
            parser::WordArg::Sentence(sentence) => {
                unresolved::SentenceRef::Inline(self.visit_sentence_def(sentence))
            }
            parser::WordArg::Path(path) => unresolved::SentenceRef::Path(convert_path(path)),
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

struct Desugarer<'a> {
    sources: &'a source::Sources,
}

impl<'a> Desugarer<'a> {
    fn desugar(self, mut library: Library) -> Result<unresolved::Library, anyhow::Error> {
        let sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef> = library
            .sentence_defs
            .into_iter()
            .map(|sentence| {
                self.compile_sentence_def(
                    &mut library.symbol_defs,
                    &mut library.const_refs,
                    sentence,
                )
            })
            .collect();
        Ok(unresolved::Library {
            root_module: library.root_module,
            modules: library.modules,
            const_refs: library.const_refs,
            symbol_defs: library.symbol_defs,
            sentence_defs,
            sentence_refs: library.sentence_refs,
        })
    }

    fn compile_sentence_def(
        &self,
        symbol_defs: &mut TiVec<bytecode::SymbolIndex, ast::SymbolDef>,
        const_refs: &mut TiVec<ast::ConstRefIndex, unresolved::ConstRef>,
        sentence: FancySentence,
    ) -> ast::SentenceDef {
        let mut words: Vec<ast::Word> = Vec::new();
        let mut locals: BTreeMap<&str, bytecode::SymbolIndex> = BTreeMap::new();
        for word in sentence.words.into_iter() {
            let inners: Vec<ast::WordInner> = match word.inner {
                FancyWordInner::Tuple(size) => {
                    let mut result = vec![ast::WordInner::StackOperation(
                        ast::StackOperation::Untuple(2),
                    )];
                    // Stack: {} (..., x, y)
                    for _ in 0..size {
                        result.push(ast::WordInner::StackOperation(
                            ast::StackOperation::Builtin(bytecode::Builtin::TuplePop),
                        ));
                        result.push(ast::WordInner::StackOperation(ast::StackOperation::Move(1)));
                    }
                    // Stack: {} y x (...)
                    // Notice: it's backwards. Reverse the order of the elements.
                    for i in 0..size {
                        result.push(ast::WordInner::StackOperation(ast::StackOperation::Move(
                            i + 1,
                        )));
                    }
                    // Stack: {} (...) x y
                    result.push(ast::WordInner::StackOperation(ast::StackOperation::Tuple(
                        size,
                    )));
                    result.push(ast::WordInner::StackOperation(
                        ast::StackOperation::Builtin(bytecode::Builtin::TuplePush),
                    ));
                    result.push(ast::WordInner::StackOperation(ast::StackOperation::Tuple(
                        2,
                    )));
                    result
                }
                FancyWordInner::Word(inner) => {
                    vec![inner]
                }
                FancyWordInner::Local(identifier) => {
                    locals.insert(
                        identifier.0.as_str(self.sources),
                        symbol_defs.push_and_get_key(ast::SymbolDef(identifier.0)),
                    );
                    vec![]
                }
                FancyWordInner::BindVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(self.sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());

                    let const_ref = const_refs.push_and_get_key(unresolved::ConstRef::Inline(
                        bytecode::PrimitiveValue::Symbol(*symbol),
                    ));

                    Self::bind_var(const_ref)
                }
                FancyWordInner::CopyVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(self.sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());

                    let const_ref1 = const_refs.push_and_get_key(unresolved::ConstRef::Inline(
                        bytecode::PrimitiveValue::Symbol(*symbol),
                    ));
                    let const_ref2 = const_refs.push_and_get_key(unresolved::ConstRef::Inline(
                        bytecode::PrimitiveValue::Symbol(*symbol),
                    ));

                    vec![
                        // Stack: ({'x: x}, (...))
                        ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
                        ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Push(const_ref1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                            bytecode::Builtin::MapGet,
                        )),
                        ast::WordInner::StackOperation(ast::StackOperation::Copy(0)),
                        // Stack: (...) {} x x
                        ast::WordInner::StackOperation(ast::StackOperation::Move(3)),
                        ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                            bytecode::Builtin::TuplePush,
                        )),
                        // Stack: {} x (..., x)
                        ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
                        ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
                        ast::WordInner::StackOperation(ast::StackOperation::Push(const_ref2)),
                        ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                            bytecode::Builtin::MapSet,
                        )),
                        // Stack: (..., x) {'x: x}
                        ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
                        ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
                    ]
                }
                FancyWordInner::MoveVar(identifier) => {
                    let symbol = locals
                        .get(identifier.0.as_str(self.sources))
                        .expect(format!("local not found: {:?}", identifier).as_str());

                    let const_ref = const_refs.push_and_get_key(unresolved::ConstRef::Inline(
                        bytecode::PrimitiveValue::Symbol(*symbol),
                    ));

                    Self::move_var(const_ref)
                }
                FancyWordInner::FnInit => {
                    vec![
                        ast::WordInner::StackOperation(ast::StackOperation::Tuple(1)),
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
            // Stack: ({}, (..., x))
            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                bytecode::Builtin::TuplePop,
            )),
            // Stack: {} (...) x
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
            // Stack: ({'x: x}, ...)
            ast::WordInner::StackOperation(ast::StackOperation::Untuple(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Push(local)),
            ast::WordInner::StackOperation(ast::StackOperation::Builtin(bytecode::Builtin::MapGet)),
            // Stack: (...) {} x
            ast::WordInner::StackOperation(ast::StackOperation::Move(2)),
            ast::WordInner::StackOperation(ast::StackOperation::Move(1)),
            ast::WordInner::StackOperation(ast::StackOperation::Builtin(
                bytecode::Builtin::TuplePush,
            )),
            // Stack: {} (..., x)
            ast::WordInner::StackOperation(ast::StackOperation::Tuple(2)),
        ]
    }
}

impl Library {
    pub fn from_parsed(sources: &source::Sources, parsed_library: parser::Library) -> Self {
        let mut builder = Builder {
            sources,
            res: Library {
                root_module: unresolved::ModuleIndex::from(0),
                modules: TiVec::new(),
                symbol_defs: TiVec::new(),
                const_refs: TiVec::new(),
                const_decls: vec![],
                sentence_defs: TiVec::new(),
                sentence_refs: TiVec::new(),
            },
        };

        let mut file_modules: Vec<(ast::Path, unresolved::ModuleIndex)> = vec![];
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
                    parent.submodules.push(unresolved::ModuleDecl {
                        name: parser::Identifier(child_mod_path.0.last().unwrap().clone()),
                        module: *child_index,
                    });
                }
            }
        }
        builder.build()
    }

    pub fn desugar(self, sources: &source::Sources) -> Result<unresolved::Library, anyhow::Error> {
        let desugarer = Desugarer { sources };
        desugarer.desugar(self)
    }
}

fn convert_path(path: parser::Path) -> unresolved::Path {
    unresolved::Path {
        inner: ast::Path(path.segments.iter().map(|i| i.0).collect()),
        relative: path.relative,
    }
}
