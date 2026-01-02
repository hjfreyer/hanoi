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

impl<C> DebugWith<C> for ConstDecl
where
    parser::Identifier: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConstDecl")
            .field("name", &UseDebugWith(&self.name, c))
            .field("value", &self.value)
            .finish()
    }
}

#[derive(Debug, Clone, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct SentenceDecl {
    pub name: parser::Identifier,
    pub sentence: ast::SentenceDefIndex,
}

impl<C> DebugWith<C> for SentenceDecl
where
    parser::Identifier: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SentenceDecl")
            .field("name", &UseDebugWith(&self.name, c))
            .field("sentence", &self.sentence)
            .finish()
    }
}

#[derive(Debug, Clone, Default, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Module {
    pub submodules: Vec<ModuleDecl>,
    pub const_decls: Vec<ConstDecl>,
    pub sentence_decls: Vec<SentenceDecl>,
}

impl<C> DebugWith<C> for Module
where
    ConstDecl: DebugWith<C>,
    SentenceDecl: DebugWith<C>,
    ModuleDecl: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("submodules", &UseDebugWith(&self.submodules, c))
            .field("const_decls", &UseDebugWith(&self.const_decls, c))
            .field("sentence_decls", &UseDebugWith(&self.sentence_decls, c))
            .finish()
    }
}

impl<C> DebugWith<C> for ModuleDecl
where
    parser::Identifier: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleDecl")
            .field("name", &UseDebugWith(&self.name, c))
            .field("module", &self.module)
            .finish()
    }
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
    // pub symbol_defs: TiVec<bytecode::SymbolIndex, String>,
    pub const_refs: TiVec<ast::ConstRefIndex, ast::ConstRef>,
    pub const_decls: Vec<ConstDecl>,

    pub variable_refs: TiVec<ast::VariableRefIndex, usize>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, unlinked::SentenceRef>,
}

impl DebugWith<source::Sources> for Library {
    fn debug_with(
        &self,
        sources: &source::Sources,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        f.debug_struct("Library")
            .field("root_module", &self.root_module)
            .field(
                "modules",
                &UseDebugWith(
                    &self.modules,
                    &LibraryView {
                        sources,
                        library: self,
                    },
                ),
            )
            .field(
                "const_refs",
                &UseDebugWith(
                    &self.const_refs,
                    &LibraryView {
                        sources,
                        library: self,
                    },
                ),
            )
            .field(
                "const_decls",
                &UseDebugWith(
                    &self.const_decls,
                    &LibraryView {
                        sources,
                        library: self,
                    },
                ),
            )
            .field("variable_refs", &self.variable_refs)
            .field(
                "sentence_defs",
                &UseDebugWith(
                    &self.sentence_defs,
                    &LibraryView {
                        sources,
                        library: self,
                    },
                ),
            )
            .field(
                "sentence_refs",
                &UseDebugWith(
                    &self.sentence_refs,
                    &LibraryView {
                        sources,
                        library: self,
                    },
                ),
            )
            .finish()
    }
}

impl DebugWith<LibraryView<'_>> for source::Span {
    fn debug_with(
        &self,
        library_view: &LibraryView<'_>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        f.write_str(self.as_str(library_view.sources))
    }
}

#[derive(Copy, Clone)]
struct LibraryView<'a> {
    sources: &'a source::Sources,
    library: &'a Library,
}

pub trait DebugWith<T> {
    fn debug_with(&self, t: &T, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

impl<'a, K, V, C> DebugWith<C> for TiVec<K, V>
where
    K: From<usize> + std::fmt::Debug,
    V: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(
                self.iter_enumerated()
                    .map(|(k, v)| (k, UseDebugWith(v, c)))
                    .collect_vec(),
            )
            .finish()
    }
}
impl<'a, V, C> DebugWith<C> for Vec<V>
where
    V: DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter().map(|v| UseDebugWith(v, c)))
            .finish()
    }
}

pub struct UseDebugWith<'a, T, C>(pub &'a T, pub &'a C);

impl<'a, T, C> std::fmt::Debug for UseDebugWith<'a, T, C>
where
    T: DebugWith<C>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.debug_with(self.1, f)
    }
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
            .map(|w| self.visit_word(w))
            .collect();
        self.res
            .sentence_defs
            .push_and_get_key(ast::SentenceDef { words })
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

    fn visit_word_arg_variable(&mut self, word_arg: parser::WordArg) -> ast::VariableRefIndex {
        let result: usize = match word_arg {
            parser::WordArg::Literal(literal) => match literal.into_value(self.sources) {
                bytecode::PrimitiveValue::Usize(value) => value,
                _ => panic!("expected usize: {:?}", literal),
            },
            _ => panic!("expected variable: {:?}", word_arg),
        };
        self.res.variable_refs.push_and_get_key(result)
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
                const_refs: TiVec::new(),
                const_decls: vec![],
                variable_refs: TiVec::new(),
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

    pub fn resolve(self, sources: &source::Sources) -> Result<unlinked::Library, anyhow::Error> {
        let const_decls = self.get_const_decls(sources, self.root_module, ast::Path(vec![]));
        let sentence_decls = self.get_sentence_decls(sources, self.root_module, ast::Path(vec![]));
        Ok(unlinked::Library {
            const_refs: self.const_refs,
            const_decls,
            variable_refs: self.variable_refs,
            sentence_defs: self.sentence_defs,
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
}

fn convert_path(path: parser::Path) -> ast::Path {
    ast::Path(path.segments.iter().map(|i| i.0).collect())
}
