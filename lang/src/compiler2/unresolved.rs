use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
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
    pub const_refs: TiVec<ast::ConstRefIndex, ConstRef>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, SentenceRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum ConstRef {
    Inline(bytecode::PrimitiveValue),
    Path(Path),
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum SentenceRef {
    Inline(ast::SentenceDefIndex),
    Path(Path),
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Path {
    pub inner: ast::Path,
    pub relative: bool,
}

struct Resolver;

impl Resolver {
    fn resolve(self, library: Library) -> Result<unlinked::Library, anyhow::Error> {
        let mut const_ref_module_paths = BTreeMap::new();
        let mut sentence_ref_module_paths = BTreeMap::new();

        self.get_module_paths(
            library.root_module,
            ast::Path(vec![]),
            &library,
            &mut const_ref_module_paths,
            &mut sentence_ref_module_paths,
        );

        let const_decls = self.get_const_decls(library.root_module, ast::Path(vec![]), &library);
        let sentence_decls =
            self.get_sentence_decls(library.root_module, ast::Path(vec![]), &library);

        let const_refs = self.resolve_const_refs(library.const_refs, &const_ref_module_paths);
        let sentence_refs =
            self.resolve_sentence_refs(library.sentence_refs, &sentence_ref_module_paths);
        Ok(unlinked::Library {
            const_refs,
            const_decls,
            symbol_defs: library.symbol_defs,
            sentence_defs: library.sentence_defs,
            sentence_refs,
            sentence_decls,
        })
    }

    fn get_const_decls(
        &self,
        module_index: ModuleIndex,
        module_path: ast::Path,
        library: &Library,
    ) -> Vec<unlinked::ConstDecl> {
        let module = &library.modules[module_index];
        let mut result = Vec::new();
        for const_decl in module.const_decls.iter() {
            result.push(unlinked::ConstDecl {
                name: module_path.join(const_decl.name.0),
                value: const_decl.value,
            });
        }
        for submodule in module.submodules.iter() {
            result.extend(self.get_const_decls(
                submodule.module,
                module_path.join(submodule.name.0),
                library,
            ));
        }
        result
    }

    fn get_sentence_decls(
        &self,
        module_index: ModuleIndex,
        module_path: ast::Path,
        library: &Library,
    ) -> Vec<unlinked::SentenceDecl> {
        let module = &library.modules[module_index];
        let mut result = Vec::new();
        for sentence_decl in module.sentence_decls.iter() {
            result.push(unlinked::SentenceDecl {
                name: module_path.join(sentence_decl.name.0),
                value: sentence_decl.sentence,
            });
        }
        for submodule in module.submodules.iter() {
            result.extend(self.get_sentence_decls(
                submodule.module,
                module_path.join(submodule.name.0),
                library,
            ));
        }
        result
    }

    fn get_module_paths(
        &self,
        module_index: ModuleIndex,
        module_path: ast::Path,
        library: &Library,
        const_ref_module_paths: &mut BTreeMap<ast::ConstRefIndex, ast::Path>,
        sentence_ref_module_paths: &mut BTreeMap<ast::SentenceRefIndex, ast::Path>,
    ) {
        for submodule in library.modules[module_index].submodules.clone().iter() {
            self.get_module_paths(
                submodule.module,
                module_path.join(submodule.name.0),
                library,
                const_ref_module_paths,
                sentence_ref_module_paths,
            );
        }

        let module = &library.modules[module_index];
        for const_decl in module.const_decls.iter() {
            assert!(const_ref_module_paths
                .insert(const_decl.value, module_path.clone())
                .is_none());
        }
        for sentence_decl in module.sentence_decls.iter() {
            let sentence_def = &library.sentence_defs[sentence_decl.sentence];
            for word in sentence_def.words.iter() {
                match &word.inner {
                    ast::WordInner::Call(sentence_ref_index) => {
                        assert!(sentence_ref_module_paths
                            .insert(*sentence_ref_index, module_path.clone())
                            .is_none());
                    }
                    ast::WordInner::StackOperation(stack_operation) => match stack_operation {
                        ast::StackOperation::Push(const_ref_index) => {
                            if const_ref_module_paths
                                .insert(*const_ref_index, module_path.clone())
                                .is_some()
                            {
                                panic!("duplicate key: {:?}", library.const_refs[*const_ref_index]);
                            }
                        }
                        _ => {}
                    },
                    ast::WordInner::Branch(sentence_ref_index, sentence_ref_index1) => {
                        assert!(sentence_ref_module_paths
                            .insert(*sentence_ref_index, module_path.clone())
                            .is_none());
                        assert!(sentence_ref_module_paths
                            .insert(*sentence_ref_index1, module_path.clone())
                            .is_none());
                    }
                    ast::WordInner::JumpTable(items) => {
                        for item in items.iter() {
                            assert!(sentence_ref_module_paths
                                .insert(*item, module_path.clone())
                                .is_none());
                        }
                    }
                }
            }
        }
    }

    fn resolve_const_refs(
        &self,
        const_refs: TiVec<ast::ConstRefIndex, ConstRef>,
        const_ref_module_paths: &BTreeMap<ast::ConstRefIndex, ast::Path>,
    ) -> TiVec<ast::ConstRefIndex, ast::ConstRef> {
        const_refs
            .into_iter_enumerated()
            .map(|(index, const_ref)| match const_ref {
                ConstRef::Inline(value) => ast::ConstRef::Inline(value),
                ConstRef::Path(path) => {
                    if path.relative {
                        ast::ConstRef::Path(
                            const_ref_module_paths
                                .get(&index)
                                .unwrap()
                                .clone()
                                .join(path.inner),
                        )
                    } else {
                        ast::ConstRef::Path(path.inner)
                    }
                }
            })
            .collect()
    }

    fn resolve_sentence_refs(
        &self,
        sentence_refs: TiVec<ast::SentenceRefIndex, SentenceRef>,
        sentence_ref_module_paths: &BTreeMap<ast::SentenceRefIndex, ast::Path>,
    ) -> TiVec<ast::SentenceRefIndex, unlinked::SentenceRef> {
        sentence_refs
            .into_iter_enumerated()
            .map(|(index, sentence_ref)| match sentence_ref {
                SentenceRef::Inline(sentence_def_index) => {
                    unlinked::SentenceRef::Inline(sentence_def_index)
                }
                SentenceRef::Path(path) => {
                    if path.relative {
                        unlinked::SentenceRef::Path(
                            sentence_ref_module_paths
                                .get(&index)
                                .unwrap()
                                .clone()
                                .join(path.inner),
                        )
                    } else {
                        unlinked::SentenceRef::Path(path.inner)
                    }
                }
            })
            .collect()
    }
}

impl Library {
    pub fn resolve(self, _sources: &source::Sources) -> Result<unlinked::Library, anyhow::Error> {
        let resolver = Resolver;
        resolver.resolve(self)
    }
}
