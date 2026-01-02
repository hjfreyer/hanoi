use std::collections::BTreeMap;

use anyhow::Context;
use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    bytecode,
    compiler2::{ast, linked},
    parser::source,
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ConstDefIndex(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDecl {
    pub name: ast::Path,
    pub value: ast::ConstRefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum SentenceRef {
    Inline(ast::SentenceDefIndex),
    Path(ast::Path),
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SentenceDecl {
    pub name: ast::Path,
    pub value: ast::SentenceDefIndex,
}


#[derive(Clone, Default)]
pub struct Library {
    // pub symbol_defs: TiVec<bytecode::SymbolIndex, String>,
    pub const_refs: TiVec<ast::ConstRefIndex, ast::ConstRef>,
    pub const_decls: Vec<ConstDecl>,

    pub variable_refs: TiVec<ast::VariableRefIndex, usize>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, SentenceRef>,
    pub sentence_decls: Vec<SentenceDecl>,
}

#[derive(Copy, Clone)]
struct LibraryView<'a> {
    sources: &'a source::Sources,
    library: &'a Library,
}


impl Library {
    pub fn link(self, sources: &source::Sources) -> Result<linked::Library, anyhow::Error> {
        let const_map: BTreeMap<Vec<&str>, ast::ConstRefIndex> = self
            .const_decls
            .into_iter()
            .map(|c| (c.name.as_strs(sources), c.value))
            .collect();

        fn deref_const_ref(
            const_ref_index: ast::ConstRefIndex,
            sources: &source::Sources,
            const_refs: &TiVec<ast::ConstRefIndex, ast::ConstRef>,
            const_map: &BTreeMap<Vec<&str>, ast::ConstRefIndex>,
        ) -> bytecode::PrimitiveValue {
            match &const_refs[const_ref_index] {
                ast::ConstRef::Inline(value) => *value,
                ast::ConstRef::Path(path) => deref_const_ref(
                    *const_map.get(path.as_strs(sources).as_slice()).unwrap(),
                    sources,
                    const_refs,
                    const_map,
                ),
            }
        }

        let sentence_map: BTreeMap<Vec<&str>, ast::SentenceDefIndex> = self
            .sentence_decls
            .into_iter()
            .map(|s| (s.name.as_strs(sources), s.value))
            .collect();
        let sentence_refs: Result<
            TiVec<ast::SentenceRefIndex, ast::SentenceDefIndex>,
            anyhow::Error,
        > = self
            .sentence_refs
            .into_iter()
            .map(|s| match s {
                SentenceRef::Inline(sentence_def_index) => Ok(sentence_def_index),
                SentenceRef::Path(path) => sentence_map
                    .get(path.as_strs(sources).as_slice())
                    .copied()
                    .with_context(|| {
                        format!("sentence not found: {:?}", path.as_strs(sources).join("::"))
                    }),
            })
            .collect();
        let sentence_refs = sentence_refs?;

        Ok(linked::Library {
            symbol_defs: Default::default(),
            const_refs: self
                .const_refs
                .keys()
                .map(|idx| deref_const_ref(idx, sources, &self.const_refs, &const_map))
                .collect(),
            variable_refs: self.variable_refs,
            sentence_defs: self.sentence_defs,
            sentence_refs,
            exports: Default::default(),
            // sentence_defs: self.sentence_defs,
            // sentence_refs: self
            //     .sentence_refs
            //     .clone()
            //     .into_iter()
            //     .map(|s| match s {
            //         SentenceRef::Inline(sentence_def_index) => sentence_def_index,
            //         SentenceRef::Path(path_index) => deref_sentence_ref(
            //             path_index,
            //             &self.sentence_refs,
            //             &sentence_map,
            //             &path_strs,
            //         ),
            //     })
            //     .collect(),
            // exports: self
            //     .exports
            //     .into_iter()
            //     .map(|(name, sentence_ref_index)| {
            //         (
            //             name,
            //             deref_sentence_ref(
            //                 sentence_ref_index,
            //                 &self.sentence_refs,
            //                 &sentence_map,
            //                 &path_strs,
            //             ),
            //         )
            //     })
            //     .collect(),
        })
    }
}
