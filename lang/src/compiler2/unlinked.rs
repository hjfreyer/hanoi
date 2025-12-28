use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
use typed_index_collections::TiVec;

use crate::{
    bytecode,
    compiler2::{ast, linked},
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ConstDefIndex(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstName {
    pub name: ast::PathIndex,
    pub value: ast::ConstRefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstRef {
    Inline(bytecode::PrimitiveValue),
    Path(ast::PathIndex),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SentenceRef {
    Inline(ast::SentenceDefIndex),
    Path(ast::PathIndex),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SentenceName {
    pub name: ast::PathIndex,
    pub value: ast::SentenceRefIndex,
}

#[derive(Debug, Clone)]
pub struct Library {
    pub identifiers: TiVec<ast::IdentifierIndex, String>,
    pub paths: TiVec<ast::PathIndex, ast::Path>,

    pub symbol_defs: TiVec<bytecode::SymbolIndex, String>,
    pub const_refs: TiVec<ast::ConstRefIndex, ConstRef>,
    pub const_names: Vec<ConstName>,

    pub variable_refs: TiVec<ast::VariableRefIndex, usize>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, SentenceRef>,
    pub sentence_names: Vec<SentenceName>,
    pub exports: BTreeMap<String, ast::PathIndex>,
}

// pub struct PathRef<'a>(&'a TiVec<IdentifierIndex, String>, );

impl Library {
    pub fn link(self) -> Result<linked::Library, anyhow::Error> {
        let path_strs: TiVec<ast::PathIndex, Vec<&str>> = self
            .paths
            .into_iter()
            .map(|p| -> Vec<&str> {
                p.0.iter()
                    .map(|i| self.identifiers.get(*i).unwrap().as_str())
                    .collect()
            })
            .collect();

        let const_map: BTreeMap<&[&str], ast::ConstRefIndex> = self
            .const_names
            .into_iter()
            .map(|c| (path_strs.get(c.name).unwrap().as_slice(), c.value))
            .collect();

        fn deref_const_ref(
            path_index: ast::PathIndex,
            const_refs: &TiVec<ast::ConstRefIndex, ConstRef>,
            const_map: &BTreeMap<&[&str], ast::ConstRefIndex>,
            path_strs: &TiVec<ast::PathIndex, Vec<&str>>,
        ) -> bytecode::PrimitiveValue {
            match const_refs
                .get(
                    *const_map
                        .get(path_strs.get(path_index).unwrap().as_slice())
                        .unwrap(),
                )
                .unwrap()
            {
                ConstRef::Inline(value) => *value,
                ConstRef::Path(path_index) => {
                    deref_const_ref(*path_index, const_refs, const_map, path_strs)
                }
            }
        }

        let sentence_map: BTreeMap<&[&str], ast::SentenceRefIndex> = self
            .sentence_names
            .into_iter()
            .map(|s| (path_strs.get(s.name).unwrap().as_slice(), s.value))
            .collect();
        fn deref_sentence_ref(
            path_index: ast::PathIndex,
            sentence_refs: &TiVec<ast::SentenceRefIndex, SentenceRef>,
            sentence_map: &BTreeMap<&[&str], ast::SentenceRefIndex>,
            path_strs: &TiVec<ast::PathIndex, Vec<&str>>,
        ) -> ast::SentenceDefIndex {
            match sentence_refs
                .get(
                    *sentence_map
                        .get(path_strs.get(path_index).unwrap().as_slice())
                        .unwrap(),
                )
                .unwrap()
            {
                SentenceRef::Inline(sentence_def_index) => *sentence_def_index,
                SentenceRef::Path(path_index) => {
                    deref_sentence_ref(*path_index, sentence_refs, sentence_map, path_strs)
                }
            }
        }

        Ok(linked::Library {
            symbol_defs: self.symbol_defs,
            const_refs: self
                .const_refs
                .clone()
                .into_iter()
                .map(|c| match c {
                    ConstRef::Inline(value) => value,
                    ConstRef::Path(path_index) => {
                        deref_const_ref(path_index, &self.const_refs, &const_map, &path_strs)
                    }
                })
                .collect(),
            variable_refs: self.variable_refs,
            sentence_defs: self.sentence_defs,
            sentence_refs: self
                .sentence_refs
                .clone()
                .into_iter()
                .map(|s| match s {
                    SentenceRef::Inline(sentence_def_index) => sentence_def_index,
                    SentenceRef::Path(path_index) => deref_sentence_ref(
                        path_index,
                        &self.sentence_refs,
                        &sentence_map,
                        &path_strs,
                    ),
                })
                .collect(),
            exports: self
                .exports
                .into_iter()
                .map(|(name, sentence_ref_index)| {
                    (
                        name,
                        deref_sentence_ref(
                            sentence_ref_index,
                            &self.sentence_refs,
                            &sentence_map,
                            &path_strs,
                        ),
                    )
                })
                .collect(),
        })
    }
}
