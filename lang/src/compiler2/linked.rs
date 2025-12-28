use std::collections::BTreeMap;

use typed_index_collections::TiVec;

use crate::{bytecode, compiler2::ast};

#[derive(Debug, Clone)]
pub struct Library {
    pub symbol_defs: TiVec<bytecode::SymbolIndex, String>,
    pub const_refs: TiVec<ast::ConstRefIndex, bytecode::PrimitiveValue>,
    pub variable_refs: TiVec<ast::VariableRefIndex, usize>,
    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, ast::SentenceDefIndex>,
    pub exports: BTreeMap<String, ast::SentenceDefIndex>,
}

impl Library {
    pub fn into_bytecode(self) -> bytecode::Library {
        bytecode::Library {
            symbols: self.symbol_defs,
            sentences: self
                .sentence_defs
                .into_iter()
                .map(|sentence_def| bytecode::Sentence {
                    words: sentence_def
                        .words
                        .into_iter()
                        .map(|word| match word {
                            ast::Word::StackOperation(stack_operation) => {
                                bytecode::Word::StackOperation(match stack_operation {
                                    ast::StackOperation::Push(const_ref_index) => {
                                        bytecode::StackOperation::Push(
                                            self.const_refs.get(const_ref_index).unwrap().clone(),
                                        )
                                    }
                                    ast::StackOperation::Copy(variable_ref_index) => {
                                        bytecode::StackOperation::Copy(
                                            *self.variable_refs.get(variable_ref_index).unwrap(),
                                        )
                                    }
                                    ast::StackOperation::Move(variable_ref_index) => {
                                        bytecode::StackOperation::Move(
                                            *self.variable_refs.get(variable_ref_index).unwrap(),
                                        )
                                    }
                                    ast::StackOperation::Drop(variable_ref_index) => {
                                        bytecode::StackOperation::Drop(
                                            *self.variable_refs.get(variable_ref_index).unwrap(),
                                        )
                                    }
                                    ast::StackOperation::Builtin(builtin) => {
                                        bytecode::StackOperation::Builtin(builtin)
                                    }
                                    ast::StackOperation::Tuple(size) => {
                                        bytecode::StackOperation::Tuple(size)
                                    }
                                    ast::StackOperation::Untuple(size) => {
                                        bytecode::StackOperation::Untuple(size)
                                    }
                                })
                            }
                            ast::Word::Call(sentence_ref_index) => {
                                bytecode::Word::Call(bytecode::SentenceIndex::from(usize::from(
                                    *self.sentence_refs.get(sentence_ref_index).unwrap(),
                                )))
                            }
                            ast::Word::Branch(true_case, false_case) => bytecode::Word::Branch(
                                bytecode::SentenceIndex::from(usize::from(
                                    *self.sentence_refs.get(true_case).unwrap(),
                                )),
                                bytecode::SentenceIndex::from(usize::from(
                                    *self.sentence_refs.get(false_case).unwrap(),
                                )),
                            ),
                            ast::Word::JumpTable(jump_table) => bytecode::Word::JumpTable(
                                jump_table
                                    .into_iter()
                                    .map(|sentence_ref_index| {
                                        bytecode::SentenceIndex::from(usize::from(
                                            *self.sentence_refs.get(sentence_ref_index).unwrap(),
                                        ))
                                    })
                                    .collect(),
                            ),
                        })
                        .collect(),
                })
                .collect(),
            exports: self
                .exports
                .into_iter()
                .map(|(name, sentence_def_index)| {
                    (
                        name,
                        bytecode::SentenceIndex::from(usize::from(sentence_def_index)),
                    )
                })
                .collect(),
        }
    }
}
