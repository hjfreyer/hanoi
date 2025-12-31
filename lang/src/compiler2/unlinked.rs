use std::collections::BTreeMap;

use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    bytecode,
    compiler2::{ast, linked},
    parser::{self, source},
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ConstDefIndex(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstName {
    pub name: ast::Path,
    pub value: ast::ConstRefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstRef {
    Inline(bytecode::PrimitiveValue),
    Path(ast::Path),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SentenceRef {
    Inline(ast::SentenceDefIndex),
    Path(ast::Path),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SentenceName {
    pub name: ast::Path,
    pub value: ast::SentenceDefIndex,
}

#[derive(Debug, Clone, Default)]
pub struct Library {
    // pub symbol_defs: TiVec<bytecode::SymbolIndex, String>,
    pub const_refs: TiVec<ast::ConstRefIndex, ConstRef>,
    pub const_names: Vec<ConstName>,

    pub variable_refs: TiVec<ast::VariableRefIndex, usize>,

    pub sentence_defs: TiVec<ast::SentenceDefIndex, ast::SentenceDef>,
    pub sentence_refs: TiVec<ast::SentenceRefIndex, SentenceRef>,
    pub sentence_names: Vec<SentenceName>,
    pub exports: BTreeMap<String, ast::PathIndex>,
}

struct Builder<'a> {
    sources: &'a source::Sources,
    res: Library,
}

impl<'a> Builder<'a> {
    fn new(sources: &'a source::Sources) -> Self {
        Self {
            sources,
            res: Library::default(),
        }
    }

    fn build(self) -> Library {
        self.res
    }

    fn visit_file(&mut self, file: parser::File) {
        for decl in file.namespace.decls {
            let module_path = ast::Path(file.mod_path.clone());
            match decl {
                parser::Decl::ConstDecl(const_decl) => {
                    self.visit_const_decl(module_path, const_decl);
                }
                parser::Decl::SentenceDecl(sentence_decl) => {
                    self.visit_sentence_decl(module_path, sentence_decl);
                }
            }
        }
    }

    fn visit_const_decl(&mut self, module_path: ast::Path, const_decl: parser::ConstDecl) {
        let name = module_path.join(const_decl.name.0);
        let const_name = ConstName {
            name,
            value: self.visit_const_expr(const_decl.value),
        };
        self.res.const_names.push(const_name);
    }

    fn visit_const_expr(&mut self, const_expr: parser::ConstExpr) -> ast::ConstRefIndex {
        self.res.const_refs.push_and_get_key(match const_expr {
            parser::ConstExpr::Literal(literal) => {
                ConstRef::Inline(literal.into_value(self.sources))
            }
            parser::ConstExpr::Path(path) => {
                ConstRef::Path(ast::Path(path.segments.iter().map(|i| i.0).collect()))
            }
        })
    }

    fn visit_sentence_decl(&mut self, module_path: ast::Path, sentence_decl: parser::SentenceDecl) {
        let name = module_path.join(sentence_decl.name.0);
        let sentence_name = SentenceName {
            name,
            value: self.visit_sentence_def(sentence_decl.sentence),
        };
        self.res.sentence_names.push(sentence_name);
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
                if let Some(builtin) = bytecode::Builtin::ALL.iter().find(|b| b.name() == word.operator.0.as_str(self.sources)) {
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
        let result: ConstRef = match word_arg {
            parser::WordArg::Literal(literal) => ConstRef::Inline(literal.into_value(self.sources)),
            parser::WordArg::Path(path) => ConstRef::Path(convert_path(path)),
            _ => panic!("expected literal or path: {:?}", word_arg),
        };
        self.res.const_refs.push_and_get_key(result)
    }

    fn visit_word_arg_sentence(&mut self, word_arg: parser::WordArg) -> ast::SentenceRefIndex {
        let result: SentenceRef = match word_arg {
            parser::WordArg::Sentence(sentence) => {
                SentenceRef::Inline(self.visit_sentence_def(sentence))
            }
            parser::WordArg::Path(path) => SentenceRef::Path(convert_path(path)),
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

fn convert_path(path: parser::Path) -> ast::Path {
    ast::Path(path.segments.iter().map(|i| i.0).collect())
}

impl Library {
    pub fn from_parsed(sources: &source::Sources, parsed_library: parser::Library) -> Self {
        let mut builder = Builder::new(sources);
        for file in parsed_library.files {
            builder.visit_file(file);
        }
        builder.build()
    }

    pub fn link(self, sources: &source::Sources) -> Result<linked::Library, anyhow::Error> {
        let const_map: BTreeMap<Vec<&str>, ast::ConstRefIndex> = self
            .const_names
            .into_iter()
            .map(|c| (c.name.as_strs(sources), c.value))
            .collect();

        fn deref_const_ref(
            const_ref_index: ast::ConstRefIndex,
            sources: &source::Sources,
            const_refs: &TiVec<ast::ConstRefIndex, ConstRef>,
            const_map: &BTreeMap<Vec<&str>, ast::ConstRefIndex>,
        ) -> bytecode::PrimitiveValue {
            match &const_refs[const_ref_index] {
                ConstRef::Inline(value) => *value,
                ConstRef::Path(path) => deref_const_ref(
                    *const_map.get(path.as_strs(sources).as_slice()).unwrap(),
                    sources,
                    const_refs,
                    const_map,
                ),
            }
        }

        let sentence_map: BTreeMap<Vec<&str>, ast::SentenceDefIndex> = self
            .sentence_names
            .into_iter()
            .map(|s| (s.name.as_strs(sources), s.value))
            .collect();
        let sentence_refs: TiVec<ast::SentenceRefIndex, ast::SentenceDefIndex> = self
            .sentence_refs
            .into_iter()
            .map(|s| match s {
                SentenceRef::Inline(sentence_def_index) => sentence_def_index,
                SentenceRef::Path(path) => {
                    *sentence_map.get(path.as_strs(sources).as_slice()).unwrap()
                }
            })
            .collect();

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
