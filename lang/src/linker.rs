use std::collections::{BTreeMap, VecDeque};

use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    compiler::{self, Name, NameRef, QualifiedName, QualifiedNameRef},
    flat::{self, SentenceIndex},
    source::{self, FileSpan, Span},
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("At {location}, {name:?} already defined")]
    AlreadyDefined {
        location: source::Location,
        name: String,
    },
    #[error("At {location}, {name} not found")]
    LabelNotFound {
        location: source::Location,
        name: String,
    },
    #[error("At {location}, unknown builtin: {name}")]
    UnknownBuiltin {
        location: source::Location,
        name: String,
    },

    #[error("At {location}, incorrect arguments for builtin {name}")]
    IncorrectBuiltinArguments {
        location: source::Location,
        name: String,
    },
    #[error("At {location}, unknown reference: {name}")]
    UnknownReference {
        location: source::Location,
        name: String,
    },
    #[error("At {location}, unused variable: {name}")]
    UnusedVariable {
        location: source::Location,
        name: String,
    },
    #[error("At {location}, branch contracts disagree")]
    BranchContractsDisagree { location: source::Location },
}

pub fn compile(sources: &source::Sources, ir: compiler::Crate) -> Result<flat::Library, Error> {
    let mut c = Compiler {
        sources,
        index: BTreeMap::new(),
        sentences: TiVec::new(),
    };

    c.compile(ir)
}

struct Compiler<'t> {
    sources: &'t source::Sources,
    index: BTreeMap<QualifiedNameRef<'t>, SentenceIndex>,
    sentences: TiVec<SentenceIndex, Option<flat::Sentence>>,
}

impl<'t> Compiler<'t> {
    fn compile(&mut self, ir: compiler::Crate) -> Result<flat::Library, Error> {
        let mut res = flat::Library::default();

        // let mut index: BTreeMap<QualifiedNameRef<'_>, SentenceIndex> = BTreeMap::new();

        // Build index of sentence names.
        for (sentence_idx, sentence) in ir.sentences.iter_enumerated() {
            let name = sentence.name.as_ref(self.sources);
            if self.index.insert(name.clone(), sentence_idx).is_some() {
                return Err(Error::AlreadyDefined {
                    location: sentence.span.location(self.sources),
                    name: name.to_string(),
                });
            }
            if let Some((n, compiler::NameRef::Generated(0))) = name.0.iter().collect_tuple() {
                if let Some(str) = n.as_str() {
                    res.exports.insert(str.to_owned(), sentence_idx);
                }
            }
        }

        self.sentences = ir.sentences.iter().map(|_| None).collect();

        let sentences: Result<Vec<flat::Sentence>, Error> = ir
            .sentences
            .into_iter()
            .map(|s| self.convert_sentence(s))
            .collect();

        res.sentences = sentences?.into_iter().collect();

        Ok(res)
    }

    fn convert_sentence(&mut self, sentence: compiler::Sentence) -> Result<flat::Sentence, Error> {
        // let mut b = SentenceBuilder::new(self.sources, &self.index, sentence.name);

        // for word in sentence.words {
        //     match word {
        //         // ir::Word::StackBindings(bindings) => {
        //         //     b.bindings(bindings);
        //         // }
        //         ir::Word::Builtin(builtin) => {
        //             b.ir_builtin(builtin)?;
        //         }
        //         ir::Word::Literal(literal) => b.literal(literal),
        //         // ir::Word::Tuple(tuple) => {
        //         //     let num_values = tuple.values.len();
        //         //     for v in tuple.values {
        //         //         b.label_call(v)?
        //         //     }
        //         //     b.tuple(tuple.span, num_values);
        //         // }
        //         // ValueExpression::Path(path) => Ok(b.path(path)),
        //         // ir::Word::Move(identifier) => b.mv(identifier)?,
        //         // ir::Word::Copy(identifier) => b.cp(identifier)?,
        //     }
        // }

        let words: Result<Vec<flat::Word>, Error> = sentence
            .words
            .into_iter()
            .map(|w| self.convert_word(w))
            .collect();

        Ok(flat::Sentence { words: words? })
        // Ok(b.build())
    }

    fn convert_word(&mut self, word: compiler::Word) -> Result<flat::Word, Error> {
        let inner = match word.inner {
            compiler::InnerWord::Push(value) => flat::InnerWord::Push(value),
            compiler::InnerWord::Builtin(builtin) => flat::InnerWord::Builtin(builtin),
            compiler::InnerWord::Copy(idx) => flat::InnerWord::Copy(idx),
            compiler::InnerWord::Drop(idx) => flat::InnerWord::Drop(idx),
            compiler::InnerWord::Move(idx) => flat::InnerWord::Move(idx),
            compiler::InnerWord::Tuple(idx) => flat::InnerWord::Tuple(idx),
            compiler::InnerWord::Untuple(idx) => flat::InnerWord::Untuple(idx),
            compiler::InnerWord::Call(qualified_name) => {
                let Some(idx) = self.index.get(&qualified_name.as_ref(&self.sources)) else {
                    return Err(Error::LabelNotFound {
                        location: word.span.location(self.sources),
                        name: qualified_name.as_ref(&self.sources).to_string(),
                    });
                };
                flat::InnerWord::Call(*idx)
            }
            compiler::InnerWord::Branch(true_case, false_case) => {
                let true_idx = self
                    .index
                    .get(&true_case.as_ref(&self.sources))
                    .expect("generated names should always exist");
                let false_idx = self
                    .index
                    .get(&false_case.as_ref(&self.sources))
                    .expect("generated names should always exist");
                flat::InnerWord::Branch(*true_idx, *false_idx)
            }
        };

        Ok(flat::Word {
            span: word.span,
            inner,
            names: Some(
                word.names
                    .into_iter()
                    .map(|s: Name| match s {
                        Name::User(file_span) => Some(file_span.as_str(self.sources).to_owned()),
                        Name::Generated(_) => None,
                    })
                    .collect(),
            ),
        })
    }
}
