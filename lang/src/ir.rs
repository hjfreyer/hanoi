use std::collections::BTreeMap;

use typed_index_collections::TiVec;

use crate::{
    flat::SentenceIndex,
    rawast::{self, Identifier, LabelCall, Word},
    source::{self, FileIndex, Span},
};

#[derive(Debug, Default)]
pub struct Crate {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

impl Crate {
    pub fn add_file(
        &mut self,
        name_prefix: QualifiedName,
        file_idx: FileIndex,
        file: rawast::File,
    ) {
        for decl in file.decl {
            let ctx = Context {
                file_idx,
                name_prefix: &name_prefix,
            };
            match decl {
                rawast::Decl::SentenceDecl(sentence_decl) => self.sentences.push(Sentence {
                    span: sentence_decl.span,
                    name: name_prefix.append(sentence_decl.label.0),
                    words: sentence_decl.sentence.words,
                }),
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct Context<'t> {
    file_idx: FileIndex,
    name_prefix: &'t QualifiedName,
}

pub struct WithContext<'t, T>(T, Context<'t>);

pub trait MakeWithContext<'t, T> {
    fn with_ctx(self, ctx: Context<'t>) -> WithContext<'t, T>;
}

impl<'t, T> MakeWithContext<'t, T> for T {
    fn with_ctx(self, ctx: Context<'t>) -> WithContext<'t, T> {
        WithContext(self, ctx)
    }
}

impl<'t, A, B> Into<Vec<B>> for WithContext<'t, Vec<A>>
where
    WithContext<'t, A>: Into<B>,
{
    fn into(self) -> Vec<B> {
        self.0
            .into_iter()
            .map(|a| a.with_ctx(self.1).into())
            .collect()
    }
}

// impl<'t> Into<Span> for WithContext<'t, pest::Span> {
//     fn into(self) -> Span {
//         Span::File(source::FileSpan {
//             file_idx: self.1.file_idx,
//             start: self.0.start(),
//             end: self.0.end(),
//         })
//     }
// }

#[derive(Debug, Clone)]
pub struct QualifiedName(pub Vec<Identifier>);

impl QualifiedName {
    pub fn join(&self, other: Self) -> Self {
        let mut res = self.clone();
        res.0.extend(other.0.into_iter());
        res
    }

    pub fn append(&self, label: Identifier) -> Self {
        let mut res = self.clone();
        res.0.push(label);
        res
    }

    pub fn to_strings(&self, sources: &source::Sources) -> Vec<String> {
        self.0
            .iter()
            .map(|s| s.0.as_str(sources).to_owned())
            .collect()
    }
}

#[derive(Debug)]
pub struct Sentence {
    pub span: Span,
    pub name: QualifiedName,
    pub words: Vec<Word>,
}
