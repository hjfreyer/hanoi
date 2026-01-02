use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::parser::source;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Span {
    pub file: usize,
    pub begin: Position,
    pub end: Position,
}

impl Span {
    pub fn from_source_span(sources: &source::Sources, span: source::Span) -> Self {
        Self {
            file: span.file_idx.into(),
            begin: Position {
                line: span.start_location(sources).line,
                col: span.start_location(sources).col,
            },
            end: Position {
                line: span.end_location(sources).line,
                col: span.end_location(sources).col,
            },
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Word {
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Sentence {
    pub words: Vec<Word>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Library {
    pub files: Vec<PathBuf>,
    pub sentences: Vec<Sentence>,
    pub symbols: Vec<Symbol>,
}
