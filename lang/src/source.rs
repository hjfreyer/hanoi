use std::{
    fmt::Display,
    path::{Path, PathBuf},
};

use derive_more::derive::{From, Into};
use typed_index_collections::TiVec;

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct FileIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GeneratedIndex(usize);

pub struct Loader {
    pub base_dir: PathBuf,
}

impl Loader {
    pub fn load(
        &self,
        path: PathBuf,
        sources: &mut Sources,
    ) -> Result<FileIndex, crate::flat::LoadError> {
        if sources.files.iter().any(|f| f.path == path) {
            return Err(crate::flat::LoadError {
                path,
                error: crate::flat::LoadErrorInner::DuplicatePath,
            });
        }

        let path = self.base_dir.join(&path);
        let contents = std::fs::read_to_string(&path).map_err(|e| crate::flat::LoadError {
            path: path.clone(),
            error: crate::flat::LoadErrorInner::IO(e.into()),
        })?;

        Ok(sources.files.push_and_get_key(File {
            path,
            source: contents,
        }))
    }
}

#[derive(Default, Debug)]
pub struct Sources {
    pub files: TiVec<FileIndex, File>,
    pub generated: TiVec<GeneratedIndex, String>,
}

impl Sources {
    // pub fn pest_span(&self, span: Span) -> pest::Span {
    //     pest::Span::new(self.files[span.file_idx].source.as_str(), span.start, span.end).unwrap()
    // }
}

#[derive(Default, Debug)]
pub struct File {
    pub path: PathBuf,
    pub source: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Span {
    Generated(GeneratedIndex),
    File(FileSpan),
}

impl Span {
    pub fn as_str(self, sources: &Sources) -> &str {
        match self {
            Self::File(file_span) => file_span.as_pest(sources).as_str(),
            Self::Generated(gen_idx) => &sources.generated[gen_idx],
        }
    }

    // pub fn as_pest(self, sources: &Sources) -> Option<pest::Span> {
    //     match self {
    //         Self::File { file_idx, start, end } => {
    //             Some(pest::Span::new(&sources.files[file_idx].source, start, end).unwrap())
    //         }
    //         Self::Generated(_) =>
    //             None
    //                 }
    // }

    pub fn location(self, sources: &Sources) -> Option<Location> {
        match self {
            Self::File(s) => Some(s.location(sources)),
            Self::Generated(_) => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct FileSpan {
    pub file_idx: FileIndex,
    pub start: usize,
    pub end: usize,
}

impl FileSpan {
    pub fn as_str(self, sources: &Sources) -> &str {
        self.as_pest(sources).as_str()
    }

    pub fn from_ast(file_idx: FileIndex, span: pest::Span) -> Self {
        Self {
            file_idx,
            start: span.start(),
            end: span.end(),
        }
    }

    pub fn as_pest(self, sources: &Sources) -> pest::Span {
        pest::Span::new(&sources.files[self.file_idx].source, self.start, self.end).unwrap()
    }

    pub fn location(self, sources: &Sources) -> Location {
        let (line, col) = self.as_pest(sources).start_pos().line_col();
        Location {
            file: sources.files[self.file_idx].path.clone(),
            line,
            col,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Location {
    pub file: PathBuf,
    pub line: usize,
    pub col: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{}:{}:{}",
            self.file.display(),
            self.line,
            self.col
        ))
    }
}
