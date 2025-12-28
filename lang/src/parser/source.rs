use std::{fmt::Display, path::PathBuf};

use derive_more::derive::{From, Into};
use thiserror::Error;
use typed_index_collections::TiVec;

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GeneratedIndex(usize);

pub struct Loader {
    pub base_dir: PathBuf,
}

#[derive(Debug, Error)]
pub struct LoadError {
    pub path: PathBuf,
    pub error: LoadErrorInner,
}

impl Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "In file {}, error: {}", self.path.display(), self.error)
    }
}

#[derive(Debug, Error)]

pub enum LoadErrorInner {
    #[error("error reading file")]
    IO(#[from] anyhow::Error),
    #[error("duplicate path")]
    DuplicatePath,
    #[error("file not found")]
    FileNotFound,
}

impl Loader {
    pub fn load(&self, path: PathBuf, sources: &mut Sources) -> Result<FileIndex, LoadError> {
        if sources.files.iter().any(|f| f.path == path) {
            return Err(LoadError {
                path,
                error: LoadErrorInner::DuplicatePath,
            });
        }
        // Try to load mod.han.
        let path1 = self.base_dir.join(&path).join("mod.han");
        if path1.exists() {
            return match std::fs::read_to_string(&path1) {
                Ok(contents) => Ok(sources.files.push_and_get_key(File {
                    path,
                    source: contents,
                })),
                Err(e) => Err(LoadError {
                    path,
                    error: LoadErrorInner::IO(e.into()),
                }),
            };
        }

        // Try setting the extension.
        let path2 = self.base_dir.join(&path).with_extension("han");
        if path2.exists() {
            return match std::fs::read_to_string(&path2) {
                Ok(contents) => Ok(sources.files.push_and_get_key(File {
                    path,
                    source: contents,
                })),
                Err(e) => Err(LoadError {
                    path,
                    error: LoadErrorInner::IO(e.into()),
                }),
            };
        }

        Err(LoadError {
            path,
            error: LoadErrorInner::FileNotFound,
        })
    }
}

#[derive(Default, Debug)]
pub struct Sources {
    pub files: TiVec<FileIndex, File>,
}

impl Sources {}

#[derive(Debug)]
pub struct File {
    pub path: PathBuf,
    pub source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub file_idx: FileIndex,
    pub start: usize,
    pub end: usize,
}

impl Span {
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

    pub fn as_pest(self, sources: &Sources) -> pest::Span<'_> {
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
