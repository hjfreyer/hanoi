use std::{fmt::Display, path::PathBuf};

use derive_more::derive::{From, Into};
use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{
    ast,
    compiler::{Name, QualifiedName},
    flat::{LoadError, LoadErrorInner},
};

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileIndex(usize);

#[derive(From, Into, Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GeneratedIndex(usize);

pub struct Loader {
    pub base_dir: PathBuf,
}

impl Loader {
    pub fn load(
        &self,
        mod_name: QualifiedName,
        sources: &mut Sources,
    ) -> Result<FileIndex, crate::flat::LoadError> {
        let path = if mod_name.0.is_empty() {
            "mod.han".to_owned()
        } else {
            format!(
                "{}.han",
                mod_name
                    .0
                    .iter()
                    .map(|name| name.as_str(sources).unwrap())
                    .join("/")
            )
        };
        let path = path.parse().unwrap();

        if sources.files.iter().any(|f| f.mod_name == mod_name) {
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
            mod_name,
            source: contents,
        }))
    }
}

#[derive(Default, Debug)]
pub struct Sources {
    pub files: TiVec<FileIndex, File>,
}

impl Sources {
    pub fn fully_load(loader: &Loader) -> Result<Self, crate::flat::LoadError> {
        let mut sources = Self::default();
        let mut queue = vec![QualifiedName(vec![])];

        while let Some(mod_name) = queue.pop() {
            let file_idx = loader.load(mod_name.clone(), &mut sources)?;
            let path = sources.files[file_idx].path.clone();

            let parsed =
                ast::File::from_source(&sources.files.last().unwrap().source).map_err(|e| {
                    LoadError {
                        path,
                        error: LoadErrorInner::Parse(e),
                    }
                })?;

            for import in parsed.imports {
                queue.push(mod_name.append(Name::User(import.span(file_idx))));
            }
        }

        Ok(sources)
    }
}

#[derive(Debug)]
pub struct File {
    pub path: PathBuf,
    pub mod_name: QualifiedName,
    pub source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
