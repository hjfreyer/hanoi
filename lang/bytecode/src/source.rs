//! Source files, byte spans, and the errors that point at them.
//!
//! A [`Span`] names a byte range inside one file, and a [`FileId`] identifies
//! that file. The path, the text, and the line table live once in the
//! [`SourceMap`]; a span carries only the 4-byte id. That keeps `Span` `Copy`
//! and cheap to hang off every token, and it means an error raised while
//! parsing an included file still renders against the right source without
//! anything having to thread a filename back up the call stack.
//!
//! Not every error has a span. Everything after parsing — desugaring, name
//! resolution, arity checking — reports against the module tree rather than
//! the token stream, so [`Error`] makes the span optional and `From<String>`
//! keeps those call sites unchanged.

use std::path::{Path, PathBuf};

/// Index into a [`SourceMap`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FileId(u32);

/// A byte range within a single file.
///
/// `u32` bounds a file at 4GiB and keeps the whole struct at 12 bytes; the
/// same trade rustc makes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: FileId, start: usize, end: usize) -> Self {
        Span {
            file,
            start: start as u32,
            end: end as u32,
        }
    }
}

struct SourceFile {
    /// What the `-->` line shows: a path for real files, or a bracketed
    /// placeholder like `<input>` for source that never came from disk.
    name: String,
    /// The file this came from, when it came from one at all.
    ///
    /// Kept beside `name` rather than parsed back out of it, because a display
    /// string is lossy for anything unusual and a path recovered by guesswork
    /// is a silent wrong answer rather than a loud one.
    path: Option<PathBuf>,
    text: String,
    /// Byte offset of each line's first character, always starting with 0.
    line_starts: Vec<u32>,
}

/// Every source text the compiler has read, and the only place their contents
/// live.
#[derive(Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        SourceMap::default()
    }

    /// Registers a source text under a display name and returns its id.
    pub fn add(&mut self, name: impl Into<String>, text: String) -> FileId {
        let mut line_starts = vec![0u32];
        line_starts.extend(
            text.bytes()
                .enumerate()
                .filter(|&(_, b)| b == b'\n')
                .map(|(i, _)| (i + 1) as u32),
        );
        self.files.push(SourceFile {
            name: name.into(),
            path: None,
            text,
            line_starts,
        });
        FileId((self.files.len() - 1) as u32)
    }

    /// Registers a file read from disk, displayed by its path.
    pub fn add_path(&mut self, path: &Path, text: String) -> FileId {
        let id = self.add(path.display().to_string(), text);
        self.files[id.0 as usize].path = Some(path.to_path_buf());
        id
    }

    pub fn name(&self, file: FileId) -> &str {
        &self.file(file).name
    }

    /// The file on disk this came from, if it came from one.
    ///
    /// `None` for source registered under a bracketed placeholder — a string
    /// assembled in a test, or a composer template. A caller that needs a
    /// sibling file has to say what it does about source that has no sibling
    /// to have.
    pub fn path(&self, file: FileId) -> Option<&Path> {
        self.file(file).path.as_deref()
    }

    pub fn text(&self, file: FileId) -> &str {
        &self.file(file).text
    }

    fn file(&self, file: FileId) -> &SourceFile {
        &self.files[file.0 as usize]
    }

    /// The file name and 1-based line and column a span begins at. Columns
    /// count characters, not bytes, so the caret lands correctly under
    /// non-ASCII text.
    pub fn locate(&self, span: Span) -> (&str, usize, usize) {
        let file = self.file(span.file);
        let line_idx = self.line_index(span);
        let line_start = file.line_starts[line_idx] as usize;
        let start = (span.start as usize).min(file.text.len());
        let column = file.text[line_start..start].chars().count() + 1;
        (&file.name, line_idx + 1, column)
    }

    fn line_index(&self, span: Span) -> usize {
        let file = self.file(span.file);
        // The first line start strictly greater than `start`, minus one.
        file.line_starts.partition_point(|&s| s <= span.start) - 1
    }

    /// Renders an error against its source, rustc style:
    ///
    /// ```text
    /// error: expected an instruction, found `{`
    ///  --> hana/main.hana:6:9
    ///    |
    ///  6 |     add {
    ///    |         ^
    /// ```
    pub fn render(&self, err: &Error) -> String {
        let Some(span) = err.span else {
            let mut out = format!("error: {}\n", err.message);
            if let Some(help) = &err.help {
                out.push_str(&format!("  = help: {}\n", help));
            }
            return out;
        };

        let file = self.file(span.file);
        let (name, line_no, column) = self.locate(span);
        let line_idx = self.line_index(span);
        let line_start = file.line_starts[line_idx] as usize;
        let line_end = file.text[line_start..]
            .find('\n')
            .map(|i| line_start + i)
            .unwrap_or(file.text.len());
        let line = &file.text[line_start..line_end];

        // A span running past the end of its first line is clipped, so the
        // caret never runs off into the gutter of the line below.
        let end = (span.end as usize).clamp(span.start as usize, line_end);
        let width = file.text[span.start as usize..end].chars().count().max(1);

        let gutter = line_no.to_string();
        let pad = " ".repeat(gutter.len());

        let mut out = format!("error: {}\n", err.message);
        out.push_str(&format!("{} --> {}:{}:{}\n", pad, name, line_no, column));
        out.push_str(&format!("{} |\n", pad));
        out.push_str(&format!("{} | {}\n", gutter, line));
        out.push_str(&format!(
            "{} | {}{}\n",
            pad,
            " ".repeat(column - 1),
            "^".repeat(width)
        ));
        if let Some(help) = &err.help {
            out.push_str(&format!("{} = help: {}\n", pad, help));
        }
        out
    }
}

/// A compiler error, with a span when one is known.
#[derive(Clone, Debug)]
pub struct Error {
    pub message: String,
    pub span: Option<Span>,
    pub help: Option<String>,
}

impl Error {
    /// An error that points at a range of source.
    pub fn at(message: impl Into<String>, span: Span) -> Self {
        Error {
            message: message.into(),
            span: Some(span),
            help: None,
        }
    }

    /// An error with no location, for phases that run after parsing.
    pub fn new(message: impl Into<String>) -> Self {
        Error {
            message: message.into(),
            span: None,
            help: None,
        }
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }
}

impl From<String> for Error {
    fn from(message: String) -> Self {
        Error::new(message)
    }
}

impl From<&str> for Error {
    fn from(message: &str) -> Self {
        Error::new(message)
    }
}

impl std::fmt::Display for Error {
    /// The message alone. Callers that hold the [`SourceMap`] should use
    /// [`SourceMap::render`] instead, which adds the location and the snippet.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(help) = &self.help {
            write!(f, "\nhelp: {}", help)?;
        }
        Ok(())
    }
}

impl std::error::Error for Error {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn locates_a_span_on_the_first_line() {
        let mut map = SourceMap::new();
        let f = map.add("<input>", "abc def\n".to_string());
        assert_eq!(map.locate(Span::new(f, 4, 7)), ("<input>", 1, 5));
    }

    #[test]
    fn locates_a_span_on_a_later_line() {
        let mut map = SourceMap::new();
        let f = map.add("<input>", "one\ntwo\nthree\n".to_string());
        let three = map.add("other", String::new());
        let _ = three;
        assert_eq!(map.locate(Span::new(f, 8, 13)), ("<input>", 3, 1));
    }

    #[test]
    fn locates_a_span_at_end_of_input() {
        let mut map = SourceMap::new();
        let text = "abc".to_string();
        let f = map.add("<input>", text);
        assert_eq!(map.locate(Span::new(f, 3, 3)), ("<input>", 1, 4));
    }

    #[test]
    fn columns_count_characters_not_bytes() {
        let mut map = SourceMap::new();
        // Two umlauts, two bytes each, so `x` sits at byte 7 but column 6.
        let text = "\"ää\" x\n".to_string();
        let f = map.add("<input>", text);
        let (_, line, column) = map.locate(Span::new(f, 7, 8));
        assert_eq!((line, column), (1, 6));
    }

    #[test]
    fn renders_with_a_caret_under_the_span() {
        let mut map = SourceMap::new();
        let f = map.add("main.hana", "sentence a {\n    add {\n}\n".to_string());
        let err = Error::at("expected an instruction, found `{`", Span::new(f, 21, 22));
        assert_eq!(
            map.render(&err),
            concat!(
                "error: expected an instruction, found `{`\n",
                "  --> main.hana:2:9\n",
                "  |\n",
                "2 |     add {\n",
                "  |         ^\n",
            )
        );
    }

    #[test]
    fn clips_a_caret_that_would_run_past_the_line() {
        let mut map = SourceMap::new();
        let f = map.add("main.hana", "abc\ndef\n".to_string());
        let rendered = map.render(&Error::at("spans two lines", Span::new(f, 1, 6)));
        assert!(rendered.contains("| abc\n"), "{}", rendered);
        assert!(rendered.contains("|  ^^\n"), "{}", rendered);
    }

    #[test]
    fn renders_help_text() {
        let mut map = SourceMap::new();
        let f = map.add("main.hana", "abc\n".to_string());
        let err = Error::at("nope", Span::new(f, 0, 3)).with_help("try `abd`");
        assert!(map.render(&err).ends_with("= help: try `abd`\n"));
    }

    #[test]
    fn renders_a_spanless_error() {
        let map = SourceMap::new();
        assert_eq!(
            map.render(&Error::new("no idea where")),
            "error: no idea where\n"
        );
    }
}
