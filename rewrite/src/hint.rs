//! Stepping stones: the `.hant` sibling file.
//!
//! A goal the rules cannot close on their own is bridged by seeding the
//! e-graph with an intermediate term — a **stepping stone** — that both sides
//! can reach. The stone is a program, so it is written as one, in a file
//! beside the `.hana` that states the identity:
//!
//! ```text
//! // identities.hant
//! hint identities::two_spellings_of_one_test via { drop 0 push true };
//! ```
//!
//! One entry per stone; an identity may have several, and an identity with
//! none just runs the default pipeline. An entry naming no stated identity is
//! an error — a renamed identity orphans its hints, and nothing else would
//! notice.
//!
//! The body is compiled by appending a scratch sentence to the corpus source,
//! so the whole parser and resolver are reused rather than imitated. The
//! scratch sentences live at the crate root, which is the one caveat: paths
//! in a hint body resolve from the root (`identities::helper`, or
//! `crate::...`), not from the module the identity was stated in.

use std::path::Path;

/// One parsed entry: which identity, and the stone's body text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hint {
    pub identity: String,
    pub body: String,
}

/// Parses a `.hant` file's text.
pub fn parse_hints(text: &str) -> Result<Vec<Hint>, String> {
    let mut hints = Vec::new();
    let mut rest = strip_comments(text);
    loop {
        rest = rest.trim_start().to_string();
        if rest.is_empty() {
            return Ok(hints);
        }
        let after_kw = rest
            .strip_prefix("hint")
            .ok_or_else(|| format!("expected `hint`, found: {}", head_of(&rest)))?;
        if !after_kw.starts_with(char::is_whitespace) {
            return Err(format!("expected `hint`, found: {}", head_of(&rest)));
        }
        let after_kw = after_kw.trim_start();
        let name_len = after_kw
            .find(char::is_whitespace)
            .ok_or("a hint ends before naming an identity")?;
        let (identity, after_name) = after_kw.split_at(name_len);
        let after_via = after_name
            .trim_start()
            .strip_prefix("via")
            .ok_or_else(|| format!("hint {}: expected `via`", identity))?
            .trim_start();
        let (body, after_body) = brace_block(after_via)
            .ok_or_else(|| format!("hint {}: expected a braced body", identity))?;
        let after_semi = after_body
            .trim_start()
            .strip_prefix(';')
            .ok_or_else(|| format!("hint {}: expected `;` after the body", identity))?;
        hints.push(Hint {
            identity: identity.to_string(),
            body: body.trim().to_string(),
        });
        rest = after_semi.to_string();
    }
}

/// Every `.hant` file directly under `root`, parsed, in filename order.
pub fn collect_hints(root: &Path) -> Result<Vec<Hint>, String> {
    let mut files: Vec<_> = std::fs::read_dir(root)
        .map_err(|e| format!("cannot read {}: {}", root.display(), e))?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "hant"))
        .collect();
    files.sort();
    let mut hints = Vec::new();
    for file in files {
        let text = std::fs::read_to_string(&file)
            .map_err(|e| format!("cannot read {}: {}", file.display(), e))?;
        hints.extend(parse_hints(&text).map_err(|e| format!("{}: {}", file.display(), e))?);
    }
    Ok(hints)
}

/// The name of the scratch sentence the `i`-th hint compiles into.
pub fn scratch_name(i: usize) -> String {
    format!("__hint_{}", i)
}

/// The source text to append to the corpus so every stone compiles in it.
pub fn scratch_sentences(hints: &[Hint]) -> String {
    hints
        .iter()
        .enumerate()
        .map(|(i, h)| format!("\nsentence {} {{ {} }}\n", scratch_name(i), h.body))
        .collect()
}

fn strip_comments(text: &str) -> String {
    text.lines()
        .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
        .collect::<Vec<_>>()
        .join("\n")
}

fn head_of(rest: &str) -> String {
    rest.chars().take(24).collect()
}

/// Splits `{ ... }` off the front, brace-balanced, answering the inside and
/// what follows the closing brace.
fn brace_block(text: &str) -> Option<(&str, &str)> {
    let mut chars = text.char_indices();
    let (_, '{') = chars.next()? else { return None };
    let mut depth = 1usize;
    for (i, c) in chars {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some((&text[1..i], &text[i + 1..]));
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_hint_file_parses_into_its_entries() {
        let hints = parse_hints(
            r#"
            // stones for the hard ones
            hint identities::two_spellings via { drop 0 push true };
            hint identities::nested via { branch { push 1 } { push 2 } };
            "#,
        )
        .unwrap();
        assert_eq!(hints.len(), 2);
        assert_eq!(hints[0].identity, "identities::two_spellings");
        assert_eq!(hints[0].body, "drop 0 push true");
        assert_eq!(hints[1].body, "branch { push 1 } { push 2 }");
    }

    #[test]
    fn a_malformed_entry_is_refused_with_its_name() {
        let err = parse_hints("hint foo via push 1;").unwrap_err();
        assert!(err.contains("foo"), "{}", err);
        let err = parse_hints("hunt foo via { push 1 };").unwrap_err();
        assert!(err.contains("expected `hint`"), "{}", err);
    }

    #[test]
    fn scratch_sentences_compile_in_a_library() {
        let hints = parse_hints("hint probe via { push 1 push 2 add };").unwrap();
        let source = format!(
            "identity probe {{ push 3 }} = {{ push 3 }};{}",
            scratch_sentences(&hints)
        );
        let library = bytecode::assemble(&source).unwrap();
        assert!(library.names.iter().any(|n| n == "__hint_0"));
    }
}
