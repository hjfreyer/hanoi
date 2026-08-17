//! Loading a source tree's identities and their proofs together.
//!
//! One entry point for `bin/prove` and the tests: read the corpus rooted at
//! `main.hana`, read every `.hant` beside it, compile the `via` bodies as
//! scratch sentences (so the real parser and resolver do the work), and hand
//! back the library with each proof attached to the identity it names.
//!
//! Attachment is checked both ways. An entry naming no stated identity is a
//! **problem** — a renamed identity must not silently shed its proof — and so
//! is a claim with two proofs. Problems do not stop the run: proving
//! proceeds with what attached, and the caller decides that a problem is a
//! failure, which `bin/prove` does.

use std::collections::HashMap;
use std::path::Path;

use bytecode::{IdentityIndex, Library, SourceMap, assemble_source};

use crate::hant::{ProofEntry, Strategy, map_via, parse_hant, via_bodies};
use crate::term::{Term, lower};

/// A loaded corpus: the compiled library, the proofs that attached, and the
/// entries that could not attach.
pub struct Corpus {
    pub library: Library,
    pub proofs: HashMap<IdentityIndex, Strategy<Term>>,
    pub problems: Vec<String>,
}

/// The name of the scratch sentence the `i`-th `via` body compiles into.
fn scratch_name(i: usize) -> String {
    format!("__via_{}", i)
}

/// Loads the corpus rooted at `root/main.hana`, plus every `.hant` directly
/// under `root`.
pub fn load(root: &Path) -> Result<Corpus, String> {
    let main_path = root.join("main.hana");
    let mut text = std::fs::read_to_string(&main_path)
        .map_err(|e| format!("cannot read {}: {}", main_path.display(), e))?;
    let entries = collect_entries(root)?;

    // Every stepping stone becomes a scratch sentence at the crate root,
    // numbered in reading order across all entries.
    let bodies: Vec<String> = entries
        .iter()
        .flat_map(|e| via_bodies(&e.strategy))
        .collect();
    for (i, body) in bodies.iter().enumerate() {
        text.push_str(&format!("\nsentence {} {{ {} }}\n", scratch_name(i), body));
    }

    let mut map = SourceMap::new();
    let file = map.add("main.hana", text);
    let library = assemble_source(&mut map, file, Some(root)).map_err(|e| map.render(&e))?;

    let mut problems = Vec::new();
    let mut proofs: HashMap<IdentityIndex, Strategy<Term>> = HashMap::new();
    let mut next_via = 0usize;
    for entry in entries {
        // Lower this entry's stones. The counter advances for orphans too:
        // the scratch numbering was fixed at collection time.
        let strategy = map_via(entry.strategy, &mut |_body: String| {
            let name = scratch_name(next_via);
            next_via += 1;
            let idx = library
                .names
                .iter_enumerated()
                .find(|(_, n)| **n == name)
                .map(|(idx, _)| idx)
                .expect("every via body compiled into a scratch sentence");
            lower(&library, idx).map_err(|e| e.to_string())
        });
        let strategy = match strategy {
            Ok(s) => s,
            Err(e) => {
                problems.push(format!("proof {}: {}", entry.identity, e));
                continue;
            }
        };
        match library.identity_by_name(&entry.identity) {
            Ok(idx) => {
                if proofs.insert(idx, strategy).is_some() {
                    problems.push(format!(
                        "identity {} is proved twice; a claim discharged twice was discharged once too often",
                        entry.identity
                    ));
                }
            }
            Err(e) => problems.push(format!("orphaned proof {}: {}", entry.identity, e)),
        }
    }

    Ok(Corpus {
        library,
        proofs,
        problems,
    })
}

/// Every `.hant` file directly under `root`, parsed, in filename order.
fn collect_entries(root: &Path) -> Result<Vec<ProofEntry>, String> {
    let mut files: Vec<_> = std::fs::read_dir(root)
        .map_err(|e| format!("cannot read {}: {}", root.display(), e))?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "hant"))
        .collect();
    files.sort();
    let mut entries = Vec::new();
    for file in files {
        let text = std::fs::read_to_string(&file)
            .map_err(|e| format!("cannot read {}: {}", file.display(), e))?;
        entries.extend(parse_hant(&text).map_err(|e| format!("{}: {}", file.display(), e))?);
    }
    Ok(entries)
}
