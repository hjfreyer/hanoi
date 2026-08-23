//! Loading a source tree's identities and their proofs together.
//!
//! One entry point for `bin/prove` and the tests: read the corpus rooted at
//! `main.hana`, read every `.hant` beside it, read every `via` waypoint as a
//! [term](crate::parse), and hand back the library with each proof attached
//! to the identity it names.
//!
//! A body is a **term**, not a Hana sentence. A residual is printed in the
//! term language and a waypoint is the answer to a residual, so the two are
//! one language: `copy(1) ; id(1) * push t1 ; equal` is what the report says
//! and what the proof writes. The padding is written rather than inferred,
//! and a body whose halves do not meet says so where it is written.
//!
//! Attachment is checked both ways. An entry naming no stated identity is a
//! **problem** — a renamed identity must not silently shed its proof — and so
//! is a claim with two proofs. Problems do not stop the run: proving
//! proceeds with what attached, and the caller decides that a problem is a
//! failure, which `bin/prove` does.

use std::collections::HashMap;
use std::path::Path;

use bytecode::{IdentityIndex, Library, SourceMap, assemble_source};

use crate::hant::{Body, ProofEntry, Step, Strategy, parse_hant};
use crate::parse::{Scope, parse_term, sentence_named};
use crate::term::Context;

/// A loaded corpus: the compiled library, the arena its waypoints were read
/// into, the proofs that attached, and the entries that could not attach.
///
/// The terms come with the corpus because a waypoint is an index: the prover
/// is handed this same [`Context`] so that what a proof says and what the
/// goals are built from are the one arena.
pub struct Corpus {
    pub library: Library,
    pub terms: Context,
    pub proofs: HashMap<IdentityIndex, Strategy<Body>>,
    pub problems: Vec<String>,
}

/// Turns a parsed strategy into a runnable one by reading each body as a term
/// against the library the proof is written for, into `ctx`.
pub(crate) fn attach(
    ctx: &mut Context,
    strategy: &Strategy<String>,
    library: &Library,
) -> Result<Strategy<Body>, String> {
    strategy
        .iter()
        .map(|step| {
            Ok(match step {
                Step::Diagram => Step::Diagram,
                // A tactic is already data — no name in it waits on the
                // library.
                Step::Rewrite { side, tactic } => Step::Rewrite {
                    side: *side,
                    tactic: tactic.clone(),
                },
                // A label is resolved here, so a proof naming a sentence that
                // is not there is a load-time problem rather than a failed
                // proof: the two mean different things to whoever reads the
                // report.
                Step::Inline(label) => Step::Inline(
                    label
                        .as_ref()
                        .map(|name| {
                            sentence_named(library, name)
                                .map(Body::Target)
                                .map_err(|e| format!("`inline`: {}", e))
                        })
                        .transpose()?,
                ),
                Step::Symm => Step::Symm,
                Step::Exact => Step::Exact,
                Step::Via {
                    waypoint,
                    left,
                    right,
                } => Step::Via {
                    waypoint: Body::Stone(
                        parse_term(ctx, waypoint, &Scope::new(library))
                            .map_err(|e| format!("`via` body: {}", e))?,
                    ),
                    left: side(ctx, left, library)?,
                    right: side(ctx, right, library)?,
                },
                Step::Cases { prim } => Step::Cases { prim: prim.clone() },
            })
        })
        .collect()
}

fn side(
    ctx: &mut Context,
    strategy: &Option<Strategy<String>>,
    library: &Library,
) -> Result<Option<Strategy<Body>>, String> {
    match strategy {
        Some(s) => attach(ctx, s, library).map(Some),
        None => Ok(None),
    }
}

/// Loads the corpus rooted at `root/main.hana`, plus every `.hant` directly
/// under `root`.
pub fn load(root: &Path) -> Result<Corpus, String> {
    let main_path = root.join("main.hana");
    let text = std::fs::read_to_string(&main_path)
        .map_err(|e| format!("cannot read {}: {}", main_path.display(), e))?;
    let entries = collect_entries(root)?;

    let mut map = SourceMap::new();
    let file = map.add("main.hana", text);
    let library = assemble_source(&mut map, file, Some(root)).map_err(|e| map.render(&e))?;

    let mut terms = Context::new();
    let mut problems = Vec::new();
    let mut proofs: HashMap<IdentityIndex, Strategy<Body>> = HashMap::new();
    for entry in entries {
        let strategy = match attach(&mut terms, &entry.strategy, &library) {
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
        terms,
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
