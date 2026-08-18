//! Loading a source tree's identities and their proofs together.
//!
//! One entry point for `bin/prove` and the tests: read the corpus rooted at
//! `main.hana`, read every `.hant` beside it, read every `via` waypoint and
//! `solve` template as a [term](crate::parse), and hand back the library with
//! each proof attached to the identity it names.
//!
//! A body is a **term**, not a Hana sentence. A residual is printed in the
//! term language and a waypoint is the answer to a residual, so the two are
//! one language: `copy(1) ; id(1) * push t1 ; equal` is what the report says
//! and what the proof writes. Bodies used to be compiled as scratch sentences
//! appended to the corpus source — which reused the real parser, and cost the
//! author a translation of every waypoint, plus a scratch **hole sentence**
//! per `solve` variable to carry its declared arity. Now the arity is on the
//! variable, the padding is written rather than inferred, and a body whose
//! halves do not meet says so where it is written.
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

/// A loaded corpus: the compiled library, the proofs that attached, and the
/// entries that could not attach.
pub struct Corpus {
    pub library: Library,
    pub proofs: HashMap<IdentityIndex, Strategy<Body>>,
    pub problems: Vec<String>,
}

/// Turns a parsed strategy into a runnable one by reading each body as a term
/// against the library the proof is written for.
pub(crate) fn attach(
    strategy: &Strategy<String>,
    library: &Library,
) -> Result<Strategy<Body>, String> {
    strategy
        .iter()
        .map(|step| {
            Ok(match step {
                Step::Egraph => Step::Egraph,
                Step::Peel => Step::Peel,
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
                        parse_term(waypoint, &Scope::new(library))
                            .map_err(|e| format!("`via` body: {}", e))?,
                    ),
                    left: side(left, library)?,
                    right: side(right, library)?,
                },
                Step::Solve {
                    vars,
                    template,
                    right,
                } => {
                    // The declared variables are the scope the template is read
                    // in: each `?var` stands as a leaf of its declared arity,
                    // and the step records which leaf goes with which name.
                    let scope = Scope::with_holes(library, vars);
                    Step::Solve {
                        vars: vars.clone(),
                        template: Body::Template {
                            term: parse_term(template, &scope)
                                .map_err(|e| format!("`solve` template: {}", e))?,
                            holes: scope.holes_in_order(vars),
                        },
                        right: side(right, library)?,
                    }
                }
                Step::Descend { then_arm, else_arm } => Step::Descend {
                    then_arm: side(then_arm, library)?,
                    else_arm: side(else_arm, library)?,
                },
            })
        })
        .collect()
}

fn side(
    strategy: &Option<Strategy<String>>,
    library: &Library,
) -> Result<Option<Strategy<Body>>, String> {
    strategy.as_ref().map(|s| attach(s, library)).transpose()
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

    let mut problems = Vec::new();
    let mut proofs: HashMap<IdentityIndex, Strategy<Body>> = HashMap::new();
    for entry in entries {
        let strategy = match attach(&entry.strategy, &library) {
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
