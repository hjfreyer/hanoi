//! Loading a source tree's identities and their proofs together.
//!
//! One entry point for `bin/prove` and the tests: read the corpus rooted at
//! `main.hana`, read every `.hant` beside it, compile every `via` waypoint
//! and `solve` template as scratch sentences (so the real parser and
//! resolver do the work), and hand back the library with each proof attached
//! to the identity it names.
//!
//! A `solve` template needs two extra motions the loader owns. Its declared
//! variables become **hole sentences** — scratch sentences whose whole
//! content is having the declared arity — and each `?var` in the body is
//! substituted with a call to its hole before the template compiles, so the
//! lowering's padding arithmetic works over real arities. A `?var` the head
//! does not declare, or a declared variable the body never mentions, is an
//! error at load time: a template that does not mean what it says must not
//! quietly search for something else.
//!
//! Attachment is checked both ways. An entry naming no stated identity is a
//! **problem** — a renamed identity must not silently shed its proof — and so
//! is a claim with two proofs. Problems do not stop the run: proving
//! proceeds with what attached, and the caller decides that a problem is a
//! failure, which `bin/prove` does.

use std::collections::{HashMap, VecDeque};
use std::path::Path;

use bytecode::{IdentityIndex, Library, SentenceIndex, SourceMap, assemble_source};

use crate::hant::{Body, ProofEntry, Step, Strategy, parse_hant};
use crate::term::{Term, lower};

/// A loaded corpus: the compiled library, the proofs that attached, and the
/// entries that could not attach.
pub struct Corpus {
    pub library: Library,
    pub proofs: HashMap<IdentityIndex, Strategy<Body>>,
    pub problems: Vec<String>,
}

/// One planned scratch compilation, in strategy walk order.
pub(crate) enum Planned {
    /// A `via` waypoint: the named scratch sentence holds its body.
    Stone { name: String },
    /// A `solve` template: the named scratch sentence holds the body with
    /// every `?var` substituted by a call to its hole sentence.
    Template {
        name: String,
        /// Per declared variable, in declaration order: the hole's name.
        holes: Vec<(String, String)>,
    },
}

/// Walks every entry once, generating the scratch source to append to the
/// corpus and the plan [`attach`] will consume in the same order.
pub(crate) fn plan_scratches(
    entries: &[ProofEntry],
) -> Result<(String, VecDeque<Planned>), String> {
    let mut source = String::new();
    let mut plan = VecDeque::new();
    let mut counter = 0usize;
    for entry in entries {
        plan_strategy(&entry.strategy, &mut source, &mut plan, &mut counter)
            .map_err(|e| format!("proof {}: {}", entry.identity, e))?;
    }
    Ok((source, plan))
}

fn plan_strategy(
    strategy: &Strategy<String>,
    source: &mut String,
    plan: &mut VecDeque<Planned>,
    counter: &mut usize,
) -> Result<(), String> {
    for step in strategy {
        match step {
            Step::Via {
                waypoint,
                left,
                right,
            } => {
                let name = format!("__via_{}", counter);
                *counter += 1;
                source.push_str(&format!("\nsentence {} {{ {} }}\n", name, waypoint));
                plan.push_back(Planned::Stone { name });
                for side in [left, right].into_iter().flatten() {
                    plan_strategy(side, source, plan, counter)?;
                }
            }
            Step::Solve {
                vars,
                template,
                right,
            } => {
                let mut holes = Vec::new();
                for (var, (inputs, outputs)) in vars {
                    let hole = format!("__hole_{}", counter);
                    *counter += 1;
                    // A sentence whose whole content is its arity: take
                    // `inputs` values, leave `outputs` zeros.
                    let body = "drop 0 ".repeat(*inputs) + &"push 0 ".repeat(*outputs);
                    source.push_str(&format!("\nsentence {} {{ {} }}\n", hole, body));
                    holes.push((var.clone(), hole));
                }
                let filled = fill_holes(template, &holes)?;
                let name = format!("__solve_{}", counter);
                *counter += 1;
                source.push_str(&format!("\nsentence {} {{ {} }}\n", name, filled));
                plan.push_back(Planned::Template { name, holes });
                for side in right.iter() {
                    plan_strategy(side, source, plan, counter)?;
                }
            }
            Step::Descend { then_arm, else_arm } => {
                for arm in [then_arm, else_arm].into_iter().flatten() {
                    plan_strategy(arm, source, plan, counter)?;
                }
            }
            Step::Egraph | Step::Peel | Step::Inline => {}
        }
    }
    Ok(())
}

/// Substitutes every `?var` token with a call to its hole sentence, and
/// holds the template to naming exactly the declared variables.
fn fill_holes(template: &str, holes: &[(String, String)]) -> Result<String, String> {
    let mut out = String::new();
    let mut used = vec![false; holes.len()];
    let mut rest = template;
    while let Some(at) = rest.find('?') {
        out.push_str(&rest[..at]);
        let after = &rest[at + 1..];
        let name_len = after
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(after.len());
        let name = &after[..name_len];
        let Some(i) = holes.iter().position(|(var, _)| var == name) else {
            return Err(format!(
                "the template names ?{} but the head declares no such variable",
                name
            ));
        };
        used[i] = true;
        out.push_str(&format!("jump crate::{}", holes[i].1));
        rest = &after[name_len..];
    }
    out.push_str(rest);
    if let Some(i) = used.iter().position(|u| !u) {
        return Err(format!(
            "the head declares {} but the template never mentions ?{}",
            holes[i].0, holes[i].0
        ));
    }
    Ok(out)
}

/// Turns a parsed strategy into a runnable one by lowering its scratch
/// sentences out of the compiled library, consuming the plan in the same
/// order [`plan_scratches`] wrote it.
pub(crate) fn attach(
    strategy: &Strategy<String>,
    plan: &mut VecDeque<Planned>,
    library: &Library,
) -> Result<Strategy<Body>, String> {
    strategy
        .iter()
        .map(|step| {
            Ok(match step {
                Step::Egraph => Step::Egraph,
                Step::Peel => Step::Peel,
                Step::Inline => Step::Inline,
                Step::Via { left, right, .. } => {
                    let Some(Planned::Stone { name }) = plan.pop_front() else {
                        unreachable!("the plan walks the same strategies in the same order");
                    };
                    Step::Via {
                        waypoint: Body::Stone(lower_named(library, &name)?),
                        left: left
                            .as_ref()
                            .map(|s| attach(s, plan, library))
                            .transpose()?,
                        right: right
                            .as_ref()
                            .map(|s| attach(s, plan, library))
                            .transpose()?,
                    }
                }
                Step::Solve { vars, right, .. } => {
                    let Some(Planned::Template { name, holes }) = plan.pop_front() else {
                        unreachable!("the plan walks the same strategies in the same order");
                    };
                    let term = lower_named(library, &name)?;
                    let holes = holes
                        .iter()
                        .map(|(var, hole)| Ok((var.clone(), sentence_named(library, hole)?)))
                        .collect::<Result<Vec<_>, String>>()?;
                    Step::Solve {
                        vars: vars.clone(),
                        template: Body::Template { term, holes },
                        right: right
                            .as_ref()
                            .map(|s| attach(s, plan, library))
                            .transpose()?,
                    }
                }
                Step::Descend { then_arm, else_arm } => Step::Descend {
                    then_arm: then_arm
                        .as_ref()
                        .map(|s| attach(s, plan, library))
                        .transpose()?,
                    else_arm: else_arm
                        .as_ref()
                        .map(|s| attach(s, plan, library))
                        .transpose()?,
                },
            })
        })
        .collect()
}

fn sentence_named(library: &Library, name: &str) -> Result<SentenceIndex, String> {
    library
        .names
        .iter_enumerated()
        .find(|(_, n)| *n == name)
        .map(|(idx, _)| idx)
        .ok_or_else(|| format!("scratch sentence {} did not compile", name))
}

fn lower_named(library: &Library, name: &str) -> Result<Term, String> {
    lower(library, sentence_named(library, name)?).map_err(|e| e.to_string())
}

/// Loads the corpus rooted at `root/main.hana`, plus every `.hant` directly
/// under `root`.
pub fn load(root: &Path) -> Result<Corpus, String> {
    let main_path = root.join("main.hana");
    let mut text = std::fs::read_to_string(&main_path)
        .map_err(|e| format!("cannot read {}: {}", main_path.display(), e))?;
    let entries = collect_entries(root)?;
    let (scratch, mut plan) = plan_scratches(&entries)?;
    text.push_str(&scratch);

    let mut map = SourceMap::new();
    let file = map.add("main.hana", text);
    let library = assemble_source(&mut map, file, Some(root)).map_err(|e| map.render(&e))?;

    let mut problems = Vec::new();
    let mut proofs: HashMap<IdentityIndex, Strategy<Body>> = HashMap::new();
    for entry in entries {
        // Attach always walks, so the plan stays in step even when the entry
        // turns out to be orphaned.
        let strategy = match attach(&entry.strategy, &mut plan, &library) {
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
    debug_assert!(plan.is_empty(), "every planned scratch was consumed");

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_template_names_only_declared_variables() {
        let holes = vec![("f".to_string(), "__hole_0".to_string())];
        assert_eq!(
            fill_holes("?f is_bool", &holes).unwrap(),
            "jump crate::__hole_0 is_bool"
        );
        let err = fill_holes("?g is_bool", &holes).unwrap_err();
        assert!(err.contains("?g"), "{}", err);
        let err = fill_holes("is_bool", &holes).unwrap_err();
        assert!(err.contains("never mentions ?f"), "{}", err);
    }

    #[test]
    fn a_variable_is_a_whole_token() {
        // `?fx` is not a mention of `?f`.
        let holes = vec![
            ("f".to_string(), "__hole_0".to_string()),
            ("fx".to_string(), "__hole_1".to_string()),
        ];
        assert_eq!(
            fill_holes("?fx ?f", &holes).unwrap(),
            "jump crate::__hole_1 jump crate::__hole_0"
        );
    }
}
