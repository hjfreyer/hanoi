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
//! **problem** — a renamed identity would otherwise silently shed its proof — and so
//! is a claim with two proofs. Problems do not stop the run: proving
//! proceeds with what attached, and the caller decides that a problem is a
//! failure, which `bin/prove` does.

use std::collections::{HashMap, HashSet};
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

/// Every identity a strategy spends with `by`, nested arms included.
///
/// The edges of the proving order: a proof that names another identity needs
/// that one proved first, since what it carries in is that proof's steps.
pub(crate) fn lemmas_of(strategy: &Strategy<Body>, out: &mut Vec<IdentityIndex>) {
    for step in strategy {
        match step {
            Step::By {
                of: Body::Lemma(idx),
                ..
            } => {
                if !out.contains(idx) {
                    out.push(*idx);
                }
            }
            Step::Via { left, right, .. }
            | Step::Cases {
                then_arm: left,
                else_arm: right,
                ..
            }
            | Step::SelectSame {
                then_arm: left,
                else_arm: right,
            } => {
                for arm in [left, right].into_iter().flatten() {
                    lemmas_of(arm, out);
                }
            }
            _ => {}
        }
    }
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
                // Resolved here for the same reason `inline`'s label is,
                // and for one more: the proving order is read off these, so
                // the dependency has to be a fact before any proof runs.
                Step::By { side, of } => Step::By {
                    side: *side,
                    of: Body::Lemma(
                        library
                            .identity_by_name(of)
                            .map_err(|e| format!("`by`: {}", e))?,
                    ),
                },
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
                Step::Cases {
                    prim,
                    literal,
                    then_arm,
                    else_arm,
                } => Step::Cases {
                    prim: prim.clone(),
                    literal: literal.clone(),
                    then_arm: side(ctx, then_arm, library)?,
                    else_arm: side(ctx, else_arm, library)?,
                },
                // Nothing in it waits on the library: the branch it splits
                // is the goal's own, and the blocks are read off it.
                Step::SelectSame { then_arm, else_arm } => Step::SelectSame {
                    then_arm: side(ctx, then_arm, library)?,
                    else_arm: side(ctx, else_arm, library)?,
                },
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

impl Corpus {
    /// Every identity, in an order that proves a `by`'s target before the
    /// proof that spends it.
    ///
    /// Library order otherwise, and library order exactly where no proof
    /// names another identity — which is the whole corpus today but one. A
    /// cycle is refused by name: two claims that lean on each other have
    /// proved neither, and the loop has to be reported rather than silently
    /// ordered away.
    pub fn proving_order(&self) -> Result<Vec<IdentityIndex>, String> {
        let mut needs: HashMap<IdentityIndex, Vec<IdentityIndex>> = HashMap::new();
        for (idx, strategy) in &self.proofs {
            let mut lemmas = Vec::new();
            lemmas_of(strategy, &mut lemmas);
            if !lemmas.is_empty() {
                needs.insert(*idx, lemmas);
            }
        }
        order_by_need(
            self.library
                .identities
                .iter_enumerated()
                .map(|(idx, _)| idx),
            &needs,
            &|idx| self.library.identities[idx].name.clone(),
        )
    }
}

/// The declared order, with each identity moved after whatever it needs.
///
/// Depth-first over `needs`, entered in declaration order, so an identity
/// nothing leans on stays exactly where it was written. `name` is only for
/// the message a cycle raises, which is the one thing this cannot order its
/// way out of: two claims that lean on each other have proved neither.
fn order_by_need(
    all: impl Iterator<Item = IdentityIndex>,
    needs: &HashMap<IdentityIndex, Vec<IdentityIndex>>,
    name: &dyn Fn(IdentityIndex) -> String,
) -> Result<Vec<IdentityIndex>, String> {
    let mut order = Vec::new();
    let mut done: HashSet<IdentityIndex> = HashSet::new();
    for idx in all {
        visit(idx, needs, &mut done, &mut Vec::new(), name, &mut order)?;
    }
    Ok(order)
}

/// Depth-first, with the path carried so a cycle can name itself.
fn visit(
    idx: IdentityIndex,
    needs: &HashMap<IdentityIndex, Vec<IdentityIndex>>,
    done: &mut HashSet<IdentityIndex>,
    open: &mut Vec<IdentityIndex>,
    name: &dyn Fn(IdentityIndex) -> String,
    order: &mut Vec<IdentityIndex>,
) -> Result<(), String> {
    if done.contains(&idx) {
        return Ok(());
    }
    if let Some(at) = open.iter().position(|&held| held == idx) {
        let loop_names: Vec<String> = open[at..]
            .iter()
            .chain(std::iter::once(&idx))
            .map(|&i| name(i))
            .collect();
        return Err(format!(
            "these identities are proved by each other and so by nothing: {}",
            loop_names.join(" -> ")
        ));
    }
    open.push(idx);
    for &needed in needs.get(&idx).map(Vec::as_slice).unwrap_or(&[]) {
        visit(needed, needs, done, open, name, order)?;
    }
    open.pop();
    done.insert(idx);
    order.push(idx);
    Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(raw: &[usize]) -> Vec<IdentityIndex> {
        raw.iter().map(|&i| IdentityIndex::from(i)).collect()
    }

    fn needing(edges: &[(usize, &[usize])]) -> HashMap<IdentityIndex, Vec<IdentityIndex>> {
        edges
            .iter()
            .map(|&(at, on)| (IdentityIndex::from(at), ids(on)))
            .collect()
    }

    fn order(count: usize, edges: &[(usize, &[usize])]) -> Result<Vec<IdentityIndex>, String> {
        order_by_need(
            (0..count).map(IdentityIndex::from),
            &needing(edges),
            &|idx| format!("#{}", usize::from(idx)),
        )
    }

    /// Nothing leans on anything, so nothing moves.
    #[test]
    fn a_corpus_that_needs_nothing_is_proved_as_written() {
        assert_eq!(order(4, &[]).unwrap(), ids(&[0, 1, 2, 3]));
    }

    /// A `by` names a claim written later, and it is proved earlier anyway —
    /// which is the whole reason the order is computed rather than assumed.
    #[test]
    fn what_a_proof_needs_is_proved_before_it() {
        assert_eq!(order(3, &[(0, &[2])]).unwrap(), ids(&[2, 0, 1]));
        // Transitively, and each still ahead of what leans on it.
        assert_eq!(order(3, &[(0, &[1]), (1, &[2])]).unwrap(), ids(&[2, 1, 0]));
    }

    /// Two claims leaning on each other have proved neither, and the loop is
    /// named rather than ordered away.
    #[test]
    fn a_loop_of_proofs_is_refused_by_name() {
        let why = order(3, &[(0, &[1]), (1, &[0])]).unwrap_err();
        assert!(why.contains("#0 -> #1 -> #0"), "{}", why);
        let why = order(1, &[(0, &[0])]).unwrap_err();
        assert!(why.contains("#0 -> #0"), "{}", why);
    }

    /// One identity needed by two others is proved once, not twice.
    #[test]
    fn a_shared_need_is_proved_once() {
        assert_eq!(order(3, &[(0, &[2]), (1, &[2])]).unwrap(), ids(&[2, 0, 1]));
    }
}
