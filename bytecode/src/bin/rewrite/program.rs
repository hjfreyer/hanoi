//! Facts about the library, computed once and handed to every rule.
//!
//! A [`Node::Call`][crate::ir::Node::Call] names a sentence rather than holding
//! its body, so a rule that meets one has to look the target up. That trades
//! away a property the tree used to have — that arities were computable from
//! the tree alone — for the ability to make inlining a rule rather than
//! something `build` does behind your back.
//!
//! What it does *not* trade away is the governing invariant: everything here is
//! a fact about the whole library, never about where in the tree a rule is
//! being applied.

use bytecode::arity::sentence_arity;
use bytecode::{Annotation, Arity, Library, SentenceIndex};

pub(crate) struct Program<'a> {
    library: &'a Library,
    /// Indexed by `usize::from(SentenceIndex)`.
    arities: Vec<Option<(i64, i64)>>,
}

impl<'a> Program<'a> {
    pub(crate) fn new(library: &'a Library) -> Self {
        let arities = (0..library.sentences.len())
            .map(|i| match sentence_arity(library, SentenceIndex::from(i)) {
                Some(Arity::Normal { inputs, outputs }) => Some((inputs, outputs)),
                // A sentence that always panics has no output count, and one
                // whose arity could not be inferred has neither.
                Some(Arity::Panic { .. }) | None => None,
            })
            .collect();

        Program { library, arities }
    }

    pub(crate) fn library(&self) -> &'a Library {
        self.library
    }

    /// What the sentence takes and leaves, or `None` when that is not known —
    /// an unannotated `#[recursive]` sentence, or one that always panics.
    pub(crate) fn arity(&self, s_idx: SentenceIndex) -> Option<(i64, i64)> {
        self.arities.get(usize::from(s_idx)).copied().flatten()
    }

    /// Whether the sentence is marked `#[recursive]`.
    ///
    /// This one annotation decides whether the tool will touch a sentence at
    /// all, and it does so without any analysis, because `check_arities`
    /// already did the work: a sentence that is *not* `#[recursive]` may not
    /// call one that is, and a sentence in a cycle cannot escape the annotation
    /// either, since inference would detect the cycle and refuse to compile.
    ///
    /// So the annotation propagates transitively up the call graph, and its
    /// absence on a root is a proof that expanding it terminates. There is
    /// nothing to traverse. `invariant::reaching_a_cycle_implies_the_recursive_annotation`
    /// checks that claim against the real corpus rather than taking it on faith.
    pub(crate) fn is_recursive(&self, s_idx: SentenceIndex) -> bool {
        self.library.annotations[s_idx]
            .iter()
            .any(|ann| matches!(ann, Annotation::Recursive))
    }

    pub(crate) fn label(&self, s_idx: SentenceIndex) -> String {
        format!("#{} {}", usize::from(s_idx), self.library.names[s_idx])
    }
}

// ---------------------------------------------------------------------------
// Naming a sentence
// ---------------------------------------------------------------------------

/// The most a listing prints before it stops being an aid and starts being a
/// wall; `check` alone matches nearly sixty sentences in the test corpus.
const MAX_LISTED: usize = 15;

/// Accepts an index (`#12` or `12`), an exact name, or an unambiguous suffix.
pub(crate) fn resolve_sentence(library: &Library, ident: &str) -> Result<SentenceIndex, String> {
    let numeric = ident.strip_prefix('#').unwrap_or(ident);
    if let Ok(raw) = numeric.parse::<usize>() {
        if raw >= library.sentences.len() {
            return Err(format!(
                "No sentence #{}: the library has {}",
                raw,
                library.sentences.len()
            ));
        }
        return Ok(SentenceIndex::from(raw));
    }

    let exact: Vec<SentenceIndex> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| *name == ident)
        .map(|(idx, _)| idx)
        .collect();
    if exact.len() == 1 {
        return Ok(exact[0]);
    }
    if exact.len() > 1 {
        return Err(format!(
            "'{}' is ambiguous: {}",
            ident,
            render_candidates(library, &exact)
        ));
    }

    // Fall back to a trailing path match, so `queue::accept` finds
    // `queue::queue::accept` without spelling out every segment.
    let suffix = format!("::{}", ident);
    let matches: Vec<SentenceIndex> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| name.ends_with(&suffix))
        .map(|(idx, _)| idx)
        .collect();

    match matches.len() {
        1 => Ok(matches[0]),
        0 => Err(format!(
            "No sentence matching '{}'. Named sentences:\n{}",
            ident,
            named_sentence_list(library)
        )),
        _ => Err(format!(
            "'{}' is ambiguous: {}",
            ident,
            render_candidates(library, &matches)
        )),
    }
}

pub(crate) fn render_candidates(library: &Library, candidates: &[SentenceIndex]) -> String {
    let mut out = String::from("\n");
    for idx in candidates.iter().take(MAX_LISTED) {
        out.push_str(&format!(
            "  #{:<5} {}\n",
            usize::from(*idx),
            library.names[*idx]
        ));
    }
    if candidates.len() > MAX_LISTED {
        out.push_str(&format!(
            "  ... and {} more\n",
            candidates.len() - MAX_LISTED
        ));
    }
    out
}

pub(crate) fn named_sentence_list(library: &Library) -> String {
    let mut named: Vec<(&str, SentenceIndex)> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| *name != "<inline>")
        .map(|(idx, name)| (name.as_str(), idx))
        .collect();
    named.sort();

    let total = named.len();
    let mut out: Vec<String> = named
        .into_iter()
        .take(MAX_LISTED)
        .map(|(name, idx)| format!("  #{:<5} {}", usize::from(idx), name))
        .collect();
    if total > MAX_LISTED {
        out.push(format!("  ... and {} more", total - MAX_LISTED));
    }
    out.join("\n")
}

#[cfg(test)]
mod invariant {
    use super::*;
    use bytecode::{Instruction, assemble};
    use std::collections::HashSet;
    use std::fs;
    use std::path::Path;

    /// Every sentence that can reach itself through calls or branch arms.
    ///
    /// Test-only: the tool does not compute this, it reads the annotation. This
    /// exists to check that reading the annotation is enough.
    fn cyclic_sentences(library: &Library) -> HashSet<SentenceIndex> {
        #[derive(Clone, Copy, PartialEq)]
        enum Colour {
            Unvisited,
            OnPath,
            Done,
        }

        fn walk(
            library: &Library,
            s_idx: SentenceIndex,
            colour: &mut [Colour],
            path: &mut Vec<SentenceIndex>,
            cyclic: &mut HashSet<SentenceIndex>,
        ) {
            match colour[usize::from(s_idx)] {
                Colour::Done => return,
                // A back edge: everything from here to the top of the path is in a
                // cycle with it.
                Colour::OnPath => {
                    let start = path.iter().position(|p| *p == s_idx).unwrap_or(0);
                    cyclic.extend(path[start..].iter().copied());
                    return;
                }
                Colour::Unvisited => {}
            }

            colour[usize::from(s_idx)] = Colour::OnPath;
            path.push(s_idx);
            for inst in &library.sentences[s_idx] {
                match inst {
                    Instruction::Dip(_, target) => walk(library, *target, colour, path, cyclic),
                    Instruction::Branch(then_t, else_t) => {
                        walk(library, *then_t, colour, path, cyclic);
                        walk(library, *else_t, colour, path, cyclic);
                    }
                    _ => {}
                }
            }
            path.pop();
            colour[usize::from(s_idx)] = Colour::Done;
        }

        let mut cyclic = HashSet::new();
        let mut colour = vec![Colour::Unvisited; library.sentences.len()];
        let mut path = Vec::new();
        for i in 0..library.sentences.len() {
            walk(
                library,
                SentenceIndex::from(i),
                &mut colour,
                &mut path,
                &mut cyclic,
            );
        }
        cyclic
    }

    /// Every sentence that can *reach* a cycle, not merely be in one.
    fn reaches_cycle(library: &Library) -> HashSet<SentenceIndex> {
        let in_cycle = cyclic_sentences(library);
        let mut out = HashSet::new();
        // Fixpoint: a sentence reaches a cycle if it is in one, or calls
        // something that reaches one.
        loop {
            let before = out.len();
            for i in 0..library.sentences.len() {
                let s_idx = SentenceIndex::from(i);
                if out.contains(&s_idx) {
                    continue;
                }
                let hit = in_cycle.contains(&s_idx)
                    || library.sentences[s_idx].iter().any(|inst| match inst {
                        Instruction::Dip(_, t) => in_cycle.contains(t) || out.contains(t),
                        Instruction::Branch(a, b) => {
                            in_cycle.contains(a)
                                || out.contains(a)
                                || in_cycle.contains(b)
                                || out.contains(b)
                        }
                        _ => false,
                    });
                if hit {
                    out.insert(s_idx);
                }
            }
            if out.len() == before {
                return out;
            }
        }
    }

    /// The claim this tool is about to rely on: reaching a cycle implies the
    /// annotation, so the annotation's *absence* proves inlining terminates.
    ///
    /// `check_arities` is what enforces it — a sentence that is not
    /// `#[recursive]` may not call one that is — and a cycle member cannot
    /// escape the annotation either, since inference would detect the cycle.
    #[test]
    fn reaching_a_cycle_implies_the_recursive_annotation() {
        let main = Path::new("../tests/main.hana");
        let Ok(code) = fs::read_to_string(main) else {
            return;
        };
        let library = bytecode::assemble_with_path(&code, main.parent()).unwrap();

        let mut unannotated = Vec::new();
        for s_idx in reaches_cycle(&library) {
            let annotated = library.annotations[s_idx]
                .iter()
                .any(|a| matches!(a, Annotation::Recursive));
            if !annotated {
                unannotated.push(library.names[s_idx].clone());
            }
        }
        unannotated.sort();
        assert!(
            unannotated.is_empty(),
            "these reach a cycle without being #[recursive]: {:?}",
            unannotated
        );
    }

    fn cyclic_names(code: &str) -> Vec<String> {
        let library = assemble(code).unwrap();
        let cyclic = cyclic_sentences(&library);
        let mut out: Vec<String> = library
            .names
            .iter_enumerated()
            .filter(|(idx, _)| cyclic.contains(idx))
            .map(|(_, name)| name.clone())
            .collect();
        out.sort();
        out
    }

    #[test]
    fn the_cycle_finder_agrees_with_itself_on_small_cases() {
        // It only has to be right enough to be worth trusting as a check on the
        // annotation, but that means it does have to be right.
        assert!(cyclic_names("sentence leaf { add } sentence probe { jump leaf }").is_empty());
        assert_eq!(
            cyclic_names("#[recursive] sentence loops { jump loops }"),
            vec!["loops"]
        );
        assert_eq!(
            cyclic_names(
                r#"
                #[recursive] sentence ping { jump pong }
                #[recursive] sentence pong { jump ping }
            "#
            ),
            vec!["ping", "pong"]
        );
        // Calling into a cycle is not being in one.
        assert_eq!(
            cyclic_names(
                r#"
                #[recursive] sentence loops { jump loops }
                #[recursive] sentence entry { jump loops }
            "#
            ),
            vec!["loops"]
        );
        // Recursion through a branch arm counts.
        assert!(
            cyclic_names(
                r#"
            #[recursive]
            sentence viabranch { pick 0 branch { drop 0 } { jump viabranch } }
        "#
            )
            .contains(&"viabranch".to_string())
        );
    }
}
