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

use bytecode::arity::{failure_reachability, sentence_arity};
use bytecode::{Arity, Library, SentenceIndex, Value};

pub(crate) struct Program<'a> {
    library: &'a Library,
    /// Indexed by `usize::from(SentenceIndex)`.
    arities: Vec<Option<(i64, i64)>>,
    /// Indexed the same way. A whole-library fixpoint, so it is computed once:
    /// `prove` asks it twice per identity, and there may be many.
    can_fail: Vec<bool>,
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

        Program {
            library,
            arities,
            can_fail: failure_reachability(library),
        }
    }

    pub(crate) fn library(&self) -> &'a Library {
        self.library
    }

    /// What the sentence takes and leaves, or `None` when that is not known —
    /// a sentence that always panics.
    pub(crate) fn arity(&self, s_idx: SentenceIndex) -> Option<(i64, i64)> {
        self.arities.get(usize::from(s_idx)).copied().flatten()
    }

    /// Whether the sentence reaches a `panic`, an `assert` or an `assert_eq`,
    /// directly or through a call.
    ///
    /// The precondition the equations are stated under. It is closed over
    /// reachability, so a root that answers `false` answers for every node a
    /// tree built from it can hold.
    ///
    /// The other thing this tool needs — that expanding a call terminates — is
    /// not a question it has to ask. Recursion is forbidden, and
    /// `check_arities` refuses it, so every sentence in a library that compiled
    /// has a finite expansion.
    pub(crate) fn can_fail(&self, s_idx: SentenceIndex) -> bool {
        self.can_fail[usize::from(s_idx)]
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

/// The symbol a name denotes: an exact fully qualified name, or an unambiguous
/// trailing part of one.
///
/// The same reading `resolve_sentence` gives a sentence, and for the same
/// reason — `Idle::tag` beats writing every segment of
/// `queue::State::Idle::tag` out.
///
/// A symbol cannot be built from its name: [`bytecode::Symbol`] compares by
/// `id`, and two declarations reading the same are different symbols. So a
/// term that pushes one is looking the real one up rather than making it, and
/// a name that denotes none is refused. (A `"const string"` is the opposite
/// case — it *is* its text, so a term writes one out.)
pub(crate) fn resolve_symbol(library: &Library, ident: &str) -> Result<Value, String> {
    if let Some(value) = library.symbols.get(ident) {
        return Ok(value.clone());
    }

    let suffix = format!("::{}", ident);
    let matches: Vec<&String> = library
        .symbols
        .keys()
        .filter(|name| name.ends_with(&suffix))
        .collect();
    match matches.len() {
        1 => Ok(library.symbols[matches[0]].clone()),
        0 => Err(no_such_symbol(library, ident)),
        _ => {
            let mut named: Vec<&str> = matches.iter().map(|s| s.as_str()).collect();
            named.sort();
            Err(format!(
                "'{}' is ambiguous: {}",
                ident,
                render_names(&named)
            ))
        }
    }
}

/// What went wrong, with the names that were on offer.
///
/// A symbol prints as the fully qualified name it is declared under, which is
/// the same name this reads, so a name taken off a listing can be written back
/// as it stands.
fn no_such_symbol(library: &Library, ident: &str) -> String {
    let mut named: Vec<&str> = library.symbols.keys().map(|s| s.as_str()).collect();
    named.sort();
    format!(
        "No symbol matching '{}'. Symbols:{}",
        ident,
        render_names(&named)
    )
}

fn render_names(names: &[&str]) -> String {
    let mut out = String::from("\n");
    for name in names.iter().take(MAX_LISTED) {
        out.push_str(&format!("  {}\n", name));
    }
    if names.len() > MAX_LISTED {
        out.push_str(&format!("  ... and {} more\n", names.len() - MAX_LISTED));
    }
    out
}

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
