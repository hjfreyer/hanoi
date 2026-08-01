//! Dumps one sentence's compiled bytecode with every call inlined — both `dip`
//! targets (which includes plain jumps, since `jump` is `Dip(0, s)`) and both
//! arms of every `branch`.
//!
//! Optional rewrite passes then run to a fixpoint over the result:
//! `--dip-normalize` pushes dips left, fuses them, and splits them into nests
//! of unary `dip 1`s; `--factor-branches` hoists a run shared by both arms of
//! a branch out in front of it; `--annihilate` cancels a drop against the
//! instruction that produced what it drops. These are the rewrites an
//! optimizer would want to do, and this tool exists to let you eyeball them.
//!
//! This is a debugging aid, not a source generator: the output does not parse,
//! because a dipped block operates below its hidden region and so cannot be
//! spliced into the enclosing instruction stream as-is. What it gives you is
//! the whole call tree in one listing instead of a set of `SentenceIndex`
//! references to chase by hand.

mod arity;
mod ir;
mod passes;
mod print;
mod rules;
mod tactic;
#[cfg(test)]
mod tests;

use std::env;
use std::fs;
use std::path::Path;
use std::process;

use bytecode::{Library, SentenceIndex};

use crate::print::print_sentence;
use crate::passes::Passes;

fn main() {
    let mut passes = Passes::default();
    let mut positional: Vec<String> = Vec::new();
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "--dip-normalize" => passes.dip_normalize = true,
            "--factor-branches" => passes.factor_branches = true,
            "--annihilate" => passes.annihilate = true,
            flag if flag.starts_with("--") => {
                eprintln!("Unknown flag: {}", flag);
                process::exit(1);
            }
            _ => positional.push(arg),
        }
    }

    if positional.len() != 2 {
        eprintln!("Usage: rewrite <directory> <sentence> [passes...]");
        eprintln!();
        eprintln!("  <sentence> is a fully qualified name (queue::queue::accept), a");
        eprintln!("  unique trailing part of one (queue::accept), or an index (#12).");
        eprintln!();
        eprintln!("  --dip-normalize   move dips as far left as they will go, fuse");
        eprintln!("                    adjacent dips that end up at the same depth,");
        eprintln!("                    then split each one into a nest of `dip 1`s.");
        eprintln!("  --factor-branches hoist a run of instructions shared by both");
        eprintln!("                    arms of a branch out in front of it.");
        eprintln!("  --annihilate      cancel a drop against the instruction that");
        eprintln!("                    produced the value it drops.");
        eprintln!();
        eprintln!("  Passes compose: each one's output is fed back to the others.");
        process::exit(1);
    }

    let library = load(&positional[0]);
    let root = match resolve_sentence(&library, &positional[1]) {
        Ok(idx) => idx,
        Err(err) => {
            eprintln!("{}", err);
            process::exit(1);
        }
    };

    print_sentence(&library, root, passes);
}

fn load(dir_arg: &str) -> Library {
    let dir = Path::new(dir_arg);
    if !dir.is_dir() {
        eprintln!("Error: '{}' is not a directory", dir_arg);
        process::exit(1);
    }

    let file_path = dir.join("main.hana");
    if !file_path.exists() {
        eprintln!("Error: Directory '{}' does not contain 'main.hana'", dir_arg);
        process::exit(1);
    }

    let code = match fs::read_to_string(&file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading '{}': {}", file_path.display(), err);
            process::exit(1);
        }
    };

    match bytecode::assemble_with_path(&code, file_path.parent()) {
        Ok(lib) => lib,
        Err(err) => {
            eprintln!("Assembly FAILED for '{}':\n{}", file_path.display(), err);
            process::exit(1);
        }
    }
}

/// Accepts an index (`#12` or `12`), an exact name, or an unambiguous suffix.
fn resolve_sentence(library: &Library, ident: &str) -> Result<SentenceIndex, String> {
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
        return Err(format!("'{}' is ambiguous: {}", ident, render_candidates(library, &exact)));
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

/// The most a listing prints before it stops being an aid and starts being a
/// wall; `check` alone matches nearly sixty sentences in the test corpus.
const MAX_LISTED: usize = 15;

fn render_candidates(library: &Library, candidates: &[SentenceIndex]) -> String {
    let mut out = String::from("\n");
    for idx in candidates.iter().take(MAX_LISTED) {
        out.push_str(&format!("  #{:<5} {}\n", usize::from(*idx), library.names[*idx]));
    }
    if candidates.len() > MAX_LISTED {
        out.push_str(&format!("  ... and {} more\n", candidates.len() - MAX_LISTED));
    }
    out
}

fn named_sentence_list(library: &Library) -> String {
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

