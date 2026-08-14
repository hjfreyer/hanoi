//! Turns one sentence's compiled bytecode into a term, rewrites it by a tactic,
//! and prints it — with every call inlined that you ask to be, both `dip`
//! targets (which includes plain jumps, since `jump` is `Dip(0, s)`) and both
//! arms of every `branch`.
//!
//! The term is an algebra rather than a list: two binary operators, `;` for
//! composition and `par { A } { B }` for two computations side by side, with
//! `id n` the identity that is the unit of both. A `dip` is `par { X } { id }`.
//! See [`ir`].
//!
//! Tactics are built from a set of equations and a handful of combinators for
//! control and traversal, so which rewrites run, in what order, where in the
//! tree, and how many times are all things you say rather than things the tool
//! decides. See `docs/tactics.md`.
//!
//! Two binaries sit on this. `rewrite` is the debugging aid: it takes one
//! sentence and shows you what a tactic does to it. `prove` is the gate: it
//! takes a whole corpus and checks that every `identity` stated in it has a
//! proof that discharges it. They share everything below.
//!
//! **Nothing here is public but the two entry points.** The binaries are
//! `fn main() { exit(rewrite::cli::run()) }` and its `prove` twin, so the
//! calculus — `Rule`, `StepKind`, `Term`, `Matcher`, `Location` — never crosses
//! a crate boundary and never becomes an API. That is not tidiness: a `Tactic`
//! holds `Box<dyn Matcher>`, a `Matcher` plans a `Step`, and a `Step` names a
//! `Rule`, so publishing the outermost of those publishes every equation as
//! part of a signature. This crate exists to host two tools, not to be linked
//! against.

pub mod cli;

/// The `prove` binary's entry point. See [`prove`].
pub fn prove_cli() -> i32 {
    prove::cli()
}

/// The `replay` binary's entry point. See [`replay`].
pub fn replay_cli() -> i32 {
    replay::cli()
}

mod applier;
mod arity;
mod debug;
mod diff;
mod engine;
mod goal;
mod ir;
mod location;
mod matcher;
mod print;
mod program;
mod prove;
mod prover;
mod replay;
mod rule;
mod script;
mod serial;
mod stack;

#[cfg(test)]
mod tests;

use std::fs;
use std::path::Path;

use bytecode::{Library, SourceMap};

use crate::matcher::{count_matcher_names, matcher_by_name, matcher_names, term_matcher_names};
use crate::program::Program;
use crate::rule::Step;
use crate::script::Definitions;

/// Rule firings allowed per run before a tool gives up and shows its work.
pub(crate) const DEFAULT_FUEL: u64 = 1_000_000;

/// What a run was asked to do, shared by both binaries.
pub(crate) struct Options {
    pub(crate) tactic: String,
    pub(crate) fuel: u64,
    pub(crate) trace: bool,
    pub(crate) check: bool,
    pub(crate) stack: bool,
    pub(crate) step: bool,
    pub(crate) show_script: bool,
    /// The widest either column of a side-by-side listing may get.
    pub(crate) width: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            tactic: "default".to_string(),
            fuel: DEFAULT_FUEL,
            trace: false,
            check: false,
            stack: false,
            step: false,
            show_script: false,
            width: diff::DEFAULT_WIDTH,
        }
    }
}

/// Assembles `<dir>/main.hana`, handing back the map along with the library.
///
/// The map is returned rather than consumed because both callers need it after
/// the fact: `rewrite` to render a later error, and `prove` to get from an
/// identity's `FileId` to the file on disk whose `.hant` must prove it.
///
/// The error is already rendered, since rendering it is the last thing the map
/// is needed for when assembly is what failed.
pub(crate) fn load(dir: &Path) -> Result<(SourceMap, Library), String> {
    if !dir.is_dir() {
        return Err(format!("'{}' is not a directory", dir.display()));
    }

    let file_path = dir.join("main.hana");
    if !file_path.exists() {
        return Err(format!(
            "Directory '{}' does not contain 'main.hana'",
            dir.display()
        ));
    }

    let code = fs::read_to_string(&file_path)
        .map_err(|err| format!("Error reading '{}': {}", file_path.display(), err))?;

    let mut sources = SourceMap::new();
    let root = sources.add_path(&file_path, code);
    match bytecode::assemble_source(&mut sources, root, file_path.parent()) {
        Ok(lib) => Ok((sources, lib)),
        Err(err) => Err(sources.render(&err)),
    }
}

// ---------------------------------------------------------------------------
// Listings the binaries print
// ---------------------------------------------------------------------------

/// The `--list-rules` body, as lines.
///
/// This exists so `matcher` can stay private. Asking the registry directly
/// would mean publishing `Matcher`, and through it `PlannedStep`, `Location`,
/// `StepKind`, `Rule`, `Node` and `Direction` — the whole calculus, exported
/// because a CLI wanted to print a table.
pub(crate) fn rule_listing() -> Vec<String> {
    let mut out = Vec::new();
    out.push("rules (place them with `each(...)` or `once(...)`),".to_string());
    out.push("and what `inv(r)` gives for each:".to_string());
    for name in matcher_names() {
        let rule = matcher_by_name(name).expect("it came from the list");
        match rule.inverse() {
            Ok(back) => out.push(format!("  {:<20} inv → {}", name, back.name())),
            Err(_) => out.push(format!("  {:<20} (no backward reading)", name)),
        }
    }
    out.push(String::new());
    out.push("rules narrowed by a number, the way `at(n, r)` is:".to_string());
    for name in count_matcher_names() {
        out.push(format!(
            "  {}(d)              e.g. `at(2, inv({}(0)))`",
            name, name
        ));
    }
    out.push(String::new());
    out.push("rules that take a term, saying what code the window cannot:".to_string());
    for name in term_matcher_names() {
        out.push(format!(
            "  {} {{ ... }}     e.g. `once({} {{ copy }})`",
            name, name
        ));
    }
    out.push(String::new());
    out.push("a term is instructions in braces — `pick n`, `push <lit>`, `id n`,".to_string());
    out.push("`par { ... } { ... }`, `branch { ... } { ... }`, `jump <sentence>`,".to_string());
    out.push("and the argument-free operators. A hidden window is `par { X } { id }`,".to_string());
    out.push("which is what a `dip` compiles to. Naming a sentence needs a program".to_string());
    out.push("loaded, since its arity is what says how wide a window the rule reads.".to_string());
    out.push(String::new());
    out.push("`inv(r)` is r's equation read the other way. Where that reading is".to_string());
    out.push("worth a name it has one — `inv(sink)` is `float` — and where it is".to_string());
    out.push("not, `inv` is the only way to say it. A reading that cannot be".to_string());
    out.push("searched for at all is refused with the reason when the tactic is".to_string());
    out.push("compiled, rather than quietly matching nothing.".to_string());
    out
}

/// The `--list-tactics` body, as lines.
pub(crate) fn tactic_listing(defs: &Definitions) -> Vec<String> {
    let mut out = vec!["tactics:".to_string()];
    for name in defs.names() {
        out.push(format!("  {}", name));
    }
    out.push(String::new());
    out.push("combinators: each, once, at, try, must, repeat, repeat_n, id, fail".to_string());
    out.push("traversals:  children, then, else, left, right, bu, td".to_string());
    out.push("operators:   `a; b` in sequence, `a | b` first that applies".to_string());
    out.push(String::new());
    out.push("aiming:      `at(n, r)` applies r at exactly position n, and".to_string());
    out.push("             `then(k, t)` reaches the then arm of the node at k".to_string());
    out.push("             (bare `then(t)` reaches every one). Composed, they".to_string());
    out.push("             name any window --show-script prints:".to_string());
    out.push("             `then(1, left(2, at(0, sink)))` is `[1.then, 2.left] @0`.".to_string());
    out.push("             An index is a claim: an aimed step that misses is".to_string());
    out.push("             reported and exits non-zero, saying what was there".to_string());
    out.push("             instead. A scan is a question, so `each` and the like".to_string());
    out.push("             stay silent — and an aim inside one is along for the".to_string());
    out.push("             ride. `try(t)` says a miss is acceptable; `must(t)`".to_string());
    out.push("             turns it into a failure that rolls the term back.".to_string());
    out
}

/// A derivation, one step per line, each with its window and replacement.
///
/// The other half of keeping the calculus private: a `Step` is a crate type
/// with private fields, so a caller can hold a `Script` and hand it back here
/// without being able to read what is in it.
///
/// `title` is what the block is called. A proof that met its goal up to
/// inlining has three of these — what the proof did, what unfolding did, and
/// the fold-back — and a reader looking at a hundred unfolds followed by a
/// hundred folds deserves to be told which is which. Numbering restarts per
/// block, each being its own journey.
pub(crate) fn derivation_lines(prog: &Program, title: &str, script: &[Step]) -> Vec<String> {
    let mut out = Vec::new();
    out.push(format!("  {} — {} step(s)", title, script.len()));
    out.push(format!("  {}", "─".repeat(title.chars().count() + 2)));
    if script.is_empty() {
        out.push("  (nothing)".to_string());
    }
    for (i, step) in script.iter().enumerate() {
        out.push(format!("  {:>4}  {}", i, step));
        if let Some((before, after)) = applier::preview(prog, step) {
            out.push(format!("        {}", before));
            out.push(format!("     ⇒  {}", after));
        }
    }
    out
}
