//! Dumps one sentence's compiled bytecode with every call inlined — both `dip`
//! targets (which includes plain jumps, since `jump` is `Dip(0, s)`) and both
//! arms of every `branch`.
//!
//! A tactic expression then rewrites the result. Tactics are built from six
//! rules and a handful of combinators for control and traversal, so which
//! rewrites run, in what order, where in the tree, and how many times are all
//! things you say rather than things the tool decides. `--list-rules` and
//! `--list-tactics` enumerate what is available, and `--step` walks a tactic
//! one rule firing at a time instead of printing only where it ended up.
//!
//! This is a debugging aid, not a source generator: the output does not parse,
//! because a dipped block operates below its hidden region and so cannot be
//! spliced into the enclosing instruction stream as-is. What it gives you is
//! the whole call tree in one listing instead of a set of `SentenceIndex`
//! references to chase by hand.

mod applier;
mod arity;
mod debug;
mod diff;
mod engine;
mod ir;
mod location;
mod matcher;
mod print;
mod program;
mod rule;
mod script;
mod stack;
#[cfg(test)]
mod tests;

use std::env;
use std::fs;
use std::path::Path;
use std::process;

use bytecode::arity::failure_reachability;
use bytecode::{Library, SentenceIndex};

use crate::engine::Env;
use crate::matcher::{matcher_names, term_matcher_names};
use crate::print::print_sentence;
use crate::program::Program;
use crate::script::{Definitions, PRELUDE};

/// Rule firings allowed per run before the tool gives up and shows its work.
const DEFAULT_FUEL: u64 = 1_000_000;

pub(crate) struct Options {
    pub(crate) tactic: String,
    pub(crate) fuel: u64,
    pub(crate) trace: bool,
    pub(crate) check: bool,
    pub(crate) stack: bool,
    pub(crate) step: bool,
    pub(crate) show_script: bool,
}

fn main() {
    let mut opts = Options {
        tactic: "default".to_string(),
        fuel: DEFAULT_FUEL,
        trace: false,
        check: false,
        stack: false,
        step: false,
        show_script: false,
    };
    let mut tactic_files: Vec<String> = Vec::new();
    let mut positional: Vec<String> = Vec::new();
    let mut list_rules = false;
    let mut list_tactics = false;

    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        let mut value = |name: &str| -> String {
            i += 1;
            match args.get(i) {
                Some(v) => v.clone(),
                None => {
                    eprintln!("{} needs a value", name);
                    process::exit(1);
                }
            }
        };
        match arg {
            "-t" | "--tactic" => opts.tactic = value("-t"),
            "--tactics" => tactic_files.push(value("--tactics")),
            "--fuel" => {
                let raw = value("--fuel");
                opts.fuel = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
                        eprintln!("--fuel needs a number, found '{}'", raw);
                        process::exit(1);
                    }
                };
            }
            "--trace" => opts.trace = true,
            "--step" => opts.step = true,
            "--stack" => opts.stack = true,
            "--check" => opts.check = true,
            "--show-script" => opts.show_script = true,
            "--list-rules" => list_rules = true,
            "--list-tactics" => list_tactics = true,
            flag if flag.starts_with('-') => {
                eprintln!("Unknown flag: {}", flag);
                usage();
                process::exit(1);
            }
            other => positional.push(other.to_string()),
        }
        i += 1;
    }

    let mut defs = Definitions::new();
    if let Err(err) = defs.load(PRELUDE) {
        eprintln!("{}", err.render(PRELUDE));
        eprintln!("(this is a bug in the built-in prelude)");
        process::exit(1);
    }
    for path in &tactic_files {
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(err) => {
                eprintln!("Error reading '{}': {}", path, err);
                process::exit(1);
            }
        };
        if let Err(err) = defs.load(&source) {
            eprint!("{}", err.render(&source));
            process::exit(1);
        }
    }

    if list_rules {
        println!("rules (place them with `each(...)` or `once(...)`):");
        for name in matcher_names() {
            println!("  {}", name);
        }
        println!();
        println!("rules that need a term saying what code to introduce:");
        for name in term_matcher_names() {
            println!(
                "  {} {{ ... }}     e.g. `once({} {{ pick 0 }})`",
                name, name
            );
        }
        return;
    }
    if list_tactics {
        println!("tactics:");
        for name in defs.names() {
            println!("  {}", name);
        }
        println!();
        println!("combinators: each, once, at, try, must, repeat, repeat_n, id, fail");
        println!("traversals:  children, then, else, body, bu, td");
        println!("operators:   `a; b` in sequence, `a | b` first that applies");
        println!();
        println!("aiming:      `at(n, r)` applies r at exactly position n, and");
        println!("             `then(k, t)` reaches the then arm of the node at k");
        println!("             (bare `then(t)` reaches every one). Composed, they");
        println!("             name any window --show-script prints:");
        println!("             `then(1, body(2, at(0, sink)))` is `[1.then, 2.body] @0`.");
        println!("             `must(t)` fails if t changed nothing, so an aimed");
        println!("             step that misses is an error rather than a no-op.");
        return;
    }

    if positional.len() != 2 {
        usage();
        process::exit(1);
    }

    let tactic = match defs.compile(&opts.tactic) {
        Ok(t) => t,
        Err(err) => {
            eprint!("{}", err.render(&opts.tactic));
            process::exit(1);
        }
    };

    let library = load(&positional[0]);
    let root = match resolve_sentence(&library, &positional[1]) {
        Ok(idx) => idx,
        Err(err) => {
            eprintln!("{}", err);
            process::exit(1);
        }
    };

    let prog = Program::new(&library);
    if prog.is_recursive(root) {
        eprintln!("error: '{}' is #[recursive]", library.names[root]);
        eprintln!();
        eprintln!("  This tool expands calls, and a recursive sentence has no finite");
        eprintln!("  expansion. hanoi requires the annotation on every caller of a");
        eprintln!("  recursive sentence, so its absence is what proves expanding a");
        eprintln!("  sentence terminates — and its presence is where that proof stops.");
        process::exit(1);
    }
    // The other half of the precondition the equations are stated under. Both
    // properties are closed over reachability, so refusing the root refuses
    // every node any tree here can come to hold — which is what lets an
    // annihilation ask only for an arity, and what makes running a computation
    // on copies and discarding the results the identity.
    if failure_reachability(&library)[usize::from(root)] {
        eprintln!("error: '{}' can fail", library.names[root]);
        eprintln!();
        eprintln!("  It reaches a `panic`, an `assert` or an `assert_eq`, directly or");
        eprintln!("  through a call. Every law this tool rewrites by assumes the code");
        eprintln!("  it is given is total: that is what lets a computation be moved,");
        eprintln!("  duplicated onto a path that would not have run it, or dropped");
        eprintln!("  along with its results. Rewriting a sentence that can fail would");
        eprintln!("  move, invent or erase the failure.");
        eprintln!();
        eprintln!("  See docs/totality.md. `#[total]` is the annotation that claims");
        eprintln!("  the property; this is the check that answers for every sentence.");
        process::exit(1);
    }

    if opts.step {
        debug::run(&prog, root, &tactic, &opts);
        return;
    }

    let env = Env::new(&prog, opts.fuel, opts.check);
    let script = match print_sentence(root, &tactic, &env, &opts.tactic, opts.stack) {
        Ok(script) => script,
        Err(err) => {
            eprintln!("error: {}", err);
            process::exit(1);
        }
    };

    if opts.show_script {
        println!();
        println!("  derivation — {} step(s)", script.len());
        println!("  ────────────");
        if script.is_empty() {
            println!("  (nothing)");
        }
        for (i, step) in script.iter().enumerate() {
            println!("  {:>4}  {}", i, step);
            if let Some((before, after)) = applier::preview(&prog, step) {
                println!("        {}", before);
                println!("     ⇒  {}", after);
            }
        }
    }

    if opts.trace {
        println!();
        println!("  rule firings");
        println!("  ────────────");
        let histogram = env.histogram();
        if histogram.is_empty() {
            println!("  (none)");
        }
        for (rule, count) in histogram {
            println!("  {:<18} {}", rule, count);
        }
        println!();
        println!("  {} step(s) in all", env.steps_taken());
    }
}

fn usage() {
    eprintln!("Usage: rewrite <directory> <sentence> [-t <tactic>] [options]");
    eprintln!();
    eprintln!("  <sentence> is a fully qualified name (queue::queue::accept), a");
    eprintln!("  unique trailing part of one (queue::accept), or an index (#12).");
    eprintln!();
    eprintln!("  -t, --tactic <expr>  the rewrite to apply. Default `default`,");
    eprintln!("                       which expands every call it safely can.");
    eprintln!("  --tactics <file>     load `tactic NAME = expr;` definitions.");
    eprintln!("  --list-rules         the rules a tactic can place.");
    eprintln!("  --list-tactics       the named tactics currently defined.");
    eprintln!("  --fuel <n>           rule firings before giving up.");
    eprintln!("  --trace              print how often each rule fired.");
    eprintln!("  --step               walk the rewrite one rule firing at a time.");
    eprintln!("  --check              verify every step preserves net stack effect.");
    eprintln!("  --show-script        print the derivation, one step per line.");
    eprintln!(
        "  --stack              show what each slot holds, with equal values sharing a name."
    );
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  rewrite tests 'Pair::check' -t dip_normalize");
    eprintln!("  rewrite tests foo -t 'repeat(bu(each(sink, fuse)))'");
    eprintln!("  rewrite tests foo -t 'annihilate | factoring'");
    eprintln!("  rewrite tests foo -t 'dips; factoring' --step");
}

fn load(dir_arg: &str) -> Library {
    let dir = Path::new(dir_arg);
    if !dir.is_dir() {
        eprintln!("Error: '{}' is not a directory", dir_arg);
        process::exit(1);
    }

    let file_path = dir.join("main.hana");
    if !file_path.exists() {
        eprintln!(
            "Error: Directory '{}' does not contain 'main.hana'",
            dir_arg
        );
        process::exit(1);
    }

    let code = match fs::read_to_string(&file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading '{}': {}", file_path.display(), err);
            process::exit(1);
        }
    };

    let mut sources = bytecode::SourceMap::new();
    let root = sources.add_path(&file_path, code);
    match bytecode::assemble_source(&mut sources, root, file_path.parent()) {
        Ok(lib) => lib,
        Err(err) => {
            eprint!("{}", sources.render(&err));
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

/// The most a listing prints before it stops being an aid and starts being a
/// wall; `check` alone matches nearly sixty sentences in the test corpus.
const MAX_LISTED: usize = 15;

fn render_candidates(library: &Library, candidates: &[SentenceIndex]) -> String {
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
