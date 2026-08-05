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

use bytecode::Library;
use bytecode::arity::failure_reachability;

use crate::engine::{Env, miss_report};
use crate::matcher::{count_matcher_names, matcher_by_name, matcher_names, term_matcher_names};
use crate::print::print_sentence;
use crate::program::{Program, resolve_sentence};
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
        println!("rules (place them with `each(...)` or `once(...)`),");
        println!("and what `inv(r)` gives for each:");
        for name in matcher_names() {
            let rule = matcher_by_name(name).expect("it came from the list");
            match rule.inverse() {
                Ok(back) => println!("  {:<20} inv → {}", name, back.name()),
                Err(_) => println!("  {:<20} (no backward reading)", name),
            }
        }
        println!();
        println!("rules narrowed by a number, the way `at(n, r)` is:");
        for name in count_matcher_names() {
            println!("  {}(d)              e.g. `at(2, inv({}(0)))`", name, name);
        }
        println!();
        println!("rules that take a term, saying what code the window cannot:");
        for name in term_matcher_names() {
            println!(
                "  {} {{ ... }}     e.g. `once({} {{ pick 0 }})`",
                name, name
            );
        }
        println!();
        println!("a term is instructions in braces — `pick n`, `push <lit>`,");
        println!("`dip n {{ ... }}`, `jump <sentence>`, and the argument-free");
        println!("operators. Naming a sentence needs a program loaded, since its");
        println!("arity is what says how wide a window the rule reads.");
        println!();
        println!("`inv(r)` is r's equation read the other way. Where that reading is");
        println!("worth a name it has one — `inv(sink)` is `float` — and where it is");
        println!("not, `inv` is the only way to say it. A reading that cannot be");
        println!("searched for at all is refused with the reason when the tactic is");
        println!("compiled, rather than quietly matching nothing.");
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
        println!("             An index is a claim: an aimed step that misses is");
        println!("             reported and exits non-zero, saying what was there");
        println!("             instead. A scan is a question, so `each` and the like");
        println!("             stay silent — and an aim inside one is along for the");
        println!("             ride. `try(t)` says a miss is acceptable; `must(t)`");
        println!("             turns it into a failure that rolls the term back.");
        return;
    }

    if positional.len() != 2 {
        usage();
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

    let prog = Program::new(&library);

    // After the library, because a term may name a sentence — `share { jump
    // foo }` needs `foo`'s arity to know how wide a window it reads. Everything
    // else about a tactic is still checked here rather than at run time.
    let tactic = match defs.compile_with(&opts.tactic, Some(&prog)) {
        Ok(t) => t,
        Err(err) => {
            eprint!("{}", err.render(&opts.tactic));
            process::exit(1);
        }
    };
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
            // A failure is usually a `must` whose aim missed, and the miss is
            // what says which number was wrong. Written under the failure
            // rather than beside it: there is only one thing wrong here.
            report_misses(&env, false);
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

    // Last, and only after the listing: the tree is what says which number to
    // write instead, so a miss is worth nothing printed above it.
    if report_misses(&env, true) {
        process::exit(1);
    }
}

/// Prints what the run aimed at and did not find. True if there was any.
///
/// An aimed step that misses is not a failure — the tree keeps what the rest of
/// the tactic did — but it is a mistyped number, so the tool says so and exits
/// non-zero. `try(...)` is how you say a miss is acceptable.
fn report_misses(env: &Env, standalone: bool) -> bool {
    let misses = env.misses();
    let report = miss_report(&misses);
    if report.is_empty() {
        return false;
    }
    eprintln!();
    if standalone {
        eprintln!("error: {}", report[0]);
    } else {
        eprintln!("  {}", report[0]);
    }
    for line in &report[1..] {
        eprintln!("{}", line);
    }
    true
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
