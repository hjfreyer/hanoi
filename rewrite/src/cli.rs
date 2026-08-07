//! `rewrite` — dump one sentence's compiled bytecode as a tree and rewrite it.
//!
//! This is a debugging aid, not a source generator: the output does not parse,
//! because a dipped block operates below its hidden region and so cannot be
//! spliced into the enclosing instruction stream as-is. What it gives you is
//! the whole call tree in one listing instead of a set of `SentenceIndex`
//! references to chase by hand.
//!
//! Its sibling is `prove`, which checks the identities a corpus states rather
//! than exploring one sentence. Both sit on the `rewrite` library.

use std::env;
use std::fs;
use std::path::Path;
use std::process;

use crate::engine::Env;
use crate::print::print_sentence;
use crate::program::{Program, resolve_sentence};
use crate::script::{Definitions, PRELUDE};
use crate::{
    Options, check_preconditions, debug, derivation_lines, load, precondition_explanation,
    report_misses, rule_listing, tactic_listing,
};

pub fn run() -> i32 {
    let mut opts = Options::default();
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
        for line in rule_listing() {
            println!("{}", line);
        }
        return 0;
    }
    if list_tactics {
        for line in tactic_listing(&defs) {
            println!("{}", line);
        }
        return 0;
    }

    if positional.len() != 2 {
        usage();
        process::exit(1);
    }

    let (_sources, library) = match load(Path::new(&positional[0])) {
        Ok(pair) => pair,
        Err(err) => {
            eprint!("{}", err);
            if !err.ends_with('\n') {
                eprintln!();
            }
            process::exit(1);
        }
    };
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
    // The two properties every equation is stated under. Both are closed over
    // reachability, so refusing the root refuses every node any tree here can
    // come to hold — which is what lets an annihilation ask only for an arity,
    // and what makes running a computation on copies and discarding the results
    // the identity.
    if let Err(p) = check_preconditions(&prog, root) {
        let lines = precondition_explanation(p, &library.names[root]);
        eprintln!("error: {}", lines[0]);
        for line in &lines[1..] {
            eprintln!("{}", line);
        }
        process::exit(1);
    }

    if opts.step {
        debug::run(&prog, root, &tactic, &opts);
        return 0;
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
        for line in derivation_lines(&prog, &script) {
            println!("{}", line);
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
    if report_misses(&env, true) { 1 } else { 0 }
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
