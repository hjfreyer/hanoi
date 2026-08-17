//! `prove` — discharge every identity a corpus states.
//!
//! ```bash
//! cargo run --bin prove -- tests
//! cargo run --bin prove -- tests --filter two_spellings --explain
//! ```
//!
//! Per identity, the goal pipeline runs (see `rewrite::strategy`) and one
//! line reports the outcome; a goal that sticks prints its **residual** — the
//! smallest spelling saturation found for each side, which is what says what
//! to try next. Exit codes: `0` every identity proved, `1` a claim is
//! unproved or a hint is orphaned, `2` the corpus would not build or the
//! arguments were wrong.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use bytecode::{IdentityIndex, SourceMap, assemble_source};
use rewrite::goal::{Goal, Outcome};
use rewrite::hint::{collect_hints, scratch_name, scratch_sentences};
use rewrite::strategy::{Config, Prover};
use rewrite::term::{Term, lower};

struct Args {
    root: PathBuf,
    filter: Option<String>,
    explain: bool,
    config: Config,
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("error: {}", message);
            eprintln!(
                "usage: prove <root> [--filter <substr>] [--explain] [--fuel <nodes>] [--iters <n>]"
            );
            return ExitCode::from(2);
        }
    };
    match run(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(message) => {
            eprintln!("error: {}", message);
            ExitCode::from(2)
        }
    }
}

fn parse_args() -> Result<Args, String> {
    let mut root = None;
    let mut filter = None;
    let mut config = Config::default();
    let mut explain = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--filter" => filter = Some(argv.next().ok_or("--filter needs a value")?),
            "--explain" => explain = true,
            "--fuel" => {
                config.node_limit = argv
                    .next()
                    .ok_or("--fuel needs a value")?
                    .parse()
                    .map_err(|e| format!("--fuel: {}", e))?
            }
            "--iters" => {
                config.iter_limit = argv
                    .next()
                    .ok_or("--iters needs a value")?
                    .parse()
                    .map_err(|e| format!("--iters: {}", e))?
            }
            "--time-limit-secs" => {
                config.time_limit = Duration::from_secs(
                    argv.next()
                        .ok_or("--time-limit-secs needs a value")?
                        .parse()
                        .map_err(|e| format!("--time-limit-secs: {}", e))?,
                )
            }
            other if root.is_none() && !other.starts_with('-') => root = Some(PathBuf::from(other)),
            other => return Err(format!("unrecognized argument: {}", other)),
        }
    }
    config.explain = explain;
    Ok(Args {
        root: root.ok_or("no corpus root given")?,
        filter,
        explain,
        config,
    })
}

fn run(args: &Args) -> Result<bool, String> {
    // The corpus, with every hint's stepping stone appended as a scratch
    // sentence so the real parser and resolver compile it.
    let main_path = args.root.join("main.hana");
    let mut text = std::fs::read_to_string(&main_path)
        .map_err(|e| format!("cannot read {}: {}", main_path.display(), e))?;
    let hints = collect_hints(&args.root)?;
    text.push_str(&scratch_sentences(&hints));

    let mut map = SourceMap::new();
    let file = map.add("main.hana", text);
    let library = assemble_source(&mut map, file, Some(&args.root)).map_err(|e| map.render(&e))?;

    // Resolve every hint to the identity it names; an orphan is an error, not
    // a shrug — a renamed identity must not silently shed its stones.
    let mut orphaned = 0usize;
    let mut stones: HashMap<IdentityIndex, Vec<Term>> = HashMap::new();
    for (i, hint) in hints.iter().enumerate() {
        let scratch = library
            .names
            .iter_enumerated()
            .find(|(_, n)| **n == scratch_name(i))
            .map(|(idx, _)| idx)
            .expect("every hint compiled into a scratch sentence");
        let stone = lower(&library, scratch).map_err(|e| e.to_string())?;
        match library.identity_by_name(&hint.identity) {
            Ok(idx) => stones.entry(idx).or_default().push(stone),
            Err(e) => {
                orphaned += 1;
                eprintln!("orphaned hint {:?}: {}", hint.identity, e);
            }
        }
    }

    let total = library.identities.len();
    println!("Proving {} identities...", total);
    let prover = Prover::new(&library, args.config.clone());
    let (mut passed, mut failed, mut filtered) = (0usize, 0usize, 0usize);
    for (idx, identity) in library.identities.iter_enumerated() {
        if let Some(f) = &args.filter
            && !identity.name.contains(f.as_str())
        {
            filtered += 1;
            continue;
        }
        let goal = Goal::of_identity(&library, idx).map_err(|e| e.to_string())?;
        let empty = Vec::new();
        let hints_for = stones.get(&idx).unwrap_or(&empty);
        match prover.prove(&goal, hints_for).map_err(|e| e.to_string())? {
            Outcome::Closed(proof) => {
                passed += 1;
                println!("identity {} ... ok ({})", identity.name, proof.summary());
                if args.explain {
                    for explanation in proof.explanations() {
                        for line in explanation.lines() {
                            println!("    {}", line);
                        }
                        println!();
                    }
                }
            }
            Outcome::Stuck(residual) => {
                failed += 1;
                println!("identity {} ... FAILED", identity.name);
                println!();
                if !residual.path.is_empty() {
                    println!("  the difference is       │ {}", residual.path.join(", "));
                }
                println!("  what the left came to   │ {}", residual.lhs);
                println!("  what the right came to  │ {}", residual.rhs);
                println!("  the search stopped      │ {}", residual.stopped);
                if !residual.firings.is_empty() {
                    println!("  rule firings");
                    for (rule, count) in residual.firings.iter().take(8) {
                        println!("    {:>6}  {}", count, rule);
                    }
                }
                println!();
            }
        }
    }

    let ok = failed == 0 && orphaned == 0;
    println!();
    println!(
        "identity result: {}. {} passed; {} failed; {} orphaned hints; {} filtered out",
        if ok { "ok" } else { "FAILED" },
        passed,
        failed,
        orphaned,
        filtered
    );
    Ok(ok)
}
