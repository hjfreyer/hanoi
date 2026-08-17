//! `prove` — discharge every identity a corpus states.
//!
//! ```bash
//! cargo run --bin prove -- tests
//! cargo run --bin prove -- tests --filter two_spellings --explain
//! ```
//!
//! Per identity, its written strategy runs — the `.hant` beside the `.hana`,
//! see `rewrite::hant` — or the default `egraph` when it has none, and one
//! line reports the outcome. A goal that sticks prints its **residual**: the
//! smallest spelling saturation found for each side, narrowed to where the
//! two differ, which is what says what to try next. Exit codes: `0` every
//! identity proved, `1` a claim is unproved or a proof entry could not
//! attach, `2` the corpus would not build or the arguments were wrong.

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use rewrite::corpus;
use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::{Config, Prover};

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

/// How many columns a residual's terms get, past the gutter [`field`] writes.
const TERM_WIDTH: usize = 70;

/// One row of the residual report: a label, a gutter, and a value that may
/// need more than one line — every line of it written inside the same gutter,
/// so a term broken over ten lines still reads as one field.
fn field(label: &str, value: &impl std::fmt::Display) {
    let value = value.to_string();
    for (i, line) in value.lines().enumerate() {
        let label = if i == 0 { label } else { "" };
        println!("  {:<24}│ {}", label, line);
    }
}

fn run(args: &Args) -> Result<bool, String> {
    let corpus = corpus::load(&args.root)?;
    for problem in &corpus.problems {
        eprintln!("{}", problem);
    }

    let total = corpus.library.identities.len();
    println!("Proving {} identities...", total);
    let prover = Prover::new(&corpus.library, args.config.clone());
    let (mut passed, mut failed, mut filtered) = (0usize, 0usize, 0usize);
    for (idx, identity) in corpus.library.identities.iter_enumerated() {
        if let Some(f) = &args.filter
            && !identity.name.contains(f.as_str())
        {
            filtered += 1;
            continue;
        }
        let goal = Goal::of_identity(&corpus.library, idx).map_err(|e| e.to_string())?;
        let strategy = corpus.proofs.get(&idx);
        match prover.prove(&goal, strategy).map_err(|e| e.to_string())? {
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
                    field("the difference is", &residual.path.join(", "));
                }
                // With the library at hand a call prints as the name a
                // waypoint would have to write, not as an index.
                let shown = |term: &rewrite::Term| {
                    term.pretty(TERM_WIDTH).named(&corpus.library).to_string()
                };
                field("what the left came to", &shown(&residual.lhs));
                field("what the right came to", &shown(&residual.rhs));
                field("the search stopped", &residual.stopped);
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

    let ok = failed == 0 && corpus.problems.is_empty();
    println!();
    println!(
        "identity result: {}. {} passed; {} failed; {} problem(s); {} filtered out",
        if ok { "ok" } else { "FAILED" },
        passed,
        failed,
        corpus.problems.len(),
        filtered
    );
    Ok(ok)
}
