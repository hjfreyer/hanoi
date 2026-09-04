//! `prove` — discharge every identity a corpus states.
//!
//! ```bash
//! cargo run --bin prove -- ../hana
//! cargo run --bin prove -- ../hana --filter two_spellings
//! ```
//!
//! Per identity, its written strategy runs — the `.hant` beside the `.hana`,
//! see `rewrite::hant` — or the default `diagram` when it has none, and one
//! line reports the outcome.
//!
//! A goal that sticks prints its **residual**: the two sides as graphs —
//! see `rewrite::render` — which is what the tactics acted on and
//! what a next step would name. A box is named by what it computes, so it
//! keeps that name across a step that leaves it alone, and two reports of
//! one proof compare — which is what watching a proof means. On a
//! terminal each name is printed with the shortest prefix that tells it
//! apart in bold: that prefix is what an `at` step is written with.
//! `--color` says to emphasise anyway, for a pipe that ends at a reader —
//! `prove ../hana --color | less -R`.
//!
//! Every close is certified before it is reported: the strategy's draft
//! is flattened to one run of rewrites, and the kernel replays that run
//! against the identity as stated. A `by` carries the cited claim's own
//! certified run in, so nothing is taken on the corpus's word.
//!
//! Exit codes: `0` every identity proved, `1` a claim is unproved or a
//! proof entry could not attach, `2` the corpus would not build or the
//! arguments were wrong.

use std::io::IsTerminal;
use std::path::PathBuf;
use std::process::ExitCode;

use rewrite::corpus;
use rewrite::kernel::goal::Goal;
use rewrite::proof::Outcome;
use rewrite::render;
use rewrite::strategy::Prover;

struct Args {
    root: PathBuf,
    filter: Option<String>,
    /// Emphasise addresses whether or not stdout is a terminal, for a pipe
    /// that ends at a reader rather than a log — `| less -R`.
    color: bool,
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("error: {}", message);
            eprintln!("usage: prove <root> [--filter <substr>] [--color]");
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
    let mut color = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--filter" => filter = Some(argv.next().ok_or("--filter needs a value")?),
            "--color" => color = true,
            other if root.is_none() && !other.starts_with('-') => root = Some(PathBuf::from(other)),
            other => return Err(format!("unrecognized argument: {}", other)),
        }
    }
    Ok(Args {
        root: root.ok_or("no corpus root given")?,
        filter,
        color,
    })
}

/// One row of the residual report: a label, a gutter, and a value that may
/// need more than one line — every line of it written inside the same
/// gutter, so a long reason still reads as one field.
fn field(label: &str, value: &impl std::fmt::Display) {
    let value = value.to_string();
    for (i, line) in value.lines().enumerate() {
        let label = if i == 0 { label } else { "" };
        println!("  {:<24}│ {}", label, line);
    }
}

/// Whether a listing may emphasise the telling prefix of each address:
/// a terminal shows it, a pipe and a log file would show the escapes
/// themselves, and [`NO_COLOR`](https://no-color.org) is a reader saying
/// they would rather not either way.
///
/// `--color` settles it instead: a pager reads escapes as well as a
/// terminal does, and the guess cannot tell that pipe from a log file, so
/// whoever is piping to one says so and is taken at their word — over
/// `NO_COLOR` too, since asking for it here is the later word.
fn emphasis(args: &Args) -> bool {
    args.color || (std::io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none())
}

fn run(args: &Args) -> Result<bool, String> {
    let emphasis = emphasis(args);
    let corpus = corpus::load(&args.root)?;
    for problem in &corpus.problems {
        eprintln!("{}", problem);
    }

    let total = corpus.library.identities.len();
    println!("Proving {} identities...", total);
    // Dependency order, not declaration order: a `by` spends another
    // identity's proof, so that one has to have closed first. A filtered-out
    // identity is still *proved* when something else leans on it — it is only
    // the report that is filtered, since a lemma nobody asked to see is not a
    // reason for the claim that needs it to fail.
    let order = corpus.proving_order()?;
    let mut prover = Prover::new(&corpus.library);
    let mut terms = rewrite::kernel::term::Context::new();
    let (mut passed, mut failed, mut filtered) = (0usize, 0usize, 0usize);
    for idx in order {
        let identity = &corpus.library.identities[idx];
        let name = identity.name.clone();
        let shown = args
            .filter
            .as_ref()
            .is_none_or(|f| name.contains(f.as_str()));
        if !shown {
            filtered += 1;
        }
        // One arena for the whole run: every goal lowered here is a place
        // in it.
        let goal = Goal::of_identity(&mut terms, &corpus.library, idx).map_err(|e| e.to_string())?;
        // The claim as stated, kept so a later proof may cite it.
        let stated = goal.clone();
        let strategy = corpus.proofs.get(&idx);
        match prover
            .prove(&mut terms, goal, strategy)
            .map_err(|e| e.to_string())?
        {
            Outcome::Closed { draft, run } => {
                prover.learn(idx, &stated, &run);
                if !shown {
                    continue;
                }
                passed += 1;
                println!("identity {} ... ok ({})", name, draft.summary());
            }
            Outcome::Stuck(residual) => {
                if !shown {
                    continue;
                }
                failed += 1;
                println!("identity {} ... FAILED", name);
                println!();
                // What the goal *is*, as the tactics left it. Every line
                // names a box a next step could name back.
                for (tag, graph) in [
                    ("left ", &residual.lhs_graph),
                    ("right", &residual.rhs_graph),
                ] {
                    println!("{}", render::listing(graph, tag).bold(emphasis));
                }
                if !residual.path.is_empty() {
                    field("the goal that stuck", &residual.path.join(", "));
                }
                field("the engine stopped", &residual.stopped);
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
