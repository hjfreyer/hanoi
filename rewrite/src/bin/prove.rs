//! `prove` — discharge every identity a corpus states.
//!
//! ```bash
//! cargo run --bin prove -- tests
//! cargo run --bin prove -- tests --filter two_spellings
//! ```
//!
//! Per identity, its written strategy runs — the `.hant` beside the `.hana`,
//! see `rewrite::hant` — or the default `diagram` when it has none, and one
//! line reports the outcome.
//!
//! A goal that sticks prints its **residual**: the two sides as graphs —
//! see `rewrite::diagram2::render` — which is what the tactics acted on and
//! what a next step would name. A box keeps its id across a step, so two
//! reports of one proof compare, which is what watching a proof means.
//!
//! `--terms` prints the sides as terms instead, narrowed to where they
//! differ: that is the language a `via` waypoint is written in, so it is
//! what a stuck goal is *answered* with — ask for it when you are ready to
//! write one. `--boxes` stops reading through the `id` and `copy` the
//! structural laws would delete.
//!
//! Exit codes: `0` every identity proved, `1` a claim is unproved or a
//! proof entry could not attach, `2` the corpus would not build or the
//! arguments were wrong.

use std::path::PathBuf;
use std::process::ExitCode;

use rewrite::corpus;
use rewrite::diagram2::render;
use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::Prover;

struct Args {
    root: PathBuf,
    filter: Option<String>,
    /// Print the sides as terms — the language a `via` is written in —
    /// rather than as graphs.
    terms_only: bool,
    /// Show `id` and `copy` rather than reading through them.
    all_boxes: bool,
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("error: {}", message);
            eprintln!("usage: prove <root> [--filter <substr>] [--terms] [--boxes]");
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
    let mut terms_only = false;
    let mut all_boxes = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--filter" => filter = Some(argv.next().ok_or("--filter needs a value")?),
            "--terms" => terms_only = true,
            "--boxes" => all_boxes = true,
            other if root.is_none() && !other.starts_with('-') => root = Some(PathBuf::from(other)),
            other => return Err(format!("unrecognized argument: {}", other)),
        }
    }
    Ok(Args {
        root: root.ok_or("no corpus root given")?,
        filter,
        terms_only,
        all_boxes,
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
    let mut corpus = corpus::load(&args.root)?;
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
        // One arena for the whole run: the waypoints the corpus read at load
        // time and the goals lowered here are places in it.
        let goal = Goal::of_identity(&mut corpus.terms, &corpus.library, idx)
            .map_err(|e| e.to_string())?;
        let lhs = goal.lhs.clone();
        let strategy = corpus.proofs.get(&idx);
        match prover
            .prove(&mut corpus.terms, goal, strategy)
            .map_err(|e| e.to_string())?
        {
            Outcome::Closed(proof) => {
                // Whether it can be spent is not this loop's business to
                // insist on: most proofs are not runs on one side, and only a
                // `by` naming this one would ever care.
                prover.learn(idx, lhs, &proof);
                if !shown {
                    continue;
                }
                passed += 1;
                println!("identity {} ... ok ({})", name, proof.summary());
            }
            Outcome::Stuck(residual) => {
                if !shown {
                    continue;
                }
                failed += 1;
                println!("identity {} ... FAILED", name);
                println!();
                if args.terms_only {
                    // What to write back. With the library at hand a call
                    // prints as the name a waypoint would have to write,
                    // not as an index.
                    let shown = |term| {
                        corpus
                            .terms
                            .pretty(term, TERM_WIDTH)
                            .named(&corpus.library)
                            .to_string()
                    };
                    if !residual.path.is_empty() {
                        field("the difference is", &residual.path.join(", "));
                    }
                    field("what the left came to", &shown(residual.lhs));
                    field("what the right came to", &shown(residual.rhs));
                } else {
                    // What the goal *is*, as the tactics left it. Every
                    // line names a box a next step could name back.
                    for (tag, graph) in [
                        ("left ", &residual.lhs_graph),
                        ("right", &residual.rhs_graph),
                    ] {
                        let listing = render::listing(graph, tag);
                        let listing = if args.all_boxes {
                            listing.all_boxes()
                        } else {
                            listing
                        };
                        println!("{}", listing);
                    }
                    if !residual.path.is_empty() {
                        field("as terms, they differ", &residual.path.join(", "));
                    }
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
