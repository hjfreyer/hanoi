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
//! see `rewrite::diagram2::render` — which is what the tactics acted on and
//! what a next step would name. A box is named by what it computes, so it
//! keeps that name across a step that leaves it alone, and two reports of
//! one proof compare — which is what watching a proof means. On a
//! terminal each name is printed with the shortest prefix that tells it
//! apart in bold: that prefix is what an `at` step is written with.
//! `--color` says to emphasise anyway, for a pipe that ends at a reader —
//! `prove ../hana --color | less -R`.
//!
//! `--expand` spends every `by` in full: instead of citing a claim and
//! taking the corpus's word for it, the cited proof's own steps are carried
//! into this goal and re-checked here. Slower by exactly what citing saves,
//! and it is the question citing is an answer to — a citation is only honest
//! if it could have been discharged, and this is what discharges it.
//!
//! Exit codes: `0` every identity proved, `1` a claim is unproved or a
//! proof entry could not attach, `2` the corpus would not build or the
//! arguments were wrong.

use std::collections::{HashMap, HashSet};
use std::io::IsTerminal;
use std::path::PathBuf;
use std::process::ExitCode;

use bytecode::IdentityIndex;
use rewrite::corpus;
use rewrite::diagram2::render;
use rewrite::goal::{Goal, Outcome};
use rewrite::strategy::{Citing, Prover};

struct Args {
    root: PathBuf,
    filter: Option<String>,
    /// Show `id` and `copy` rather than reading through them.
    /// Spend every `by` in full — the cited proof's own steps, carried in
    /// and re-checked here — rather than citing the claim on the corpus's
    /// word.
    expand: bool,
    /// Emphasise addresses whether or not stdout is a terminal, for a pipe
    /// that ends at a reader rather than a log — `| less -R`.
    color: bool,
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("error: {}", message);
            eprintln!("usage: prove <root> [--filter <substr>] [--expand] [--color]");
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
    let mut expand = false;
    let mut color = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--filter" => filter = Some(argv.next().ok_or("--filter needs a value")?),
            "--expand" => expand = true,
            "--color" => color = true,
            other if root.is_none() && !other.starts_with('-') => root = Some(PathBuf::from(other)),
            other => return Err(format!("unrecognized argument: {}", other)),
        }
    }
    Ok(Args {
        root: root.ok_or("no corpus root given")?,
        filter,
        expand,
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
    let mut prover = Prover::new(&corpus.library).citing(if args.expand {
        Citing::Expanded
    } else {
        Citing::OnTrust
    });
    // A proof that cites another claim stands given that claim, so the run
    // owes a last question that no single proof can answer: was everything
    // leaned on actually discharged? A `by` can only name what has already
    // closed, so this cannot fail today — which is exactly why it is cheap to
    // ask, and worth asking where the promise is made rather than assumed.
    let mut closed: HashSet<IdentityIndex> = HashSet::new();
    let mut cited: HashMap<IdentityIndex, Vec<IdentityIndex>> = HashMap::new();
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
        // The claim as stated, kept so a later proof may cite it.
        let stated = goal.clone();
        let strategy = corpus.proofs.get(&idx);
        match prover
            .prove(&mut corpus.terms, goal, strategy)
            .map_err(|e| e.to_string())?
        {
            Outcome::Closed(proof) => {
                proof.cites(cited.entry(idx).or_default());
                closed.insert(idx);
                prover.learn(idx, &stated, &proof);
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

    let mut leaning = Vec::new();
    for (at, on) in &cited {
        for needed in on {
            if !closed.contains(needed) {
                leaning.push(format!(
                    "{} was accepted citing {}, which did not close",
                    corpus.library.identities[*at].name, corpus.library.identities[*needed].name
                ));
            }
        }
    }
    for complaint in &leaning {
        println!("{}", complaint);
    }

    let ok = failed == 0 && corpus.problems.is_empty() && leaning.is_empty();
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
