//! Working a goal from the command line: `rewrite <dir> <identity>`.
//!
//! This is where a proof gets written. `prove` decides whether a `.hant` already
//! discharges every claim the corpus states; this is the loop you are in before
//! there is anything to decide — a goal, a strategy off the command line, and
//! the smallest disagreement left over when it does not close.
//!
//! **What closes here is what goes in the `.hant`, character for character.**
//! `-t` is a proof body, resolved exactly as a `proof` is, so a bare tactic is
//! the blind reading and `normalize(cleanup)` is a strategy. Nothing has to be
//! translated on the way into the file, which is the whole point of running the
//! search from out here.
//!
//! It differs from `prove` in the one way the two tools have always differed:
//! **`rewrite` explores and `prove` decides.**
//!
//! - **A goal that does not close is not a failure.** It is the normal state
//!   while you are working, and the residual is the answer rather than the
//!   complaint. The exit code says whether the *run* was clean, not whether the
//!   claim is true.
//! - **A miss is a diagnostic**, printed under the listing rather than in place
//!   of it — because the listing is what tells you which number to write
//!   instead. `prove` fails a proof over the same miss, and both read the same
//!   `Solved::misses`; what differs is only what they do about it.
//!
//! There is no positional for a *sentence*. Everything here is about a goal, so
//! a term worth looking at is a term worth stating an identity over — and a
//! reflexive one, `identity probe { jump X } = { jump X };`, gives back the old
//! one-sided listing with a diff against where you started thrown in.

use bytecode::{Identity, SentenceIndex};

use crate::debug;
use crate::engine::{Tactic, miss_report};
use crate::ir::{Term, build_padded};
use crate::print::render_nodes;
use crate::program::Program;
use crate::prover::{self, Goal, Solved, Unproved};

use crate::{Options, derivation_lines};

/// The run was clean, whether or not the goal closed.
pub(crate) const OK: i32 = 0;
/// An aimed step missed, or the strategy could not be run at all.
pub(crate) const PROBLEM: i32 = 1;

/// Works one identity's goal, writing the report to `out`.
///
/// Writing to a `Write` rather than to stdout is what makes every outcome
/// testable without a subprocess, which is the arrangement `prove::run` already
/// uses for the same reason.
pub(crate) fn run(
    prog: &Program,
    identity: &Identity,
    strategy: &prover::Strategy,
    inline: &Tactic,
    opts: &Options,
    out: &mut dyn std::io::Write,
) -> std::io::Result<i32> {
    let (lhs, rhs) = crate::ir::goal_terms(prog, identity.lhs, identity.rhs);
    let goal = Goal::root(lhs.into_spine(), rhs.into_spine());
    let (found, firings) = prover::work(prog, inline, &goal, strategy, opts.fuel, opts.check);
    let solved = match found {
        Ok(solved) => solved,
        Err(Unproved::Residual(residual)) => {
            // Not an error. This is the answer: the smallest piece of the claim
            // still standing, which is what says what to try next.
            writeln!(out)?;
            for line in residual.headline() {
                writeln!(out, "{}", line)?;
            }
            writeln!(out)?;
            for line in residual.diff(prog, opts.stack, opts.width) {
                writeln!(out, "{}", line)?;
            }
            // A route that did not work out still cost what it cost, and what it
            // cost is often the thing you were asking about.
            if opts.trace {
                writeln!(out)?;
                for line in trace(&firings, None) {
                    writeln!(out, "{}", line)?;
                }
            }
            return Ok(OK);
        }
        Err(err) => {
            for line in broken(&err) {
                writeln!(out, "{}", line)?;
            }
            return Ok(PROBLEM);
        }
    };

    if opts.step {
        // The stepper walks a script from a sentence, and each side of an
        // identity *is* one — so a decomposed derivation needs nothing special
        // to walk. The backward half of a `normalize` and the lifted steps of a
        // `descend` go past like any others.
        debug::run(prog, identity.lhs, solved.script.clone(), None, opts);
        return Ok(OK);
    }

    writeln!(out, "closed — {}", solved.closed.summary())?;
    writeln!(out)?;
    // Where the two sides met. For a reflexive goal this is the listing, which
    // is how looking at a compiled term survives having no positional of its
    // own.
    for line in met(prog, identity.lhs, &solved, opts) {
        writeln!(out, "{}", line)?;
    }

    if opts.show_script {
        writeln!(out)?;
        for line in derivation_lines(prog, "derivation", &solved.script) {
            writeln!(out, "{}", line)?;
        }
    }

    if opts.trace {
        writeln!(out)?;
        for line in trace(&firings, Some(solved.script.len())) {
            writeln!(out, "{}", line)?;
        }
    }

    // Last, and only after the listing: the tree is what says which number to
    // write instead, so a miss is worth nothing printed above it.
    if solved.misses.is_empty() {
        return Ok(OK);
    }
    writeln!(out)?;
    for line in miss_report(&solved.misses) {
        writeln!(out, "{}", indented(&line))?;
    }
    Ok(PROBLEM)
}

/// The term the two sides met at.
///
/// The left-hand side with as much of the derivation applied as gets it to the
/// middle — which for a strategy that drove both sides is *neither* side as
/// written, and is the term worth looking at. Running the whole script would
/// land back on the right-hand side, which the goal already said.
fn met(prog: &Program, lhs: SentenceIndex, solved: &Solved, opts: &Options) -> Vec<String> {
    let mut body = tree(prog, lhs);
    let upto = solved.closed.met_after(solved.script.len());
    if let Err(err) =
        crate::applier::apply_script_seq(prog, &mut body, &solved.script[..upto], opts.check)
    {
        // The final replay is `prove`'s job, and a script that will not apply is
        // a bug rather than a wrong claim — say so instead of printing a tree
        // that is not the one the derivation describes.
        return vec![format!("  the derivation does not apply: {}", err)];
    }
    render_nodes(prog, &body, opts.stack, true, true)
}

/// How often each rule fired, most frequent first.
///
/// The counts are the **search's** and the step total is the **derivation's**,
/// and the gap between them is the reading worth having: a tactic thrashing
/// between two rules that undo each other shows up as a large count against a
/// small derivation, which is what you want to see when a proof costs more than
/// it should. A goal that did not close has no derivation to count, so the total
/// is left off rather than guessed at.
fn trace(firings: &[(&'static str, usize)], steps: Option<usize>) -> Vec<String> {
    let mut out = vec!["  rule firings".to_string(), "  ────────────".to_string()];
    if firings.is_empty() {
        out.push("  (none)".to_string());
    }
    for (rule, count) in firings {
        out.push(format!("  {:<18} {}", rule, count));
    }
    if let Some(steps) = steps {
        out.push(String::new());
        out.push(format!("  {} step(s) in all", steps));
    }
    out
}

/// A run that could not happen, as opposed to a goal that did not close.
fn broken(err: &Unproved) -> Vec<String> {
    match err {
        Unproved::Ran(err) => vec![format!("error: the strategy did not run: {}", err)],
        Unproved::Inlining(which, err) => vec![
            format!(
                "error: unfolding the {} side did not finish: {}",
                which, err
            ),
            String::new(),
            "  A strategy that meets in the middle drives both sides, so both".to_string(),
            "  have to settle.".to_string(),
        ],
        Unproved::Replay(why) => vec![
            format!("error: the derivation does not replay: {}", why),
            String::new(),
            "  That is a bug in the rewriter, not in the strategy.".to_string(),
        ],
        // Handled by the caller, which prints it as an answer rather than an
        // error.
        Unproved::Residual(_) => vec!["error: the goal did not close".to_string()],
    }
}

fn tree(prog: &Program, root: SentenceIndex) -> Vec<Term> {
    build_padded(prog, root).into_spine()
}

/// Two spaces in front of a line, except an empty one — which would otherwise
/// become trailing whitespace in the report.
fn indented(line: &str) -> String {
    if line.is_empty() {
        String::new()
    } else {
        format!("  {}", line)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::script::{Definitions, PRELUDE};
    use bytecode::Library;

    /// A corpus, a goal, and a strategy: the whole of what this module does.
    fn work(source: &str, strategy: &str, opts: Options) -> (i32, String) {
        let library: Library = bytecode::assemble(source).unwrap_or_else(|e| panic!("{}", e));
        let prog = Program::new(&library);
        let mut defs = Definitions::new();
        defs.load(PRELUDE).expect("the prelude parses");
        let inline = defs
            .compile_with("unfold_all", Some(&prog))
            .expect("the prelude compiles");
        let compiled = defs
            .compile_proof(strategy, Some(&prog))
            .unwrap_or_else(|e| panic!("{}", e.render(strategy)));
        let index = library
            .identity_by_name("foo")
            .unwrap_or_else(|e| panic!("{}", e));

        let mut out = Vec::new();
        let code = run(
            &prog,
            &library.identities[index],
            &compiled,
            &inline,
            &opts,
            &mut out,
        )
        .expect("writing to a Vec cannot fail");
        (code, String::from_utf8(out).expect("the report is utf-8"))
    }

    fn with(strategy: &str) -> Options {
        Options {
            tactic: strategy.to_string(),
            ..Options::default()
        }
    }

    const TWO_SPELLINGS: &str = "identity foo { is_bool is_bool } = { is_int is_bool };";

    #[test]
    fn a_strategy_that_closes_says_so_and_shows_where_they_met() {
        let (code, report) = work(
            TWO_SPELLINGS,
            "normalize(cleanup)",
            with("normalize(cleanup)"),
        );
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("closed — 4 steps meeting"), "{}", report);
        // The term both sides reached, which is neither side as written.
        assert!(report.contains("push true"), "{}", report);
    }

    /// The loop's normal state, and the reason the exit code is 0: a goal left
    /// standing is an answer, not a complaint.
    #[test]
    fn a_goal_that_does_not_close_is_reported_rather_than_failed() {
        let (code, report) = work(TWO_SPELLINGS, "cleanup", with("cleanup"));
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("what it reached"), "{}", report);
        assert!(report.contains("is_int"), "{}", report);
        assert!(!report.contains("error"), "{}", report);
    }

    /// With the default strategy the two sides are shown as written, which is
    /// what a bare `rewrite <dir> <identity>` is for.
    #[test]
    fn the_default_strategy_shows_the_goal() {
        let (code, report) = work(TWO_SPELLINGS, "default", with("default"));
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("what it reached"), "{}", report);
        assert!(report.contains("is_bool"), "{}", report);
        assert!(report.contains("is_int"), "{}", report);
    }

    /// A residual found by decomposition says which arm it is in, which is the
    /// narrowing that makes the loop worth running.
    #[test]
    fn a_residual_names_the_arm_it_is_in() {
        let (code, report) = work(
            "identity foo { branch { not } { drop 0 push 1 } } \
             = { branch { not } { drop 0 push 2 } };",
            "descend(then: exact(id))",
            with("descend(then: exact(id))"),
        );
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("inside [0.else]"), "{}", report);
        assert!(report.contains("push 1"), "{}", report);
    }

    /// A reflexive goal is how a term with nothing to prove about it still gets
    /// looked at: the old one-sided listing, plus a diff against where it
    /// started.
    #[test]
    fn a_reflexive_goal_is_an_exploration_vehicle() {
        const PROBE: &str = "function f { drop 0 push true }\n\
                             identity foo { jump f } = { jump f };";

        // Closed by `id`, and what it shows is the term itself.
        let (code, report) = work(PROBE, "id", with("id"));
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("closed — 0 steps"), "{}", report);
        assert!(report.contains("jump"), "{}", report);

        // Under a tactic that changes the left, the residual view is
        // after-against-before.
        let (code, report) = work(PROBE, "unfold_all", with("unfold_all"));
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("push true"), "{}", report);
    }

    /// The divergence from `prove`, which fails a proof over the same miss.
    #[test]
    fn a_miss_is_a_diagnostic_printed_under_the_listing() {
        let (code, report) = work(
            "identity foo { is_bool is_bool } = { drop 0 push true };",
            "at(9, sink); cleanup",
            with("at(9, sink); cleanup"),
        );
        assert_eq!(code, PROBLEM, "{}", report);
        // The listing is still there, and the miss is under it.
        assert!(report.contains("closed"), "{}", report);
        assert!(report.contains("matched nothing"), "{}", report);
        let listing = report.find("closed").expect("a listing");
        let miss = report.find("matched nothing").expect("a miss");
        assert!(listing < miss, "the miss belongs under the listing");
    }

    #[test]
    fn a_strategy_that_runs_out_of_fuel_says_so() {
        let (code, report) = work(
            TWO_SPELLINGS,
            "normalize(cleanup)",
            Options {
                // `cleanup` needs two firings a side, so one is not enough.
                fuel: 1,
                ..with("normalize(cleanup)")
            },
        );
        assert_eq!(code, PROBLEM, "{}", report);
        assert!(report.contains("out of fuel"), "{}", report);
    }
}
