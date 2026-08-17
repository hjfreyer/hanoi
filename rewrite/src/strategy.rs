//! The goal pipeline: what happens to a claim before and after the e-graph.
//!
//! It is short, and the reason it is short is worth stating. Decomposition
//! moves that looked necessary — strip a shared prefix, descend into branch
//! arms — are **congruences**, and an e-graph performs congruences
//! intrinsically: the moment saturation unites `A` with `B`, the parents
//! `P ; A` and `P ; B` are one e-node and merge for free, and a branch
//! merges the moment its arms do. Running those moves *before* saturation
//! bought nothing and cost real money — a peeled subgoal can be false
//! (`push 1 ; drop` = `push 2 ; drop`, minus the shared `drop`), and a
//! false goal saturates to the end of its budget. So the prover does:
//!
//! 1. **Trivial** — the two sides are one term as written.
//! 2. **Saturate** — both sides and any stepping stones into one e-graph,
//!    every rule fires, and a hook closes the run the moment the two roots
//!    meet — saturation has no goal of its own and would happily keep
//!    exploring a closed one.
//! 3. **Inline** — a stuck goal that still holds calls is reopened with
//!    every call unfolded and tried once more. This one is *not* a
//!    congruence — it spends the library's defining equations, and opened
//!    calls multiply the term — so it stays a goal-level decision.
//!
//! Peeling and descending still exist, after the search rather than before
//! it: a stuck goal's residual is **narrowed** — shared affixes stripped,
//! branch pairs with matching other arms descended into — so the report
//! points at where the difference lives instead of printing two whole
//! terms. The same moves are the natural vocabulary for a human or agent
//! directing a proof by hand, which is where they came from.

use std::time::Duration;

use bytecode::Library;
use egg::{AstSize, BackoffScheduler, EGraph, Extractor, Runner};

use crate::goal::{Goal, Outcome, Proof, Residual};
use crate::lang::{Proving, expr_of, expr_to_term};
use crate::rules::rules;
use crate::term::{Error, Term, lower};

/// The saturation budget, and whether to pay for explanations.
#[derive(Debug, Clone)]
pub struct Config {
    pub iter_limit: usize,
    pub node_limit: usize,
    pub time_limit: Duration,
    /// Extract a step-by-step explanation for every close. Explanation
    /// tracking taxes every union, so the e-graph only carries it when
    /// someone asked to read one.
    pub explain: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            iter_limit: 40,
            node_limit: 100_000,
            time_limit: Duration::from_secs(10),
            explain: false,
        }
    }
}

/// Proves goals against one library.
pub struct Prover<'l> {
    pub library: &'l Library,
    pub config: Config,
    /// Built once: a rule is a pattern compiled and a closure boxed, and
    /// every saturation in a run uses the same set.
    rules: Vec<crate::rules::ProofRewrite>,
}

impl<'l> Prover<'l> {
    pub fn new(library: &'l Library, config: Config) -> Self {
        Prover {
            library,
            config,
            rules: rules(),
        }
    }

    /// Runs the pipeline on a goal. `hints` are stepping stones: terms seeded
    /// into the e-graph beside the two sides, for bridging what the rules do
    /// not find on their own.
    pub fn prove(&self, goal: &Goal, hints: &[Term]) -> Result<Outcome, Error> {
        self.prove_from(goal, hints, true)
    }

    fn prove_from(&self, goal: &Goal, hints: &[Term], may_inline: bool) -> Result<Outcome, Error> {
        if goal.lhs == goal.rhs {
            return Ok(Outcome::Closed(Proof::Trivial));
        }

        match self.saturate(goal, hints) {
            Outcome::Closed(proof) => Ok(Outcome::Closed(proof)),
            Outcome::Stuck(residual) => {
                if may_inline && (has_calls(&goal.lhs) || has_calls(&goal.rhs)) {
                    let opened = Goal::aligned(
                        inline_calls(self.library, &goal.lhs)?,
                        inline_calls(self.library, &goal.rhs)?,
                    );
                    return Ok(match self.prove_from(&opened, hints, false)? {
                        Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined(Box::new(sub))),
                        // The residual of the opened goal is the one worth
                        // reading: it is where the search actually died.
                        stuck => stuck,
                    });
                }
                Ok(Outcome::Stuck(residual))
            }
        }
    }

    /// One e-graph, both sides, every rule, until they meet or the budget is
    /// spent.
    fn saturate(&self, goal: &Goal, hints: &[Term]) -> Outcome {
        let mut analysis = Proving::default();
        let lhs = expr_of(&goal.lhs, &mut analysis.session);
        let rhs = expr_of(&goal.rhs, &mut analysis.session);
        let goal_arity = goal.lhs.arity();
        let hint_exprs: Vec<_> = hints
            .iter()
            .filter(|h| h.arity().net() == goal_arity.net())
            .map(|h| {
                let padded = h
                    .clone()
                    .under(goal_arity.inputs.saturating_sub(h.arity().inputs));
                expr_of(&padded, &mut analysis.session)
            })
            .collect();

        // The backoff scheduler exists to slow growth, and the growth here
        // comes from the handful of rules that fire on shape alone. The fact
        // rules match everywhere and *decline* nearly everywhere — banning
        // one on its match count would silence exactly the rare application
        // it exists for — so only the shape rules stay bannable.
        let growth = [
            "assoc-compose",
            "assoc-compose-rev",
            "assoc-par",
            "assoc-par-rev",
            "stair-deep-first",
            "stair-top-first",
            "drop-split-two",
            "drop-split-two-rev",
        ];
        let mut scheduler = BackoffScheduler::default();
        for rule in &self.rules {
            if !growth.contains(&rule.name.as_str()) {
                scheduler = scheduler.do_not_ban(rule.name.as_str());
            }
        }

        // Explanation tracking taxes every union, so the e-graph only carries
        // it when someone asked to read one.
        let egraph = EGraph::new(analysis);
        let egraph = if self.config.explain {
            egraph.with_explanations_enabled()
        } else {
            egraph
        };

        let mut runner = Runner::default()
            .with_scheduler(scheduler)
            .with_iter_limit(self.config.iter_limit)
            .with_node_limit(self.config.node_limit)
            .with_time_limit(self.config.time_limit)
            .with_egraph(egraph)
            .with_expr(&lhs)
            .with_expr(&rhs)
            // Stop the moment the two sides meet: saturation would happily
            // keep exploring an already-closed goal to the end of the budget.
            .with_hook(|runner| {
                let (l, r) = (runner.roots[0], runner.roots[1]);
                if runner.egraph.find(l) == runner.egraph.find(r) {
                    Err("the sides met".to_string())
                } else {
                    Ok(())
                }
            });
        for hint in &hint_exprs {
            runner = runner.with_expr(hint);
        }
        let mut runner = runner.run(&self.rules);

        let (l, r) = (runner.roots[0], runner.roots[1]);
        if runner.egraph.find(l) == runner.egraph.find(r) {
            let explanation = self
                .config
                .explain
                .then(|| runner.explain_equivalence(&lhs, &rhs).get_flat_string());
            return Outcome::Closed(Proof::Saturated {
                iterations: runner.iterations.len(),
                classes: runner.egraph.number_of_classes(),
                explanation,
            });
        }

        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (_, best_l) = extractor.find_best(l);
        let (_, best_r) = extractor.find_best(r);
        drop(extractor);
        let mut firings: Vec<(String, usize)> = Default::default();
        for iteration in &runner.iterations {
            for (rule, count) in &iteration.applied {
                match firings.iter_mut().find(|(name, _)| name == rule.as_str()) {
                    Some((_, total)) => *total += count,
                    None => firings.push((rule.to_string(), *count)),
                }
            }
        }
        firings.sort_by_key(|&(_, count)| std::cmp::Reverse(count));

        // The best spelling of each side, narrowed to where they differ: the
        // congruence moves, run backwards over the wreckage for the report.
        let full_l = expr_to_term(&best_l, &runner.egraph.analysis.session);
        let full_r = expr_to_term(&best_r, &runner.egraph.analysis.session);
        let (path, lhs, rhs) = narrow(full_l, full_r);
        Outcome::Stuck(Residual {
            lhs,
            rhs,
            path,
            firings,
            stopped: match &runner.stop_reason {
                Some(reason) => format!("{:?}", reason),
                None => "unknown".to_string(),
            },
        })
    }
}

// ---- narrowing a residual ---------------------------------------------------

/// Localizes a stuck goal's difference: strips what the two compose spines
/// share at either end, and descends into a branch pair whose *other* arm
/// already matches, until neither move applies. The path records each step,
/// so the report can say "the difference is inside the then arm" instead of
/// printing two whole terms.
///
/// These are the congruence moves the search itself never needs — an e-graph
/// merges parents the moment children meet — read backwards over a failure.
/// Sound for pointing (any remaining difference must live inside what is
/// kept), and only for pointing: the narrowed pair may be equal for reasons
/// the stripped context supplied, which is exactly why peeling was removed
/// from the search path.
fn narrow(lhs: Term, rhs: Term) -> (Vec<String>, Term, Term) {
    let mut path = Vec::new();
    let (mut lhs, mut rhs) = (lhs, rhs);
    loop {
        if let Some((narrowed, prefix, suffix)) = peel(&Goal {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }) {
            path.push(match (prefix, suffix) {
                (p, 0) => format!("past {} shared leading part(s)", p),
                (0, s) => format!("before {} shared trailing part(s)", s),
                (p, s) => format!("between {} shared leading and {} trailing part(s)", p, s),
            });
            lhs = narrowed.lhs;
            rhs = narrowed.rhs;
            continue;
        }
        if let (
            Term::Branch {
                if_true: t1,
                if_false: e1,
            },
            Term::Branch {
                if_true: t2,
                if_false: e2,
            },
        ) = (&lhs, &rhs)
        {
            if t1 == t2 && e1 != e2 {
                path.push("in the else arm".to_string());
                let (l, r) = (e1.as_ref().clone(), e2.as_ref().clone());
                (lhs, rhs) = (l, r);
                continue;
            }
            if e1 == e2 && t1 != t2 {
                path.push("in the then arm".to_string());
                let (l, r) = (t1.as_ref().clone(), t2.as_ref().clone());
                (lhs, rhs) = (l, r);
                continue;
            }
        }
        return (path, lhs, rhs);
    }
}

/// Strips what the two compose spines share at either end. Answers the
/// narrowed goal and how much went, or `None` when nothing does.
fn peel(goal: &Goal) -> Option<(Goal, usize, usize)> {
    let lhs = spine(&goal.lhs);
    let rhs = spine(&goal.rhs);

    let prefix = lhs.iter().zip(&rhs).take_while(|(a, b)| a == b).count();
    // Never peel a whole side away twice over: if the spines are equal the
    // goal was trivial, and the caller handled it.
    let rest = lhs.len().min(rhs.len()) - prefix;
    let suffix = lhs
        .iter()
        .rev()
        .zip(rhs.iter().rev())
        .take(rest)
        .take_while(|(a, b)| a == b)
        .count();
    if prefix + suffix == 0 {
        return None;
    }

    // The width flowing across the cut, read off the last stripped part.
    let boundary = if prefix > 0 {
        lhs[prefix - 1].arity().outputs
    } else {
        goal.lhs.arity().inputs
    };
    let narrowed = Goal {
        lhs: rebuild(&lhs[prefix..lhs.len() - suffix], boundary),
        rhs: rebuild(&rhs[prefix..rhs.len() - suffix], boundary),
    };
    Some((narrowed, prefix, suffix))
}

/// A term's compose spine, outermost first: the flattening of `;`.
fn spine(term: &Term) -> Vec<&Term> {
    fn walk<'t>(term: &'t Term, out: &mut Vec<&'t Term>) {
        match term {
            Term::Compose(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            other => out.push(other),
        }
    }
    let mut out = Vec::new();
    walk(term, &mut out);
    out
}

/// A spine segment back as a term; an empty segment is the identity on the
/// width that flowed across it.
fn rebuild(parts: &[&Term], width_if_empty: usize) -> Term {
    let mut parts = parts.iter();
    let Some(first) = parts.next() else {
        return Term::Id(width_if_empty);
    };
    parts.fold((*first).clone(), |acc, next| {
        Term::Compose(Box::new(acc), Box::new((*next).clone()))
    })
}

// ---- inlining ---------------------------------------------------------------

fn has_calls(term: &Term) -> bool {
    match term {
        Term::Call { .. } => true,
        Term::Compose(a, b) | Term::Par(a, b) => has_calls(a) || has_calls(b),
        Term::Branch { if_true, if_false } => has_calls(if_true) || has_calls(if_false),
        _ => false,
    }
}

/// The term with every call replaced by its body, all the way down.
/// Terminates because recursion is forbidden: the call graph of a library
/// that compiled is acyclic.
fn inline_calls(library: &Library, term: &Term) -> Result<Term, Error> {
    Ok(match term {
        Term::Call { target, .. } => {
            let body = lower(library, *target)?;
            inline_calls(library, &body)?
        }
        Term::Compose(a, b) => Term::Compose(
            Box::new(inline_calls(library, a)?),
            Box::new(inline_calls(library, b)?),
        ),
        Term::Par(a, b) => Term::Par(
            Box::new(inline_calls(library, a)?),
            Box::new(inline_calls(library, b)?),
        ),
        Term::Branch { if_true, if_false } => Term::Branch {
            if_true: Box::new(inline_calls(library, if_true)?),
            if_false: Box::new(inline_calls(library, if_false)?),
        },
        leaf => leaf.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::assemble;

    fn prove_identity(code: &str, name: &str) -> Outcome {
        let library = assemble(code).unwrap();
        let idx = library.identity_by_name(name).unwrap();
        let goal = Goal::of_identity(&library, idx).unwrap();
        Prover::new(&library, Config::default())
            .prove(&goal, &[])
            .unwrap()
    }

    #[test]
    fn a_shared_prefix_is_no_obstacle() {
        // The prefix is a congruence: the e-graph closes the whole goal the
        // moment the differing tails meet, with no peeling step.
        let outcome = prove_identity(
            "identity probe { drop 0 is_bool is_bool } = { drop 0 drop 0 push true };",
            "probe",
        );
        assert!(matches!(outcome, Outcome::Closed(_)));
    }

    #[test]
    fn differing_arms_close_by_congruence() {
        let outcome = prove_identity(
            "identity probe { branch { is_bool is_bool } { not } } = { branch { is_int is_bool } { not } };",
            "probe",
        );
        assert!(matches!(outcome, Outcome::Closed(_)));
    }

    #[test]
    fn a_call_on_the_right_is_opened_when_the_closed_goal_sticks() {
        let outcome = prove_identity(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
            "#,
            "probe",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the goal to close");
        };
        assert!(proof.summary().starts_with("inline"), "{}", proof.summary());
    }

    #[test]
    fn a_false_goal_reports_a_residual() {
        let outcome = prove_identity("identity probe { push 1 } = { push 2 };", "probe");
        let Outcome::Stuck(residual) = outcome else {
            panic!("push 1 is not push 2");
        };
        assert_eq!(format!("{}", residual.lhs), "push 1");
        assert_eq!(format!("{}", residual.rhs), "push 2");
        assert!(residual.path.is_empty());
    }

    #[test]
    fn a_shared_suffix_of_unequal_work_still_closes() {
        // `push 1 ; drop` = `push 2 ; drop`: the claim that made automatic
        // peeling dangerous. Whole-goal saturation closes it directly.
        let outcome = prove_identity(
            "identity probe { push 1 drop 0 } = { push 2 drop 0 };",
            "probe",
        );
        assert!(matches!(outcome, Outcome::Closed(_)));
    }

    #[test]
    fn a_stuck_goal_names_where_the_difference_lives() {
        // A false claim buried in one branch arm behind a shared prefix: the
        // residual walks to it rather than printing the whole terms.
        let outcome = prove_identity(
            "identity probe { drop 0 branch { drop 0 push 1 } { not } } = { drop 0 branch { drop 0 push 2 } { not } };",
            "probe",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the arms differ");
        };
        assert_eq!(format!("{}", residual.lhs), "push 1");
        assert_eq!(format!("{}", residual.rhs), "push 2");
        assert!(
            residual.path.iter().any(|step| step.contains("then arm")),
            "{:?}",
            residual.path
        );
    }
}
