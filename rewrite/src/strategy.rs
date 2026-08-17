//! The goal pipeline: what happens to a claim before and after the e-graph.
//!
//! Saturation is the engine, but it is the *last* thing that happens to a
//! goal, not the only thing. The moves in front of it are the ones that keep
//! e-graphs small and failures readable:
//!
//! 1. **Trivial** — the two sides are one term as written.
//! 2. **Peel** — strip what the two compose spines share at either end and
//!    prove what is left. Peeling is *incomplete* — `push 1 ; drop` equals
//!    `push 2 ; drop` and stripping the shared `drop` leaves a false claim —
//!    so a peeled goal that sticks falls back to the whole one.
//! 3. **Descend** — two branches are equal exactly when their arms are equal
//!    pairwise (the stack under the condition is arbitrary, so there is no
//!    context to lose): one subgoal per differing arm, and the decomposition
//!    is complete, unlike peeling.
//! 4. **Saturate** — both sides and any stepping stones go into one e-graph,
//!    every rule fires until the sides meet or the budget runs out.
//! 5. **Inline** — a stuck goal that still holds calls is reopened with every
//!    call unfolded and tried once more. Unfolding is a goal-level decision,
//!    deliberately not a rule: opened calls multiply the term, and the goal
//!    is the only level that knows the cheap route failed.

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
    /// Extract a step-by-step explanation for every close. Costs time on
    /// large proofs, so the report asks for it explicitly.
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

/// How hard a saturation may try.
///
/// A peeled subgoal gets a **probe**: peeling is incomplete, so the narrowed
/// claim may simply be false, and a false goal saturates until the budget
/// runs out — the full budget, spent proving nothing, before the fallback
/// even starts. A probe is the fraction of the budget a wrong turn is
/// allowed to cost. Everything else — the goal as stated, a descend arm, the
/// inlined retry — runs **full**.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Effort {
    Probe,
    Full,
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
        self.prove_from(goal, hints, true, Effort::Full)
    }

    fn prove_from(
        &self,
        goal: &Goal,
        hints: &[Term],
        may_inline: bool,
        effort: Effort,
    ) -> Result<Outcome, Error> {
        if goal.lhs == goal.rhs {
            return Ok(Outcome::Closed(Proof::Trivial));
        }

        // Peel, and fall back: what the peeled goal cannot say, the whole one
        // still can. The peeled attempt runs as a probe — see [`Effort`] —
        // and everything under it stays one.
        if let Some((peeled, prefix, suffix)) = peel(goal)
            && let Outcome::Closed(sub) =
                self.prove_from(&peeled, hints, may_inline, Effort::Probe)?
        {
            return Ok(Outcome::Closed(Proof::Peel {
                prefix,
                suffix,
                sub: Box::new(sub),
            }));
        }

        // Two branches: one subgoal per differing arm, complete.
        if let (
            Term::Branch {
                if_true: t1,
                if_false: e1,
            },
            Term::Branch {
                if_true: t2,
                if_false: e2,
            },
        ) = (&goal.lhs, &goal.rhs)
        {
            let arm = |a: &Term, b: &Term| -> Result<Option<Option<Box<Proof>>>, Error> {
                if a == b {
                    return Ok(Some(None));
                }
                let sub = Goal::aligned(a.clone(), b.clone());
                Ok(match self.prove_from(&sub, hints, may_inline, effort)? {
                    Outcome::Closed(p) => Some(Some(Box::new(p))),
                    Outcome::Stuck(_) => None,
                })
            };
            if let (Some(then_sub), Some(else_sub)) = (arm(t1, t2)?, arm(e1, e2)?) {
                return Ok(Outcome::Closed(Proof::Descend { then_sub, else_sub }));
            }
            // An arm that stuck is not the end: the whole branch goal goes to
            // saturation below, where the arms can help each other.
        }

        match self.saturate(goal, hints, effort) {
            Outcome::Closed(proof) => Ok(Outcome::Closed(proof)),
            Outcome::Stuck(residual) => {
                if may_inline && (has_calls(&goal.lhs) || has_calls(&goal.rhs)) {
                    let opened = Goal::aligned(
                        inline_calls(self.library, &goal.lhs)?,
                        inline_calls(self.library, &goal.rhs)?,
                    );
                    return Ok(match self.prove_from(&opened, hints, false, effort)? {
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
    fn saturate(&self, goal: &Goal, hints: &[Term], effort: Effort) -> Outcome {
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

        // A probe gets a fraction of the budget: it is the price a wrong
        // peel is allowed to cost before the whole goal gets its turn.
        let (iter_limit, node_limit, time_limit) = match effort {
            Effort::Full => (
                self.config.iter_limit,
                self.config.node_limit,
                self.config.time_limit,
            ),
            Effort::Probe => (
                self.config.iter_limit / 3 + 1,
                self.config.node_limit / 5 + 1,
                self.config.time_limit / 8,
            ),
        };

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
            .with_iter_limit(iter_limit)
            .with_node_limit(node_limit)
            .with_time_limit(time_limit)
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
        Outcome::Stuck(Residual {
            lhs: expr_to_term(&best_l, &runner.egraph.analysis.session),
            rhs: expr_to_term(&best_r, &runner.egraph.analysis.session),
            firings,
            stopped: match &runner.stop_reason {
                Some(reason) => format!("{:?}", reason),
                None => "unknown".to_string(),
            },
        })
    }
}

// ---- peeling ----------------------------------------------------------------

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
    fn a_shared_prefix_is_peeled_and_the_rest_proved() {
        let outcome = prove_identity(
            "identity probe { drop 0 is_bool is_bool } = { drop 0 drop 0 push true };",
            "probe",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the goal to close");
        };
        assert!(
            proof.summary().starts_with("peel 1+0"),
            "{}",
            proof.summary()
        );
    }

    #[test]
    fn arms_are_their_own_claims() {
        let outcome = prove_identity(
            "identity probe { branch { is_bool is_bool } { not } } = { branch { is_int is_bool } { not } };",
            "probe",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the goal to close");
        };
        assert!(
            proof.summary().contains("else: as written"),
            "{}",
            proof.summary()
        );
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
    }

    #[test]
    fn peeling_a_false_remainder_falls_back_to_the_whole_goal() {
        // `push 1 ; drop` = `push 2 ; drop`: stripping the shared `drop`
        // leaves a false claim, and the whole goal still closes.
        let outcome = prove_identity(
            "identity probe { push 1 drop 0 } = { push 2 drop 0 };",
            "probe",
        );
        assert!(
            matches!(outcome, Outcome::Closed(_)),
            "the fallback saturation closes what peeling cannot"
        );
    }
}
