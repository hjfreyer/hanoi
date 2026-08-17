//! The interpreter for the strategy language of [`crate::hant`].
//!
//! A proof mirrors a tree of goals. A strategy acts on one goal:
//! manipulations transform it, a splitter (`via`, `descend`) replaces it
//! with independent subgoals each carrying its own strategy, and `egraph`
//! closes it. The default — what an identity with no written proof gets —
//! is `egraph` alone, and nothing else runs unbidden. That division is
//! deliberate, twice over:
//!
//! - **The manipulations the engine performs itself are not offered as
//!   automatic steps.** Peeling an affix and descending into arms are
//!   congruences, and an e-graph performs congruences intrinsically: unite
//!   `A` with `B` and the parents `P ; A` and `P ; B` merge for free. When
//!   this crate ran them automatically they bought nothing and cost real
//!   money — a peeled subgoal can be false, and a false goal saturates to
//!   the end of its budget. As *directed* moves they are a different thing:
//!   the author who writes `peel` is asserting the narrowed claim is the
//!   true one, and an assertion that is wrong fails loudly in a small goal.
//! - **Every written step is a checked claim.** `inline` spends the
//!   library's defining equations; `via` is the transitivity cut — `A = B`
//!   splits into the independent goals `A = C` and `C = B`, each free to
//!   take a different road — so a wrong waypoint fails its half, named,
//!   instead of being quietly ignored. Saturation is allowed neither on
//!   its own.
//!
//! `egraph` runs the engine and fails if the gas runs out. A stuck goal's
//! residual is still **narrowed** for the report — shared affixes stripped,
//! the differing arm entered — because when the engine gives up, where the
//! difference lives is the thing worth printing.

use std::time::Duration;

use bytecode::Library;
use egg::{AstSize, BackoffScheduler, EGraph, Extractor, Runner};

use crate::goal::{Goal, Outcome, Proof, Residual};
use crate::hant::{Step, Strategy, default_strategy};
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

    /// Runs a strategy on a goal — the written one, or the default `egraph`
    /// when the identity carries no proof.
    pub fn prove(&self, goal: &Goal, strategy: Option<&Strategy<Term>>) -> Result<Outcome, Error> {
        let default = default_strategy();
        let strategy = strategy.unwrap_or(&default);
        self.run(strategy, goal.clone())
    }

    /// One strategy on one goal. A goal whose sides are one term as written
    /// is closed before any step runs — at every level, so a `descend` arm
    /// or a cut's side that became trivial needs no steps of its own.
    fn run(&self, strategy: &[Step<Term>], goal: Goal) -> Result<Outcome, Error> {
        if goal.lhs == goal.rhs {
            return Ok(Outcome::Closed(Proof::Trivial));
        }
        let Some((head, rest)) = strategy.split_first() else {
            return Ok(Outcome::Stuck(gave_up(
                goal,
                "the strategy ended with the goal still open",
            )));
        };
        match head {
            Step::Egraph => Ok(self.saturate(&goal)),

            Step::Via {
                waypoint,
                left,
                right,
            } => {
                // The cut is a claim, so a waypoint whose stack effect cannot
                // sit between the sides is refused here, loudly, rather than
                // producing goals no rule could ever close.
                if waypoint.arity().net() != goal.lhs.arity().net() {
                    let why = format!(
                        "the `via` waypoint's net stack change ({}) is not the goal's ({})",
                        waypoint.arity().net(),
                        goal.lhs.arity().net()
                    );
                    return Ok(Outcome::Stuck(gave_up(goal, &why)));
                }
                // Two goals, fully independent from here: each side takes its
                // own road, and proving both proves the whole by transitivity.
                let default = default_strategy();
                let side = |name: &str,
                            strategy: &Option<Strategy<Term>>,
                            sub: Goal|
                 -> Result<Result<Box<Proof>, Residual>, Error> {
                    let strategy = strategy.as_ref().unwrap_or(&default);
                    Ok(match self.run(strategy, sub)? {
                        Outcome::Closed(p) => Ok(Box::new(p)),
                        Outcome::Stuck(mut residual) => {
                            residual
                                .path
                                .insert(0, format!("in the {} half of the cut", name));
                            Err(residual)
                        }
                    })
                };
                let left_sub = match side(
                    "left",
                    left,
                    Goal::aligned(goal.lhs.clone(), waypoint.clone()),
                )? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                let right_sub = match side(
                    "right",
                    right,
                    Goal::aligned(waypoint.clone(), goal.rhs.clone()),
                )? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                Ok(Outcome::Closed(Proof::Cut {
                    left_sub,
                    right_sub,
                }))
            }

            Step::Peel => {
                let Some((narrowed, prefix, suffix)) = peel(&goal) else {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "`peel` found nothing shared to strip",
                    )));
                };
                Ok(match self.run(rest, narrowed)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Peel {
                        prefix,
                        suffix,
                        sub: Box::new(sub),
                    }),
                    Outcome::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, "past the peeled affixes".to_string());
                        Outcome::Stuck(residual)
                    }
                })
            }

            Step::Inline => {
                if !has_calls(&goal.lhs) && !has_calls(&goal.rhs) {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "`inline` found no calls to open",
                    )));
                }
                let opened = Goal::aligned(
                    inline_calls(self.library, &goal.lhs)?,
                    inline_calls(self.library, &goal.rhs)?,
                );
                Ok(match self.run(rest, opened)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined(Box::new(sub))),
                    stuck => stuck,
                })
            }

            Step::Descend { then_arm, else_arm } => {
                let (
                    Term::Branch {
                        if_true: t1,
                        if_false: e1,
                    },
                    Term::Branch {
                        if_true: t2,
                        if_false: e2,
                    },
                ) = (&goal.lhs, &goal.rhs)
                else {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "`descend` needs a branch on both sides",
                    )));
                };
                let arm = |name: &str,
                           strategy: &Option<Strategy<Term>>,
                           a: &Term,
                           b: &Term|
                 -> Result<Result<Option<Box<Proof>>, Residual>, Error> {
                    let sub = Goal::aligned(a.clone(), b.clone());
                    match strategy {
                        Some(s) => Ok(match self.run(s, sub)? {
                            Outcome::Closed(p) => Ok(Some(Box::new(p))),
                            Outcome::Stuck(mut residual) => {
                                residual.path.insert(0, format!("in the {} arm", name));
                                Err(residual)
                            }
                        }),
                        // An arm left out is a claim that it already matches,
                        // and the claim is checked rather than assumed.
                        None if a == b => Ok(Ok(None)),
                        None => Ok(Err(Residual {
                            path: vec![format!("in the {} arm", name)],
                            stopped: format!(
                                "the {} arms are not already equal, and `descend` was given no strategy for them",
                                name
                            ),
                            ..gave_up(sub, "")
                        })),
                    }
                };
                let then_sub = match arm("then", then_arm, t1, t2)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                let else_sub = match arm("else", else_arm, e1, e2)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                Ok(Outcome::Closed(Proof::Descend { then_sub, else_sub }))
            }
        }
    }

    /// One e-graph, both sides, every rule, until they meet or the budget is
    /// spent.
    fn saturate(&self, goal: &Goal) -> Outcome {
        let mut analysis = Proving::default();
        let lhs = expr_of(&goal.lhs, &mut analysis.session);
        let rhs = expr_of(&goal.rhs, &mut analysis.session);

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
            })
            .run(&self.rules);

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

/// A residual for a strategy that failed before any search ran: the goal as
/// it stood, and why the step gave up.
fn gave_up(goal: Goal, why: &str) -> Residual {
    Residual {
        lhs: goal.lhs,
        rhs: goal.rhs,
        path: Vec::new(),
        firings: Vec::new(),
        stopped: why.to_string(),
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
    use crate::hant::parse_hant;
    use bytecode::assemble;

    /// Proves the identity named `name`, with the strategy written as a
    /// `.hant` entry body, or the default when `strategy` is `None`.
    fn prove_with(code: &str, name: &str, strategy: Option<&str>) -> Outcome {
        let library = assemble(code).unwrap();
        let idx = library.identity_by_name(name).unwrap();
        let goal = Goal::of_identity(&library, idx).unwrap();
        let parsed = strategy.map(|s| {
            let entries = parse_hant(&format!("proof {} = {};", name, s)).unwrap();
            crate::hant::map_via(entries.into_iter().next().unwrap().strategy, &mut |body| {
                Err::<Term, String>(format!(
                    "this test writes no via bodies, got {{ {} }}",
                    body
                ))
            })
            .unwrap()
        });
        Prover::new(&library, Config::default())
            .prove(&goal, parsed.as_ref())
            .unwrap()
    }

    fn prove_identity(code: &str, name: &str) -> Outcome {
        prove_with(code, name, None)
    }

    /// The same, for strategies whose `via` bodies must compile — a small
    /// version of what `corpus::load` does with scratch sentences.
    fn prove_with_vias(code: &str, name: &str, strategy: &str) -> Outcome {
        let entries = parse_hant(&format!("proof {} = {};", name, strategy)).unwrap();
        let entry = entries.into_iter().next().unwrap();
        let mut source = code.to_string();
        for (i, body) in crate::hant::via_bodies(&entry.strategy).iter().enumerate() {
            source.push_str(&format!("\nsentence __via_{} {{ {} }}\n", i, body));
        }
        let library = assemble(&source).unwrap();
        let mut next = 0usize;
        let strategy = crate::hant::map_via(entry.strategy, &mut |_body: String| {
            let scratch = format!("__via_{}", next);
            next += 1;
            let idx = library
                .names
                .iter_enumerated()
                .find(|(_, n)| **n == scratch)
                .map(|(idx, _)| idx)
                .expect("the scratch sentence compiled");
            lower(&library, idx).map_err(|e| e.to_string())
        })
        .unwrap();
        let idx = library.identity_by_name(name).unwrap();
        let goal = Goal::of_identity(&library, idx).unwrap();
        Prover::new(&library, Config::default())
            .prove(&goal, Some(&strategy))
            .unwrap()
    }

    #[test]
    fn the_default_is_the_engine_alone() {
        // The prefix is a congruence: the e-graph closes the whole goal the
        // moment the differing tails meet, with no peeling step written.
        let outcome = prove_identity(
            "identity probe { drop 0 is_bool is_bool } = { drop 0 drop 0 push true };",
            "probe",
        );
        assert!(matches!(outcome, Outcome::Closed(Proof::Saturated { .. })));
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
    fn a_call_stays_closed_until_a_proof_says_inline() {
        let code = r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
        "#;
        // The default does not spend the library's definitions…
        let outcome = prove_identity(code, "probe");
        assert!(matches!(outcome, Outcome::Stuck(_)));
        // …a written proof does.
        let outcome = prove_with(code, "probe", Some("inline egraph"));
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the opened goal to close");
        };
        assert_eq!(proof.summary(), "inline; saturated (4 iters, 6 classes)");
    }

    #[test]
    fn a_directed_peel_and_descend_close_and_say_so() {
        let outcome = prove_with(
            "identity probe { drop 0 branch { is_bool is_bool } { not } } = { drop 0 branch { is_int is_bool } { not } };",
            "probe",
            Some("peel descend(then: egraph)"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the goal to close");
        };
        assert!(
            proof
                .summary()
                .starts_with("peel 1+0; descend (then: saturated"),
            "{}",
            proof.summary()
        );
        assert!(
            proof.summary().contains("else: as written"),
            "{}",
            proof.summary()
        );
    }

    #[test]
    fn an_omitted_descend_arm_is_checked_not_assumed() {
        let outcome = prove_with(
            "identity probe { branch { is_bool is_bool } { not } } = { branch { is_int is_bool } { not } };",
            "probe",
            Some("descend(else: egraph)"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the then arms are not already equal");
        };
        assert!(
            residual.stopped.contains("then arms"),
            "{}",
            residual.stopped
        );
    }

    #[test]
    fn a_step_that_does_nothing_fails_loudly() {
        let code = "identity probe { is_bool is_bool } = { drop 0 push true };";
        let Outcome::Stuck(residual) = prove_with(code, "probe", Some("peel egraph")) else {
            panic!("nothing is shared to peel");
        };
        assert!(residual.stopped.contains("`peel`"), "{}", residual.stopped);
        let Outcome::Stuck(residual) = prove_with(code, "probe", Some("inline egraph")) else {
            panic!("there are no calls to open");
        };
        assert!(
            residual.stopped.contains("`inline`"),
            "{}",
            residual.stopped
        );
    }

    #[test]
    fn a_cut_splits_the_goal_and_closes_each_half() {
        // `is_bool ; is_bool` = `is_int ; is_bool`, cut at the normal form
        // both sides reach: two independent goals, each a small saturation.
        let outcome = prove_with_vias(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            "via { drop 0 push true }",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("both halves close");
        };
        assert!(
            proof.summary().starts_with("cut (left: saturated"),
            "{}",
            proof.summary()
        );
    }

    #[test]
    fn a_cut_lets_each_half_take_its_own_road() {
        // The right half compares the waypoint against a call, so it inlines;
        // the left half needs no such thing. Fully independent strategies.
        let outcome = prove_with_vias(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
            "#,
            "probe",
            "via { drop 0 push true } (right: inline egraph)",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("both halves close");
        };
        assert_eq!(
            proof.summary(),
            "cut (left: saturated (4 iters, 6 classes); right: inline; the two sides are one term)"
        );
    }

    #[test]
    fn a_wrong_waypoint_fails_its_half_by_name() {
        // `not` has the right arity but is no midpoint: the left goal,
        // `is_bool ; is_bool` = `not`, is false and says so.
        let outcome = prove_with_vias(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            "via { not }",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the left half is false");
        };
        assert!(
            residual.path.iter().any(|p| p.contains("left half")),
            "{:?}",
            residual.path
        );
    }

    #[test]
    fn a_waypoint_off_the_goal_net_is_refused_loudly() {
        let outcome = prove_with_vias(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            "via { push 1 }",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the waypoint's net does not fit");
        };
        assert!(
            residual.stopped.contains("net stack change"),
            "{}",
            residual.stopped
        );
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
