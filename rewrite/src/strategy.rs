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

use bytecode::{Library, SentenceIndex};
use egg::{AstSize, BackoffScheduler, EGraph, Extractor, Runner};

use std::collections::HashMap;

use crate::goal::{Goal, Outcome, Proof, Residual};
use crate::hant::{Body, Step, Strategy, default_strategy};
use crate::lang::{Proving, expr_of, expr_to_term, pattern_of};
use crate::rules::rules;
use crate::term::{Arity, Error, Term, lower};

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
    pub fn prove(&self, goal: &Goal, strategy: Option<&Strategy<Body>>) -> Result<Outcome, Error> {
        let default = default_strategy();
        let strategy = strategy.unwrap_or(&default);
        self.run(strategy, goal.clone())
    }

    /// One strategy on one goal. A goal whose sides are one term as written
    /// is closed before any step runs — at every level, so a `descend` arm
    /// or a cut's side that became trivial needs no steps of its own.
    fn run(&self, strategy: &[Step<Body>], goal: Goal) -> Result<Outcome, Error> {
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
                let Body::Stone(waypoint) = waypoint else {
                    unreachable!("the loader reads a via body as a stone");
                };
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
                            strategy: &Option<Strategy<Body>>,
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

            Step::Solve {
                vars,
                template,
                right,
            } => {
                let Body::Template { term, holes } = template else {
                    unreachable!("the loader reads a solve body as a template");
                };
                // The template stands where a waypoint would, so it owes the
                // same net stack change — checked with the holes at their
                // declared arities, before any search runs.
                if term.arity().net() != goal.lhs.arity().net() {
                    let why = format!(
                        "the `solve` template's net stack change ({}) is not the goal's ({})",
                        term.arity().net(),
                        goal.lhs.arity().net()
                    );
                    return Ok(Outcome::Stuck(gave_up(goal, &why)));
                }

                // One saturation: the goal's two sides, and a pattern built
                // in the same session so its leaves name the same values.
                let mut analysis = Proving::default();
                let lhs = expr_of(&goal.lhs, &mut analysis.session);
                let rhs = expr_of(&goal.rhs, &mut analysis.session);
                let hole_vars: HashMap<bytecode::SentenceIndex, egg::Var> = holes
                    .iter()
                    .map(|(name, idx)| {
                        (
                            *idx,
                            format!("?{}", name).parse().expect("a var spelled ?x"),
                        )
                    })
                    .collect();
                let pattern = pattern_of(term, &hole_vars, &mut analysis.session);
                let runner = self.run_engine(analysis, &lhs, &rhs);

                // The goal may simply have closed while we were solving.
                let (l, r) = (runner.roots[0], runner.roots[1]);
                if runner.egraph.find(l) == runner.egraph.find(r) {
                    return Ok(self.judge(runner, &lhs, &rhs));
                }

                // Match the template against the left side's class. The match
                // both finds the fills and *is* the proof of the left half:
                // the instantiated template's nodes live in that class. First
                // match at the declared arities wins — recorded in the proof,
                // so a different match after a rule-set change is visible.
                use egg::Searcher;
                let matches = pattern.search_eclass(&runner.egraph, runner.egraph.find(l));
                let extractor = Extractor::new(&runner.egraph, AstSize);
                let mut fills: Option<Vec<(String, Term)>> = None;
                'subst: for subst in matches.iter().flat_map(|m| m.substs.iter()) {
                    let mut candidate = Vec::new();
                    for ((name, (inputs, outputs)), (_, idx)) in vars.iter().zip(holes) {
                        let var = hole_vars[idx];
                        let Some(&class) = subst.get(var) else {
                            continue 'subst;
                        };
                        if runner.egraph[class].data.arity != Arity::new(*inputs, *outputs) {
                            continue 'subst;
                        }
                        let (_, best) = extractor.find_best(class);
                        candidate.push((
                            name.clone(),
                            expr_to_term(&best, &runner.egraph.analysis.session),
                        ));
                    }
                    fills = Some(candidate);
                    break;
                }
                drop(extractor);
                let Some(fills) = fills else {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "the template matched nothing in the left side's class at the declared arities",
                    )));
                };

                // The filled-in waypoint, and the one goal left: its right half.
                let by_hole: HashMap<bytecode::SentenceIndex, &Term> = holes
                    .iter()
                    .zip(&fills)
                    .map(|((_, idx), (_, fill))| (*idx, fill))
                    .collect();
                let filled = substitute_holes(term, &by_hole);
                let fills_shown = fills
                    .iter()
                    .map(|(name, term)| format!("?{} = {}", name, term))
                    .collect::<Vec<_>>()
                    .join(", ");
                let default = default_strategy();
                let right = right.as_ref().unwrap_or(&default);
                Ok(
                    match self.run(right, Goal::aligned(filled, goal.rhs.clone()))? {
                        Outcome::Closed(p) => Outcome::Closed(Proof::Solved {
                            fills,
                            right_sub: Box::new(p),
                        }),
                        Outcome::Stuck(mut residual) => {
                            residual.path.insert(
                                0,
                                format!("in the right half of the solve, with {}", fills_shown),
                            );
                            Outcome::Stuck(residual)
                        }
                    },
                )
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

            Step::Symm => {
                // Equality is symmetric, so this claims nothing; it moves
                // which side the asymmetric steps read. A residual carries
                // the swap in its path, because "the left came to" means the
                // left of the goal that failed, not the left of the identity.
                let swapped = Goal {
                    lhs: goal.rhs,
                    rhs: goal.lhs,
                };
                Ok(match self.run(rest, swapped)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Swapped(Box::new(sub))),
                    Outcome::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, "with the sides swapped".to_string());
                        Outcome::Stuck(residual)
                    }
                })
            }

            Step::Inline(label) => {
                // A label opens one sentence's calls and leaves the rest shut,
                // which is what lets a waypoint keep naming the calls it does
                // not care about: unfolding everything means spelling
                // everything out on the other side of the cut.
                let only = match label {
                    None => None,
                    Some(Body::Target(idx)) => Some(*idx),
                    Some(_) => unreachable!("the loader reads an inline label as a target"),
                };
                if !has_calls(&goal.lhs, only) && !has_calls(&goal.rhs, only) {
                    let why = match only {
                        None => "`inline` found no calls to open".to_string(),
                        Some(idx) => format!(
                            "`inline({})` found no call to it here",
                            self.library.names[idx]
                        ),
                    };
                    return Ok(Outcome::Stuck(gave_up(goal, &why)));
                }
                let opened = Goal::aligned(
                    inline_calls(self.library, &goal.lhs, only)?,
                    inline_calls(self.library, &goal.rhs, only)?,
                );
                let target = only.map(|idx| self.library.names[idx].clone());
                Ok(match self.run(rest, opened)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined {
                        target,
                        sub: Box::new(sub),
                    }),
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
                           strategy: &Option<Strategy<Body>>,
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
        let runner = self.run_engine(analysis, &lhs, &rhs);
        self.judge(runner, &lhs, &rhs)
    }

    /// Builds and runs the engine on a goal's two expressions.
    fn run_engine(
        &self,
        analysis: Proving,
        lhs: &egg::RecExpr<crate::lang::HanaLang>,
        rhs: &egg::RecExpr<crate::lang::HanaLang>,
    ) -> Runner<crate::lang::HanaLang, Proving> {
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

        Runner::default()
            .with_scheduler(scheduler)
            .with_iter_limit(self.config.iter_limit)
            .with_node_limit(self.config.node_limit)
            .with_time_limit(self.config.time_limit)
            .with_egraph(egraph)
            .with_expr(lhs)
            .with_expr(rhs)
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
            .run(&self.rules)
    }

    /// Reads the verdict off a finished run: the sides met, or the residual.
    fn judge(
        &self,
        mut runner: Runner<crate::lang::HanaLang, Proving>,
        lhs: &egg::RecExpr<crate::lang::HanaLang>,
        rhs: &egg::RecExpr<crate::lang::HanaLang>,
    ) -> Outcome {
        let (l, r) = (runner.roots[0], runner.roots[1]);
        if runner.egraph.find(l) == runner.egraph.find(r) {
            let explanation = self
                .config
                .explain
                .then(|| runner.explain_equivalence(lhs, rhs).get_flat_string());
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

/// The template with every hole replaced by the term the match bound it to.
fn substitute_holes(term: &Term, fills: &HashMap<bytecode::SentenceIndex, &Term>) -> Term {
    match term {
        Term::Call { target, .. } if fills.contains_key(target) => fills[target].clone(),
        Term::Compose(a, b) => Term::Compose(
            Box::new(substitute_holes(a, fills)),
            Box::new(substitute_holes(b, fills)),
        ),
        Term::Par(a, b) => Term::Par(
            Box::new(substitute_holes(a, fills)),
            Box::new(substitute_holes(b, fills)),
        ),
        Term::Branch { if_true, if_false } => Term::Branch {
            if_true: Box::new(substitute_holes(if_true, fills)),
            if_false: Box::new(substitute_holes(if_false, fills)),
        },
        leaf => leaf.clone(),
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

/// Whether there is anything for an `inline` to open: any call at all, or a
/// call to the one sentence a label named.
fn has_calls(term: &Term, only: Option<SentenceIndex>) -> bool {
    match term {
        Term::Call { target, .. } => only.is_none_or(|idx| *target == idx),
        Term::Compose(a, b) | Term::Par(a, b) => has_calls(a, only) || has_calls(b, only),
        Term::Branch { if_true, if_false } => has_calls(if_true, only) || has_calls(if_false, only),
        _ => false,
    }
}

/// The term with calls replaced by their bodies: every call, all the way down,
/// or every call to `only` and no others.
///
/// The unlabelled walk terminates because recursion is forbidden — the call
/// graph of a library that compiled is acyclic — and for the same reason the
/// labelled one needs no recursion into the body it just opened: nothing a
/// sentence calls can reach that sentence again.
fn inline_calls(
    library: &Library,
    term: &Term,
    only: Option<SentenceIndex>,
) -> Result<Term, Error> {
    let recur = |t: &Term| inline_calls(library, t, only);
    Ok(match term {
        Term::Call { target, .. } => match only {
            None => recur(&lower(library, *target)?)?,
            Some(idx) if *target == idx => lower(library, *target)?,
            Some(_) => term.clone(),
        },
        Term::Compose(a, b) => Term::Compose(Box::new(recur(a)?), Box::new(recur(b)?)),
        Term::Par(a, b) => Term::Par(Box::new(recur(a)?), Box::new(recur(b)?)),
        Term::Branch { if_true, if_false } => Term::Branch {
            if_true: Box::new(recur(if_true)?),
            if_false: Box::new(recur(if_false)?),
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
    /// `.hant` entry body, or the default when `strategy` is `None` — reading
    /// `via` and `solve` bodies exactly as `corpus::load` does.
    fn prove_with(code: &str, name: &str, strategy: Option<&str>) -> Outcome {
        let entries = strategy
            .map(|s| parse_hant(&format!("proof {} = {};", name, s)).unwrap())
            .unwrap_or_default();
        let library = assemble(code).unwrap();
        let strategy = entries
            .first()
            .map(|e| crate::corpus::attach(&e.strategy, &library).unwrap());
        let idx = library.identity_by_name(name).unwrap();
        let goal = Goal::of_identity(&library, idx).unwrap();
        Prover::new(&library, Config::default())
            .prove(&goal, strategy.as_ref())
            .unwrap()
    }

    fn prove_identity(code: &str, name: &str) -> Outcome {
        prove_with(code, name, None)
    }

    fn prove_with_vias(code: &str, name: &str, strategy: &str) -> Outcome {
        prove_with(code, name, Some(strategy))
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
    fn a_labelled_inline_opens_one_sentence_and_leaves_the_rest_shut() {
        // `outer` calls `inner`. Opening `outer` alone leaves the call to
        // `inner` standing, so the waypoint can name it rather than spell it,
        // and the summary says which sentence was spent.
        let code = r#"
            #[arity(1,1)] sentence inner { drop 0 push true }
            #[arity(1,1)] sentence outer { jump crate::inner }
            identity probe { jump crate::outer } = { drop 0 push true };
        "#;
        let outcome = prove_with(
            code,
            "probe",
            Some("inline(outer) via { call inner } (right: inline)"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the opened goal is `call inner` against the claim");
        };
        assert_eq!(
            proof.summary(),
            "inline outer; cut (left: the two sides are one term; \
             right: inline; the two sides are one term)"
        );
    }

    #[test]
    fn a_label_naming_an_uncalled_sentence_fails_loudly() {
        let code = r#"
            #[arity(1,1)] sentence elsewhere { drop 0 push false }
            identity probe { is_bool is_bool } = { drop 0 push true };
        "#;
        let Outcome::Stuck(residual) = prove_with(code, "probe", Some("inline(elsewhere) egraph"))
        else {
            panic!("nothing here calls it");
        };
        assert!(
            residual.stopped.contains("found no call to it"),
            "{}",
            residual.stopped
        );
    }

    #[test]
    fn a_label_naming_nothing_at_all_is_a_load_error() {
        // A sentence that is not there is a mistake in the proof, not a proof
        // that failed, so it is caught when the entry is attached.
        let library = assemble("identity probe { is_bool } = { is_bool };").unwrap();
        let entries = parse_hant("proof probe = inline(nowhere) egraph;").unwrap();
        let err = crate::corpus::attach(&entries[0].strategy, &library).unwrap_err();
        assert!(err.contains("no sentence is called"), "{}", err);
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
            "via { drop(1) ; push true }",
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
            "via { drop(1) ; push true } (right: inline egraph)",
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
    fn a_solve_fills_its_template_from_the_left_side() {
        // The left side reaches `drop ; push true`; the template asks for
        // "something, then `push true`" and the match fills ?f with the
        // smallest spelling of that something. The right half then compares
        // the filled waypoint against a call, so it inlines.
        let outcome = prove_with_vias(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
            "#,
            "probe",
            "solve (f: 1 -> 0) { ?f ; push true } (right: inline)",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the template matches and the right half closes");
        };
        assert_eq!(
            proof.summary(),
            "solve (?f = drop(1); right: inline; the two sides are one term)"
        );
    }

    #[test]
    fn symm_hands_the_asymmetric_steps_the_other_side() {
        // `solve` matches its template against the *left* side's class, and
        // here the side worth matching is the right one. Swap, then solve.
        let outcome = prove_with_vias(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { jump crate::drop_and_true } = { is_bool is_bool };
            "#,
            "probe",
            "symm solve (f: 1 -> 0) { ?f ; push true } (right: inline)",
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the swapped goal is the one solve can match");
        };
        assert_eq!(
            proof.summary(),
            "symm; solve (?f = drop(1); right: inline; the two sides are one term)"
        );
    }

    #[test]
    fn a_swapped_goal_that_sticks_says_which_way_round_it_is() {
        let outcome = prove_with_vias("identity probe { push 1 } = { push 2 };", "probe", "symm");
        let Outcome::Stuck(residual) = outcome else {
            panic!("push 2 is not push 1 either way round");
        };
        assert!(
            residual.path.iter().any(|step| step.contains("swapped")),
            "{:?}",
            residual.path
        );
        assert_eq!(format!("{}", residual.lhs), "push 2");
    }

    #[test]
    fn a_template_that_matches_nothing_fails_loudly() {
        let outcome = prove_with_vias(
            r#"
            sentence three { push 3 }
            identity probe { push 1 push 2 add } = { jump crate::three };
            "#,
            "probe",
            "solve (f: 0 -> 1) { ?f ; not }",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("nothing in the left class ends in `not`");
        };
        assert!(
            residual.stopped.contains("matched nothing"),
            "{}",
            residual.stopped
        );
    }

    #[test]
    fn a_template_off_the_goal_net_is_refused_loudly() {
        let outcome = prove_with_vias(
            "identity probe { push 1 } = { push 2 };",
            "probe",
            "solve (f: 1 -> 1) { ?f }",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the template's net does not fit");
        };
        assert!(
            residual.stopped.contains("net stack change"),
            "{}",
            residual.stopped
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
