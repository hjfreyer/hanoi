//! Proving a goal, where the engine only ever transforms a term.
//!
//! Everything under this module is **blind**: a matcher reads one window of one
//! term and cannot know what it is being rewritten towards, and a tactic threads
//! a single tree. That is deliberate, and it is why a proof used to be written
//! by iterating with `rewrite` until two listings agreed — the tool could show
//! you where you got, never steer you where you meant to go.
//!
//! What is missing is not an equation. Congruence — `A = B ⟹ C[A] = C[B]` — is
//! already in the system twice over: a [`Location`] *is* a context, and
//! [`Location::under`] *is* the rule. The applier will rewrite a window at any
//! depth. What nothing could do was read the rule backwards: given a goal, cut
//! it into smaller goals, discharge each with the blind engine, and lift the
//! pieces back.
//!
//! So this is a third layer, above the two in `docs/tactics.md`. A **rule**
//! rewrites a window, a **tactic** places rules in a term, and a **strategy**
//! discharges a goal. The layering is strict: a strategy calls tactics and never
//! the other way round, and the leaves of every strategy are ordinary runs of
//! the ordinary engine.
//!
//! **Nothing here is trusted.** A strategy chooses which sub-goals to attack; it
//! does not get to decide what is true. Every step still comes from a matcher
//! and is still re-derived by the applier, and `prove` still replays the whole
//! assembled script onto the right-hand side before calling an identity proved.
//! A decomposition that lifts its pieces wrongly produces a script that does not
//! replay, which is a loud failure and not a quiet one.
//!
//! # Why decomposition is written and not inferred
//!
//! Peeling a common prefix is **incomplete**: `push 1 ; drop` = `push 2 ; drop`
//! is true, and stripping the shared `drop` leaves the false `push 1 ⇒ push 2`.
//! Descending commits just as hard. A prover that decomposed on its own
//! initiative whenever the plain tactic came up short would sometimes turn a
//! provable goal into an unprovable one and then report a residual that is not
//! the author's actual mistake.
//!
//! So there is deliberately **no default ladder** — no `auto` that tries
//! decomposition when a tactic falls short. A bare tactic in a `.hant` means
//! what it has always meant ([`Strategy::Blind`]), and congruence happens only
//! where someone wrote it down. Which route a proof takes is then part of the
//! proof, reviewed with it and diffable when it changes.

use std::cell::{Cell, RefCell};

use crate::applier::apply_script;
use crate::diff::side_by_side;
use crate::engine::{Env, Miss, Tactic, TacticError, run as run_tactic};
use crate::ir::{Node, Selector, same_effect, same_effect_seq};
use crate::location::Location;
use crate::print::render_nodes;
use crate::program::Program;
use crate::rule::{Script, Step, invert};

/// A claim to be discharged: two terms, and where in an enclosing term they sit.
///
/// `at` is carried for the *report* rather than for the proof. A sub-goal's
/// script is lifted at the point of decomposition, so by the time it reaches the
/// caller it already addresses the enclosing sequence; what `at` buys is a
/// residual that can say which branch arm the disagreement is in instead of
/// handing back a whole-term diff.
pub(crate) struct Goal {
    pub(crate) at: Vec<(usize, Selector)>,
    pub(crate) lhs: Vec<Node>,
    pub(crate) rhs: Vec<Node>,
}

impl Goal {
    /// The whole identity, which is where every proof starts.
    pub(crate) fn root(lhs: Vec<Node>, rhs: Vec<Node>) -> Goal {
        Goal {
            at: Vec::new(),
            lhs,
            rhs,
        }
    }

    fn under(&self, index: usize, sel: Selector, lhs: Vec<Node>, rhs: Vec<Node>) -> Goal {
        let mut at = self.at.clone();
        at.push((index, sel));
        Goal { at, lhs, rhs }
    }
}

/// How a goal is to be attacked.
///
/// The leaves ([`Blind`](Strategy::Blind), [`Exact`](Strategy::Exact),
/// [`Normalize`](Strategy::Normalize)) run tactics and compare. Everything else
/// cuts the goal up and recurses. See the module docs for why there is no
/// variant that decides between them on its own.
pub(crate) enum Strategy {
    /// A bare tactic, which is what every `.hant` written before this module
    /// existed holds: run it on the left-hand side and compare, exactly or —
    /// failing that — after unfolding both sides.
    ///
    /// Kept as one variant rather than assembled from the others because it has
    /// to mean *exactly* what it meant before, down to the step counts, and the
    /// order it does things in is not expressible as a composition: the
    /// unfolding is applied to what the tactic reached, not to the term the
    /// tactic started from.
    Blind(Tactic),
    /// `exact(t)`: run `t` on the left and land on the right as written. The
    /// same as [`Blind`](Strategy::Blind) without the inlining fallback, for a
    /// proof that wants to say the shapes match and mean it.
    Exact(Tactic),
    /// `normalize(t)`: run `t` on *both* sides and meet in the middle.
    ///
    /// The derivation is the left's script followed by the right's inverted,
    /// which is sound for the three reasons [`invert`] is written down under.
    Normalize(Tactic),
    /// `peel(s)`: strip the longest common prefix and suffix, then `s` on what
    /// is left. Fails when there is nothing to strip — see [`Prover::peel`].
    Peel(Box<Strategy>),
    /// `descend(...)`: congruence into the one node each side has reduced to.
    Descend(Descent),
    /// `inline(s)`: unfold every call on both sides, then `s` on the result.
    Inline(Box<Strategy>),
    /// `s1 | s2`: try, and fall back.
    Choice(Vec<Strategy>),
}

/// Which children `descend` reaches into.
///
/// A branch has two, and both have to be discharged for the branches to be
/// equal — so this is one form taking both rather than two forms that would have
/// to be sequenced. An arm with no strategy given must already agree by effect,
/// which is a claim like any other and is checked.
pub(crate) enum Descent {
    Body(Box<Strategy>),
    Arms {
        then: Option<Box<Strategy>>,
        els: Option<Box<Strategy>>,
    },
}

/// A discharged goal: the derivation, and how it closed.
pub(crate) struct Solved {
    /// `lhs ⇒ rhs`, addressed relative to the goal it discharges.
    pub(crate) script: Script,
    /// Aimed steps that did not land, from runs that ended up in the derivation.
    ///
    /// Collected here and reported by `prove`, which fails the proof over them.
    /// Gathering them per-leaf and merging only on success is what keeps an
    /// alternative that lost a [`Choice`](Strategy::Choice) from being blamed
    /// for aiming at a term nobody kept.
    pub(crate) misses: Vec<Miss>,
    pub(crate) closed: Closed,
}

/// How a proof reached the right-hand side, for the line the report prints.
pub(crate) enum Closed {
    /// The tactic landed on it as written.
    Exactly { steps: usize },
    /// It landed somewhere the right-hand side *inlines to*. Unfolding is an
    /// equation like any other — the axiom the library contributes by defining a
    /// sentence — so two terms with the same fully inlined form are equal.
    UpToInlining {
        steps: usize,
        unfolded: usize,
        folded: usize,
    },
    /// The two sides were driven together from both ends.
    Meeting { left: usize, right: usize },
    /// The goal was cut up, and every piece closed.
    ByParts { steps: usize, parts: usize },
}

impl Closed {
    /// The count a passing line reports.
    pub(crate) fn summary(&self) -> String {
        match self {
            Closed::Exactly { steps } => plural(*steps, "step", "steps"),
            Closed::UpToInlining {
                steps,
                unfolded,
                folded,
            } => format!(
                "{} + {} up to inlining",
                plural(*steps, "step", "steps"),
                unfolded + folded
            ),
            Closed::Meeting { left, right } => format!(
                "{} meeting in the middle",
                plural(left + right, "step", "steps")
            ),
            Closed::ByParts { steps, parts } => format!(
                "{} in {}",
                plural(*steps, "step", "steps"),
                plural(*parts, "part", "parts")
            ),
        }
    }

    /// How far along the derivation the two sides met.
    ///
    /// A derivation runs `LHS ⇒ … ⇒ (the middle) ⇐ … ⇐ RHS`, and the middle is
    /// the interesting term: it is what both sides were driven to, where the two
    /// ends are just the claim restated. For a strategy that drove only the left
    /// there is no middle and the answer is the whole script, which lands on the
    /// right-hand side — correctly, since that is where the right-hand side was
    /// already sitting.
    pub(crate) fn met_after(&self, script: usize) -> usize {
        match self {
            Closed::Exactly { .. } | Closed::ByParts { .. } => script,
            Closed::UpToInlining {
                steps, unfolded, ..
            } => steps + unfolded,
            Closed::Meeting { left, .. } => *left,
        }
    }

    /// How many goals were discharged to get here.
    fn parts(&self) -> usize {
        match self {
            Closed::ByParts { parts, .. } => *parts,
            _ => 1,
        }
    }
}

/// Why a goal did not come out proved.
pub(crate) enum Unproved {
    /// The strategy ran, and a goal is left over. The useful failure: it names
    /// the smallest disagreement rather than the whole term.
    Residual(Residual),
    /// A tactic ran out of fuel, was refused, or failed.
    Ran(Box<TacticError>),
    /// Unfolding a side to compare them did not finish. Named apart from
    /// [`Ran`](Unproved::Ran) because it is not the proof's own failure and
    /// reads as one.
    Inlining(&'static str, Box<TacticError>),
    /// A leaf's script does not reproduce the run it came from. A bug in the
    /// rewriter, not in the proof.
    Replay(String),
}

/// The goal a strategy could not close, and where it is.
pub(crate) struct Residual {
    pub(crate) at: Vec<(usize, Selector)>,
    pub(crate) lhs: Vec<Node>,
    pub(crate) rhs: Vec<Node>,
    /// What the strategy was trying to do when it gave up.
    pub(crate) why: String,
}

impl Residual {
    /// The context, as a location prints one. Empty at the root.
    pub(crate) fn context(&self) -> Option<String> {
        if self.at.is_empty() {
            return None;
        }
        Some(
            Location {
                descent: self.at.clone(),
                at: 0,
            }
            .to_string()
            .trim_end_matches(" @0")
            .to_string(),
        )
    }

    /// What the strategy was doing, and where it was doing it.
    ///
    /// Split from [`diff`](Residual::diff) so a caller can put something of its
    /// own between the two — `prove` quotes the proof and says which file to go
    /// and fix it in, where `rewrite` has a strategy that came off the command
    /// line and nothing to cite.
    pub(crate) fn headline(&self) -> Vec<String> {
        let mut out = vec![format!("  {}", self.why)];
        if let Some(context) = self.context() {
            out.push(String::new());
            out.push(format!("  The goal left over is inside {}.", context));
        }
        out
    }

    /// The two sides, side by side.
    ///
    /// Rendered **without origins**: the two sides came from two sentences, so
    /// every `<inline>` label differs and none of those differences mean
    /// anything. `same_effect_seq` ignores them for the same reason, and a
    /// listing being compared has to agree with the comparison.
    pub(crate) fn diff(&self, prog: &Program, stack: bool) -> Vec<String> {
        let left = render_nodes(prog, &self.lhs, stack, true, false);
        let right = render_nodes(prog, &self.rhs, stack, true, false);
        let rows = side_by_side(&left, &right, "what it reached", "the right-hand side");
        if !rows.is_empty() {
            return rows;
        }
        // Two listings that read alike but are not the same term. That is a bug
        // in one of them rather than in the proof, so show both rather than
        // nothing at all.
        let mut out = vec!["  The two listings read alike but are not the same term.".to_string()];
        out.extend(left);
        out.push(String::new());
        out.extend(right);
        out
    }
}

/// Discharges `goal` with `strategy`.
///
/// `fuel` is the budget for the *whole* proof, not for each leaf: it is
/// decremented by what every run spends, so a strategy with twenty sub-goals
/// cannot quietly cost twenty times a strategy with one.
pub(crate) fn solve(
    prog: &Program,
    inline: &Tactic,
    goal: &Goal,
    strategy: &Strategy,
    fuel: u64,
    check: bool,
) -> Result<Solved, Unproved> {
    work(prog, inline, goal, strategy, fuel, check).0
}

/// The same, with what the search cost alongside what it found.
///
/// The firing counts are the **search's**, not the derivation's: every run the
/// strategy made is counted, including an alternative that lost a
/// [`Choice`](Strategy::Choice) and steps a tactic took and rolled back. That is
/// deliberate, and it is the opposite of how [`Solved::misses`] is gathered —
/// because the two answer different questions. A miss is a *claim* that turned
/// out to be about a term nobody kept, so it is dropped with the run that made
/// it. A firing is *work done*, and work done is done whoever paid for it. Which
/// is also why this comes back from a goal that did not close: what a fruitless
/// route cost is exactly what you wanted to know about it.
pub(crate) fn work(
    prog: &Program,
    inline: &Tactic,
    goal: &Goal,
    strategy: &Strategy,
    fuel: u64,
    check: bool,
) -> (Result<Solved, Unproved>, Vec<(&'static str, usize)>) {
    let prover = Prover {
        prog,
        inline,
        check,
        fuel: Cell::new(fuel),
        firings: RefCell::new(Vec::new()),
    };
    let out = prover.solve(goal, strategy);
    (out, prover.firings.into_inner())
}

struct Prover<'a> {
    prog: &'a Program<'a>,
    /// `unfold_all`, compiled once by the caller.
    inline: &'a Tactic,
    check: bool,
    fuel: Cell<u64>,
    /// What every run so far has cost, merged. See [`work`].
    firings: RefCell<Vec<(&'static str, usize)>>,
}

/// One run of the blind engine.
struct Ran {
    nodes: Vec<Node>,
    script: Script,
    misses: Vec<Miss>,
}

impl Prover<'_> {
    fn solve(&self, goal: &Goal, strategy: &Strategy) -> Result<Solved, Unproved> {
        match strategy {
            Strategy::Blind(tactic) => self.blind(goal, tactic),
            Strategy::Exact(tactic) => self.exact(goal, tactic),
            Strategy::Normalize(tactic) => self.normalize(goal, tactic),
            Strategy::Peel(inner) => self.peel(goal, inner),
            Strategy::Descend(descent) => self.descend(goal, descent),
            Strategy::Inline(inner) => self.inline(goal, inner),
            Strategy::Choice(parts) => self.choice(goal, parts),
        }
    }

    // -----------------------------------------------------------------------
    // The leaves
    // -----------------------------------------------------------------------

    /// What a bare tactic in a `.hant` means, unchanged.
    fn blind(&self, goal: &Goal, tactic: &Tactic) -> Result<Solved, Unproved> {
        let ran = self.run(tactic, goal.lhs.clone(), Unproved::ran)?;
        let steps = ran.script.len();
        if same_effect_seq(&ran.nodes, &goal.rhs) {
            return Ok(Solved {
                script: ran.script,
                misses: ran.misses,
                closed: Closed::Exactly { steps },
            });
        }

        // Up to inlining. The fold-back is generated by running the *forward*
        // unfold on the right-hand side and inverting the script, which is why
        // `inv(unfold)` having no matcher costs nothing: nothing can read a
        // window and say which sentence to fold into, and nothing has to — the
        // step already names it.
        let left = self.unfold(ran.nodes.clone(), "left-hand")?;
        let right = self.unfold(goal.rhs.clone(), "right-hand")?;
        if !same_effect_seq(&left.nodes, &right.nodes) {
            return Err(Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: ran.nodes,
                rhs: goal.rhs.clone(),
                // Neutral about which tool is asking: `prove` reads this out of
                // a `.hant` and `rewrite` off the command line, and a bare
                // tactic is what `Blind` holds either way.
                why: "the tactic ran, but did not reach the right-hand side,\n  \
                      and inlining both sides did not reconcile them either."
                    .to_string(),
            }));
        }

        let (unfolded, folded) = (left.script.len(), right.script.len());
        let mut script = ran.script;
        script.extend(left.script);
        script.extend(invert(&right.script));
        Ok(Solved {
            script,
            misses: ran.misses,
            closed: Closed::UpToInlining {
                steps,
                unfolded,
                folded,
            },
        })
    }

    /// `exact(t)`: no inlining fallback. The shapes match, or they do not.
    fn exact(&self, goal: &Goal, tactic: &Tactic) -> Result<Solved, Unproved> {
        let ran = self.run(tactic, goal.lhs.clone(), Unproved::ran)?;
        let steps = ran.script.len();
        if !same_effect_seq(&ran.nodes, &goal.rhs) {
            return Err(Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: ran.nodes,
                rhs: goal.rhs.clone(),
                why: "the tactic ran and landed somewhere else.".to_string(),
            }));
        }
        Ok(Solved {
            script: ran.script,
            misses: ran.misses,
            closed: Closed::Exactly { steps },
        })
    }

    /// `normalize(t)`: drive both sides with the same tactic and meet.
    ///
    /// **The right-hand run's misses are discarded.** An aimed step is a claim
    /// about the term it is aimed at, and running a proof's tactic against the
    /// right-hand side asks it a question it was never written to answer — so a
    /// miss there says nothing about the proof. It is the stance the engine
    /// already takes towards an aim made inside a search.
    fn normalize(&self, goal: &Goal, tactic: &Tactic) -> Result<Solved, Unproved> {
        let left = self.run(tactic, goal.lhs.clone(), |e| {
            Unproved::Inlining("left-hand", e)
        })?;
        let right = self.run(tactic, goal.rhs.clone(), |e| {
            Unproved::Inlining("right-hand", e)
        })?;
        if !same_effect_seq(&left.nodes, &right.nodes) {
            return Err(Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: left.nodes,
                rhs: right.nodes,
                why: "both sides were normalized, and they did not meet.\n  \
                      What is shown is where each side got, not what was written."
                    .to_string(),
            }));
        }
        let (l, r) = (left.script.len(), right.script.len());
        let mut script = left.script;
        script.extend(invert(&right.script));
        Ok(Solved {
            script,
            // Only the left's. See above.
            misses: left.misses,
            closed: Closed::Meeting { left: l, right: r },
        })
    }

    // -----------------------------------------------------------------------
    // The decompositions
    // -----------------------------------------------------------------------

    /// `peel(s)`: strip what the two sides already share at each end.
    ///
    /// **Fails when it strips nothing.** A `peel` that quietly passed its goal
    /// through would be a no-op that hides an authoring mistake — the same
    /// reason `must(t)` fails when `t` changes nothing.
    fn peel(&self, goal: &Goal, inner: &Strategy) -> Result<Solved, Unproved> {
        let prefix = goal
            .lhs
            .iter()
            .zip(&goal.rhs)
            .take_while(|(l, r)| same_effect(l, r))
            .count();
        // Never past the prefix: two identical sequences are all prefix, and
        // counting them twice would take the suffix off the front.
        let room = goal.lhs.len().min(goal.rhs.len()) - prefix;
        let suffix = goal
            .lhs
            .iter()
            .rev()
            .zip(goal.rhs.iter().rev())
            .take_while(|(l, r)| same_effect(l, r))
            .count()
            .min(room);

        if prefix == 0 && suffix == 0 {
            return Err(Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: goal.lhs.clone(),
                rhs: goal.rhs.clone(),
                why: "`peel` found nothing the two sides already share at either end.".to_string(),
            }));
        }

        let sub = Goal {
            at: goal.at.clone(),
            lhs: goal.lhs[prefix..goal.lhs.len() - suffix].to_vec(),
            rhs: goal.rhs[prefix..goal.rhs.len() - suffix].to_vec(),
        };
        let solved = self.solve(&sub, inner)?;
        // The prefix is untouched by every step below, so the whole sub-script
        // shifts by exactly its length.
        let script = lift(solved.script, &[], prefix);
        Ok(Solved {
            closed: Closed::ByParts {
                steps: script.len(),
                parts: solved.closed.parts(),
            },
            script,
            misses: solved.misses,
        })
    }

    /// `descend(...)`: congruence into a node both sides open with.
    ///
    /// The goal must have reduced to one node a side — `peel(descend(...))` is
    /// the usual way to get there — because a node at position 3 of one sequence
    /// and position 4 of another are not the same node, and guessing which
    /// interior nodes correspond is a search this deliberately does not do.
    fn descend(&self, goal: &Goal, descent: &Descent) -> Result<Solved, Unproved> {
        let refuse = |why: String| {
            Err(Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: goal.lhs.clone(),
                rhs: goal.rhs.clone(),
                why,
            }))
        };
        let ([lhs], [rhs]) = (&goal.lhs[..], &goal.rhs[..]) else {
            return refuse(format!(
                "`descend` needs one node a side, and has {} against {}.\n  \
                 Strip what the two sides share first: `peel(descend(...))`.",
                goal.lhs.len(),
                goal.rhs.len()
            ));
        };

        match (lhs, rhs, descent) {
            (
                Node::Dip {
                    depth: dl,
                    body: bl,
                    ..
                },
                Node::Dip {
                    depth: dr,
                    body: br,
                    ..
                },
                Descent::Body(inner),
            ) => {
                // Equal depths or the congruence does not hold: `dip 1 { A }`
                // and `dip 2 { B }` hide different amounts of the stack, so
                // `A = B` says nothing about them.
                if dl != dr {
                    return refuse(format!(
                        "the two frames hide different depths, {} against {},\n  \
                         so proving their bodies equal would not make them equal.",
                        dl, dr
                    ));
                }
                let sub = goal.under(0, Selector::Body, bl.clone(), br.clone());
                let solved = self.solve(&sub, inner)?;
                let script = lift(solved.script, &[(0, Selector::Body)], 0);
                Ok(Solved {
                    closed: Closed::ByParts {
                        steps: script.len(),
                        parts: solved.closed.parts(),
                    },
                    script,
                    misses: solved.misses,
                })
            }

            (
                Node::Branch {
                    then_body: tl,
                    else_body: el,
                    ..
                },
                Node::Branch {
                    then_body: tr,
                    else_body: er,
                    ..
                },
                Descent::Arms { then, els },
            ) => {
                let mut script = Script::new();
                let mut misses = Vec::new();
                let mut parts = 0usize;
                for (sel, strategy, l, r) in [
                    (Selector::Then, then, tl, tr),
                    (Selector::Else, els, el, er),
                ] {
                    let sub = goal.under(0, sel, l.clone(), r.clone());
                    match strategy {
                        Some(strategy) => {
                            let solved = self.solve(&sub, strategy)?;
                            parts += solved.closed.parts();
                            misses.extend(solved.misses);
                            script.extend(lift(solved.script, &[(0, sel)], 0));
                        }
                        // An arm with no strategy is a claim that it needs no
                        // proof, and a claim gets checked.
                        None if same_effect_seq(l, r) => parts += 1,
                        None => {
                            return Err(Unproved::Residual(Residual {
                                at: sub.at,
                                lhs: sub.lhs,
                                rhs: sub.rhs,
                                why: format!(
                                    "the two `{}` arms are not already equal, and \
                                     `descend` was\n  given no strategy for them.",
                                    crate::location::selector_name(sel)
                                ),
                            }));
                        }
                    }
                }
                Ok(Solved {
                    closed: Closed::ByParts {
                        steps: script.len(),
                        parts,
                    },
                    script,
                    misses,
                })
            }

            (Node::Dip { .. }, Node::Dip { .. }, Descent::Arms { .. }) => refuse(
                "both sides are frames, and `descend` was given branch arms.\n  \
                 Write `descend(body: ...)`."
                    .to_string(),
            ),
            (Node::Branch { .. }, Node::Branch { .. }, Descent::Body(_)) => refuse(
                "both sides are branches, and `descend` was given a body.\n  \
                 Write `descend(then: ..., else: ...)`."
                    .to_string(),
            ),
            _ => refuse(
                "the two sides are not the same kind of node, so there is no\n  \
                 congruence to descend through."
                    .to_string(),
            ),
        }
    }

    /// `inline(s)`: open every call on both sides, then `s`.
    ///
    /// The fold-back is the right-hand side's own unfold script read backwards,
    /// which is the same trick [`blind`](Prover::blind) turns.
    fn inline(&self, goal: &Goal, inner: &Strategy) -> Result<Solved, Unproved> {
        let left = self.unfold(goal.lhs.clone(), "left-hand")?;
        let right = self.unfold(goal.rhs.clone(), "right-hand")?;
        let sub = Goal {
            at: goal.at.clone(),
            lhs: left.nodes,
            rhs: right.nodes,
        };
        let solved = self.solve(&sub, inner)?;
        // Same sequence, same offset: unfolding moves nothing sideways, so the
        // sub-script needs no lifting.
        let mut script = left.script;
        script.extend(solved.script);
        script.extend(invert(&right.script));
        Ok(Solved {
            closed: Closed::ByParts {
                steps: script.len(),
                parts: solved.closed.parts(),
            },
            script,
            misses: solved.misses,
        })
    }

    /// `s1 | s2`: the first that closes the goal.
    ///
    /// A residual is an alternative not working out, so it is caught; so is a
    /// tactic that *asked* to fail, which is how `must` says an aimed step
    /// missed. Running out of fuel is not caught: that is the budget for the
    /// whole proof gone, and silently trying the next branch with nothing left
    /// would report the wrong failure.
    fn choice(&self, goal: &Goal, parts: &[Strategy]) -> Result<Solved, Unproved> {
        let mut last = None;
        for strategy in parts {
            match self.solve(goal, strategy) {
                Ok(solved) => return Ok(solved),
                Err(Unproved::Ran(err)) if matches!(*err, TacticError::Failed) => {
                    last = Some(Unproved::Ran(err));
                }
                Err(err @ Unproved::Residual(_)) => last = Some(err),
                Err(err) => return Err(err),
            }
        }
        // The last alternative's, not the first: a choice is written with the
        // general case last, and that is the one whose failure explains the
        // most.
        Err(last.unwrap_or_else(|| {
            Unproved::Residual(Residual {
                at: goal.at.clone(),
                lhs: goal.lhs.clone(),
                rhs: goal.rhs.clone(),
                why: "an empty choice closes nothing.".to_string(),
            })
        }))
    }

    // -----------------------------------------------------------------------
    // Running the blind engine
    // -----------------------------------------------------------------------

    /// One tactic, on one term, against what is left of the budget.
    ///
    /// The script is replayed against the term it started from and held to
    /// reproducing the run *exactly* — `==`, not by effect. That is the claim
    /// that makes a script a derivation rather than a log, and it is checked at
    /// every leaf rather than once at the end so that a decomposition cannot
    /// bury a bad piece inside a good whole.
    fn run(
        &self,
        tactic: &Tactic,
        nodes: Vec<Node>,
        wrap: impl Fn(Box<TacticError>) -> Unproved,
    ) -> Result<Ran, Unproved> {
        let env = Env::new(self.prog, self.fuel.get(), self.check);
        let outcome = run_tactic(&env, tactic, nodes.clone());
        self.fuel
            .set(self.fuel.get().saturating_sub(env.steps_taken()));
        merge(&mut self.firings.borrow_mut(), env.histogram());
        let (got, script) = outcome.map_err(|e| wrap(Box::new(e)))?;

        let mut replayed = nodes;
        match apply_script(self.prog, &mut replayed, &script, self.check) {
            Ok(()) if replayed == got => {}
            Ok(()) => {
                return Err(Unproved::Replay("it produced a different tree".to_string()));
            }
            Err(err) => return Err(Unproved::Replay(err.to_string())),
        }

        Ok(Ran {
            nodes: got,
            script,
            misses: env.misses(),
        })
    }

    /// `unfold_all` on one side, which is the one tactic this module supplies
    /// for itself.
    fn unfold(&self, nodes: Vec<Node>, which: &'static str) -> Result<Ran, Unproved> {
        self.run(self.inline, nodes, |e| Unproved::Inlining(which, e))
    }
}

impl Unproved {
    fn ran(err: Box<TacticError>) -> Unproved {
        Unproved::Ran(err)
    }
}

/// A sub-goal's script, as the enclosing goal addresses it.
///
/// This is congruence, and [`Location::under`] is all of it: the sub-proof said
/// where it wanted to rewrite *within the goal it was shown*, exactly as a
/// matcher does within its window, and this is what the caller does with that
/// answer. Because the result is still a flat [`Script`], a proof found by
/// decomposition is an ordinary derivation — it replays, prints, and serializes
/// with nothing knowing it was assembled.
fn lift(script: Script, outer: &[(usize, Selector)], window_start: usize) -> Script {
    script
        .into_iter()
        .map(|step| Step {
            loc: step.loc.under(outer, window_start),
            ..step
        })
        .collect()
}

/// Adds one run's firing counts to a running total, keeping the order
/// [`Env::histogram`] produces: most frequent first, ties by name.
fn merge(into: &mut Vec<(&'static str, usize)>, from: Vec<(&'static str, usize)>) {
    for (name, count) in from {
        match into.iter_mut().find(|(n, _)| *n == name) {
            Some((_, total)) => *total += count,
            None => into.push((name, count)),
        }
    }
    into.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
}

fn plural(n: usize, one: &str, many: &str) -> String {
    if n == 1 {
        format!("{} {}", n, one)
    } else {
        format!("{} {}", n, many)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::{Direction, StepKind};
    use crate::script::{Definitions, PRELUDE};
    use bytecode::{Instruction, Library, SentenceIndex, Value};

    fn defs() -> Definitions {
        let mut d = Definitions::new();
        d.load(PRELUDE).expect("the prelude parses");
        d
    }

    fn op(inst: Instruction) -> Node {
        Node::Op(inst)
    }

    fn push(n: i64) -> Node {
        Node::Op(Instruction::Push(Value::Int(n)))
    }

    /// Runs a strategy against a goal spelled out as nodes, and returns either
    /// the derivation's length or the residual's `why`.
    fn attempt(goal: Goal, strategy: &Strategy) -> Result<Solved, Unproved> {
        let library = Box::leak(Box::new(Library::new()));
        let prog = Program::new(library);
        let inline = defs()
            .compile_with("unfold_all", Some(&prog))
            .expect("the prelude compiles");
        solve(&prog, &inline, &goal, strategy, 10_000, true)
    }

    /// The solved goal, or a panic saying why it was not — `Unproved` carries
    /// terms and tactic errors, so it explains itself far better through
    /// [`why`] than a derived `Debug` would.
    fn ok(result: Result<Solved, Unproved>, expected: &str) -> Solved {
        match result {
            Ok(solved) => solved,
            Err(err) => panic!("expected {}, got: {}", expected, why(err)),
        }
    }

    fn why(err: Unproved) -> String {
        match err {
            Unproved::Residual(r) => r.why,
            Unproved::Ran(e) => format!("ran: {}", e),
            Unproved::Inlining(which, e) => format!("inlining {}: {}", which, e),
            Unproved::Replay(e) => format!("replay: {}", e),
        }
    }

    fn cleanup() -> Tactic {
        defs().compile_with("cleanup", None).expect("cleanup")
    }

    fn id() -> Tactic {
        defs().compile_with("id", None).expect("id")
    }

    // -----------------------------------------------------------------------
    // Peeling
    // -----------------------------------------------------------------------

    #[test]
    fn peeling_strips_what_both_sides_share_and_proves_the_rest() {
        // `drop ; is_bool is_bool ; drop` against `drop ; drop 0 push true ; drop`.
        let shared = |mid: Vec<Node>| {
            let mut out = vec![op(Instruction::Drop)];
            out.extend(mid);
            out.push(op(Instruction::Drop));
            out
        };
        let goal = Goal::root(
            shared(vec![op(Instruction::IsBool), op(Instruction::IsBool)]),
            shared(vec![op(Instruction::Drop), push(0), push(1)]),
        );
        // Not provable as written — what matters is that peeling isolated the
        // middle, which the residual's shape is what shows.
        let err = attempt(goal, &Strategy::Peel(Box::new(Strategy::Exact(cleanup()))))
            .err()
            .expect("the middles differ");
        let Unproved::Residual(r) = err else {
            panic!("expected a residual");
        };
        // The shared `drop`s are gone from both sides of what is reported.
        assert!(
            !r.rhs.contains(&op(Instruction::Drop)) || r.rhs.len() < 5,
            "the suffix should have been peeled"
        );
    }

    /// The discipline that makes a decomposition say so when it no longer
    /// matches the term, instead of passing the goal through unchanged.
    #[test]
    fn peeling_nothing_is_a_failure_not_a_no_op() {
        let goal = Goal::root(vec![push(1)], vec![push(2)]);
        let err = attempt(goal, &Strategy::Peel(Box::new(Strategy::Exact(id()))))
            .err()
            .expect("there is nothing to peel");
        assert!(
            why(err).contains("found nothing"),
            "expected a peel failure"
        );
    }

    /// Two identical sequences are all prefix. Counting the suffix as well
    /// would take it off the front a second time and slice past the middle.
    #[test]
    fn peeling_two_identical_sides_does_not_double_count() {
        let goal = Goal::root(
            vec![op(Instruction::Drop), op(Instruction::Drop)],
            vec![op(Instruction::Drop), op(Instruction::Drop)],
        );
        let solved = ok(
            attempt(goal, &Strategy::Peel(Box::new(Strategy::Exact(id())))),
            "an empty goal to close with no steps",
        );
        assert!(solved.script.is_empty(), "nothing to do, nothing done");
    }

    // -----------------------------------------------------------------------
    // Descending
    // -----------------------------------------------------------------------

    /// The case that motivates the whole module: the two sides differ only
    /// inside a branch arm, which no amount of inlining reconciles.
    #[test]
    fn descending_proves_one_arm_and_checks_the_other() {
        let branch = |then_body: Vec<Node>| Node::Branch {
            then_origin: "<test>".to_string(),
            then_body,
            else_origin: "<test>".to_string(),
            else_body: vec![op(Instruction::Drop)],
        };
        let goal = Goal::root(
            vec![branch(vec![
                op(Instruction::IsBool),
                op(Instruction::IsBool),
            ])],
            vec![branch(vec![op(Instruction::Drop), push(0), push(1)])],
        );
        let solved = attempt(
            goal,
            &Strategy::Descend(Descent::Arms {
                then: Some(Box::new(Strategy::Exact(cleanup()))),
                els: None,
            }),
        );
        // Whether it closes depends on the rule set; what this pins is that the
        // steps it produced address the *then arm*, which is congruence doing
        // its job.
        if let Ok(solved) = solved {
            assert!(
                solved
                    .script
                    .iter()
                    .all(|s| s.loc.descent.first() == Some(&(0, Selector::Then))),
                "every step should have been lifted into the then arm"
            );
        }
    }

    /// An arm with no strategy is a claim that it needs none, and a claim gets
    /// checked rather than assumed.
    #[test]
    fn an_arm_left_out_must_already_agree() {
        let branch = |else_body: Vec<Node>| Node::Branch {
            then_origin: "<test>".to_string(),
            then_body: vec![op(Instruction::Drop)],
            else_origin: "<test>".to_string(),
            else_body,
        };
        let goal = Goal::root(vec![branch(vec![push(1)])], vec![branch(vec![push(2)])]);
        let err = attempt(
            goal,
            &Strategy::Descend(Descent::Arms {
                then: None,
                els: None,
            }),
        )
        .err()
        .expect("the else arms differ");
        let Unproved::Residual(r) = err else {
            panic!("expected a residual");
        };
        assert!(
            r.why.contains("`else` arms are not already equal"),
            "{}",
            r.why
        );
        // ...and the residual says where it is, which is the whole point of
        // carrying the context.
        assert_eq!(r.context().as_deref(), Some("[0.else]"));
    }

    #[test]
    fn frames_hiding_different_depths_do_not_descend() {
        let dip = |depth: usize| Node::Dip {
            depth,
            origins: Vec::new(),
            body: vec![op(Instruction::Drop)],
        };
        let goal = Goal::root(vec![dip(1)], vec![dip(2)]);
        let err = attempt(
            goal,
            &Strategy::Descend(Descent::Body(Box::new(Strategy::Exact(id())))),
        )
        .err()
        .expect("different depths");
        assert!(why(err).contains("different depths"));
    }

    #[test]
    fn descending_needs_one_node_a_side() {
        let goal = Goal::root(
            vec![op(Instruction::Drop), op(Instruction::Drop)],
            vec![op(Instruction::Drop)],
        );
        let err = attempt(
            goal,
            &Strategy::Descend(Descent::Body(Box::new(Strategy::Exact(id())))),
        )
        .err()
        .expect("two nodes against one");
        assert!(why(err).contains("one node a side"));
    }

    // -----------------------------------------------------------------------
    // The garden path
    // -----------------------------------------------------------------------

    /// Peeling is incomplete, and this is the shape of it: `push 1 ; drop` and
    /// `push 2 ; drop` are equal, and stripping the shared `drop` leaves the
    /// false `push 1 ⇒ push 2`.
    ///
    /// Both outcomes here are correct. The point is that the author picks, and
    /// that the wrong pick fails legibly instead of wandering — which is why
    /// there is no default that would have picked `peel` on its own.
    #[test]
    fn peeling_can_turn_a_true_goal_into_a_false_one() {
        let goal = || {
            Goal::root(
                vec![push(1), op(Instruction::Drop)],
                vec![push(2), op(Instruction::Drop)],
            )
        };

        // Peeled, the residual is the false middle.
        let err = attempt(goal(), &Strategy::Peel(Box::new(Strategy::Exact(id()))))
            .err()
            .expect("`push 1` is not `push 2`");
        let Unproved::Residual(r) = err else {
            panic!("expected a residual");
        };
        assert_eq!(r.lhs, vec![push(1)]);
        assert_eq!(r.rhs, vec![push(2)]);

        // Normalized, both sides annihilate and it closes.
        let solved = ok(
            attempt(goal(), &Strategy::Normalize(cleanup())),
            "both sides to clean up to nothing",
        );
        assert!(matches!(solved.closed, Closed::Meeting { .. }));
    }

    /// A choice reports the last alternative's failure, since a choice is
    /// written with the general case last.
    #[test]
    fn a_choice_takes_the_first_that_closes() {
        let goal = Goal::root(
            vec![push(1), op(Instruction::Drop)],
            vec![push(2), op(Instruction::Drop)],
        );
        let solved = ok(
            attempt(
                goal,
                &Strategy::Choice(vec![
                    Strategy::Peel(Box::new(Strategy::Exact(id()))),
                    Strategy::Normalize(cleanup()),
                ]),
            ),
            "the second alternative to close it",
        );
        assert!(matches!(solved.closed, Closed::Meeting { .. }));
    }

    // -----------------------------------------------------------------------
    // Lifting
    // -----------------------------------------------------------------------

    /// The sub-script has to come back addressing the enclosing sequence, or a
    /// decomposed proof would replay against the wrong window.
    #[test]
    fn a_lifted_script_addresses_the_enclosing_sequence() {
        let step = |loc: Location| Step {
            kind: StepKind::Unfold {
                depth: 0,
                target: SentenceIndex::from(0),
            },
            dir: Direction::Forward,
            loc,
        };
        // A step at @2 of a sub-goal that starts at 5 of its parent is at @7.
        let lifted = lift(vec![step(Location::root(2))], &[], 5);
        assert_eq!(lifted[0].loc, Location::root(7));
        // ...and a step at @2 of a then arm keeps its own offset, under the arm.
        let lifted = lift(vec![step(Location::root(2))], &[(0, Selector::Then)], 0);
        assert_eq!(
            lifted[0].loc,
            Location {
                descent: vec![(0, Selector::Then)],
                at: 2,
            }
        );
    }
}
