//! The interpreter for the strategy language of [`crate::hant`].
//!
//! A proof mirrors a tree of goals, and a goal is two
//! [graphs](crate::kernel::graph). A strategy acts on one: manipulations
//! transform it — the tactic steps rewrite a side in place, `inline` opens
//! calls, `symm` turns it — a splitter (`via`, `select-same`) replaces it
//! with independent subgoals each carrying its own strategy, and
//! `diagram` closes it. A goal
//! whose sides have become **isomorphic** closes on its own, before any
//! step runs, which is what `exact`'s claim tests. The default — what an
//! identity with no written proof gets — is `diagram` alone.
//!
//! The closer **is** the table now: `diagram` rewrites both sides by
//! [`tactic::decide`](crate::tactic::decide) — every driven
//! law, to fixpoint — and asks whether they landed on
//! one diagram, by isomorphism. Every rewrite on the way is an instance of
//! a named law checked by
//! [`rules::apply`], so the verdict is a
//! derivation's worth of checked steps and one final isomorphism, rather
//! than one engine's word. A stuck `diagram` means the claim is false, or
//! true only for reasons the table cannot yet say — and `cases` is the
//! step for the largest of those: case analysis on an intermediate
//! result that can only be `true` or `false`, done as the table's own
//! expansion rewrite and spent deliberately the way `inline` spends a
//! definition. Nothing in this module touches a graph except through
//! [`Derivation::push`](crate::kernel::rules::Derivation::push): the
//! whole file is untrusted convenience over the table.
//!
//! A stuck goal's residual is **both sides as graphs**, plus the steps of
//! the strategy that holds it: when the engine says no, what it acted on
//! is the thing worth printing, and a box in it keeps the id a next step
//! would name. A stuck *tactic* reports the goal as it now stands: a
//! failed run leaves its graph at the last step that landed, and showing
//! that state is the point of the guarantee.

use std::collections::HashMap;

use bytecode::{IdentityIndex, Library};

use crate::hant::{Body, OnSide, Step, Strategy, default_strategy};
use crate::kernel;
use crate::kernel::goal::{self, Goal};
use crate::kernel::graph::{self, Address, Graph, Named, Pair, Prefix};
use crate::kernel::rules::{self, Derivation};
use crate::kernel::term::{Context, Error};
use crate::proof::{self, Outcome, Proof, Residual, against};
use crate::tactic;

/// One side of a goal, picked out for a mutation that borrows it alone.
type Pick = fn(&mut Goal) -> &mut Graph;

/// A claim that has closed, in the two forms a `by` might spend it: the
/// pair a citation applies, and the run that would discharge that citation.
struct Lemma {
    pair: Pair,
    run: Vec<kernel::rules::Step>,
}

/// Proves goals against one library.
///
/// Every step reads the goal's terms out of a [`Context`] and writes the
/// terms it makes back into it, so the one arena is threaded through: a
/// waypoint read at load time, the goal, and every subgoal a strategy carves
/// out of it are all places in it.
///
/// It also **remembers what it has proved**, which is what a `by` spends. A
/// prover is filled by whoever drives it — [`Prover::learn`] after each
/// close, in the corpus's [proving
/// order](crate::corpus::Corpus::proving_order) — and a `by` naming a claim
/// this prover has not been taught fails saying so, rather than quietly
/// assuming it.
pub struct Prover<'l> {
    pub library: &'l Library,
    /// The claims that have closed, as the [`Pair`] a `by` spends — the
    /// identity's two sides, built and aligned exactly as its own goal was —
    /// beside the run that would discharge a citation of it, or why there is
    /// none.
    ///
    /// Only closed claims go in, which is the whole of what makes a citation
    /// honest: a `by` can name nothing this prover has not already seen
    /// discharged.
    lemmas: HashMap<IdentityIndex, Lemma>,
}

/// What running a strategy over one goal wrote, before anything checked
/// it: the draft, or where it stuck. [`Prover::prove`] is what turns a
/// draft into an [`Outcome`], by flattening and certifying it.
// A residual carries two graphs and a draft a tree; one of each per
// goal, briefly, is not worth a box.
#[allow(clippy::large_enum_variant)]
enum Draft {
    Closed(Proof),
    Stuck(Residual),
}

impl<'l> Prover<'l> {
    pub fn new(library: &'l Library) -> Self {
        Prover {
            library,
            lemmas: HashMap::new(),
        }
    }

    /// The same prover, spending every `by` in full rather than on trust.
    /// Records a closed identity so later proofs may cite it with `by`.
    ///
    /// `goal` is the claim **as stated** — before its own strategy touched
    /// it — because that is the claim, and a `by` looks for its left side —
    /// beside the certified run that takes the one onto the other, which is
    /// what a `by` carries in. Nothing about *how* the claim closed is
    /// kept: every close is a flat run by the time it is certified, so a
    /// claim proved by `via`, by `inline`, by `select-same` or by driving
    /// both sides together is as citable as one driven from the left.
    ///
    /// Remembers a claim that closed, as what a `by` spends: its two sides
    /// as the goal built them, and the certified run that takes the one
    /// onto the other. A citation carries that run in — every use pays for
    /// the claim's own steps and nothing is taken on trust — so the run is
    /// kept beside the pair.
    pub fn learn(&mut self, idx: IdentityIndex, goal: &Goal, run: &[kernel::rules::Step]) {
        let pair = Pair::new(goal.lhs.clone(), goal.rhs.clone())
            .expect("a goal's sides are built, and aligned to one arity");
        self.lemmas.insert(
            idx,
            Lemma {
                pair,
                run: run.to_vec(),
            },
        );
    }

    /// Runs a strategy over a goal and answers what became of it.
    ///
    /// The strategy writes a [`Proof`] — a draft, the tree of goals it
    /// carved and the steps each spent — and nothing is believed of it.
    /// [`proof::flatten`] reads the one run off the tree, and
    /// [`certify`](goal::certify) replays that run against the goal as
    /// stated. A draft that does not flatten, or a run that does not land,
    /// is a prover bug and comes back [`Outcome::Stuck`] saying so rather
    /// than closed on the prover's word.
    pub fn prove(
        &self,
        ctx: &mut Context,
        goal: Goal,
        strategy: Option<&Strategy<Body>>,
    ) -> Result<Outcome, Error> {
        let default = default_strategy();
        let strategy = strategy.unwrap_or(&default);
        let stated = goal.clone();
        let draft = match self.run(ctx, strategy, goal)? {
            Draft::Closed(draft) => draft,
            Draft::Stuck(residual) => return Ok(Outcome::Stuck(residual)),
        };
        let run = match proof::flatten(&draft, &stated, ctx) {
            Ok(run) => run,
            Err(why) => {
                let why = format!(
                    "the draft does not flatten to a run — a prover bug, and the claim is not \
                     accepted on its word: {}",
                    why
                );
                return Ok(Outcome::Stuck(gave_up(&stated, &why)));
            }
        };
        if let Err(why) = goal::certify(&stated, &run, ctx, self.library) {
            let why = format!(
                "the run does not certify — a prover bug, and the claim is not accepted on \
                 its word: {}",
                why
            );
            return Ok(Outcome::Stuck(gave_up(&stated, &why)));
        }
        Ok(Outcome::Closed { draft, run })
    }

    /// One strategy on one goal. A goal whose sides are one graph —
    /// isomorphic — is closed before any step runs, at every level, so a
    /// cut's side that a manipulation made trivial needs no steps of its
    /// own.
    fn run(&self, ctx: &mut Context, strategy: &[Step<Body>], goal: Goal) -> Result<Draft, Error> {
        if graph::isomorphic(&goal.lhs, &goal.rhs) {
            return Ok(Draft::Closed(Proof::Trivial));
        }
        let Some((head, rest)) = strategy.split_first() else {
            return Ok(Draft::Stuck(gave_up(
                &goal,
                "the strategy ended with the goal still open",
            )));
        };
        match head {
            // Both sides rewritten by the whole table to fixpoint; either
            // they land on one diagram or the claim is beyond the table.
            // Every rewrite is an instance of a named law checked by
            // `rules::apply`, so the closer's verdict is a derivation's
            // worth of checked steps and one isomorphism. The residual is
            // what each side became.
            Step::Diagram => {
                let mut goal = goal;
                let mut spent: [Vec<kernel::rules::Step>; 2] = [Vec::new(), Vec::new()];
                let picks: [Pick; 2] = [|g| &mut g.lhs, |g| &mut g.rhs];
                for (pick, record) in picks.into_iter().zip(&mut spent) {
                    let mut deriv = kernel::rules::Derivation::default();
                    if let Err(e) = tactic::run(pick(&mut goal), &mut deriv, &tactic::decide()) {
                        let why = format!("`diagram`'s drive failed: {}", e);
                        return Ok(Draft::Stuck(gave_up(&goal, &why)));
                    }
                    *record = deriv.steps().cloned().collect();
                }
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    let [lhs, rhs] = spent;
                    return Ok(Draft::Closed(Proof::Diagram { lhs, rhs }));
                }
                Ok(Draft::Stuck(gave_up(
                    &goal,
                    "the two sides rewrite to different diagrams: the claim is \
                     false, or true only for reasons the table cannot yet say",
                )))
            }

            // Case analysis, as a splitter: η on the named wire — the
            // instruction set promises the answer is `true` or `false`
            // and nothing else, so everything downstream of it becomes a
            // branch over both assumptions (`rules::case_split`, three
            // checked rows) — and then that branch split the way
            // `select-same` splits one a goal already has. The two cases
            // are independent goals, each with its own strategy, each
            // closed on its own road.
            //
            // The hypothesis is not a context anything has to carry: it
            // is the block each case stands in, with the assumed answer
            // pasted into it, and the law the closing `select-same` is
            // named after puts the two back together. A manipulation had
            // to spend it as a rewrite scoped to a region; a splitter
            // spends it as the goal it is.
            Step::Cases {
                at,
                then_arm,
                else_arm,
            } => {
                if !rest.is_empty() {
                    unreachable!("`cases` closes the goal, and `validate` refused what follows");
                }
                self.cases_step(ctx, goal, at, then_arm, else_arm)
            }

            // A goal whose sides are one graph closed above, before any
            // step ran — so an `exact` that is reached is an `exact` whose
            // claim is false, and its whole job is the report: the goal
            // exactly as it stands, with no normalization to reshape it.
            // That unaltered residual is what the step is usually written
            // for — `exact` alone shows the identity as built and aligned,
            // and after a manipulation it shows what the manipulation
            // left, box by box.
            Step::Exact => Ok(Draft::Stuck(gave_up(
                &goal,
                "`exact` claims the sides are one graph, and they are not",
            ))),

            // A graph tactic on one side, or on each in turn. Every rewrite
            // it lands went through `rules::apply`, so nothing here is
            // trusted; and a tactic that fails leaves its side standing at
            // the last step that landed, so the residual shows exactly the
            // state a person would want to look at.
            Step::Rewrite { side, tactic } => {
                let mut goal = goal;
                let mut spent: [Vec<kernel::rules::Step>; 2] = [Vec::new(), Vec::new()];
                let picks: &[(Pick, usize)] = match side {
                    OnSide::Lhs => &[(|g| &mut g.lhs, 0)],
                    OnSide::Rhs => &[(|g| &mut g.rhs, 1)],
                    OnSide::Both => &[(|g| &mut g.lhs, 0), (|g| &mut g.rhs, 1)],
                };
                for &(pick, at) in picks {
                    let mut deriv = kernel::rules::Derivation::default();
                    match tactic::run(pick(&mut goal), &mut deriv, tactic) {
                        Ok(_) => spent[at] = deriv.steps().cloned().collect(),
                        Err(e) => {
                            let why = format!("`{}(…)`: {}", side.word(), e);
                            return Ok(Draft::Stuck(gave_up(&goal, &why)));
                        }
                    }
                }
                let [lhs, rhs] = spent;
                Ok(match self.run(ctx, rest, goal)? {
                    Draft::Closed(sub) => Draft::Closed(Proof::Rewrote {
                        side: side.word(),
                        lhs,
                        rhs,
                        sub: Box::new(sub),
                    }),
                    Draft::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, format!("after rewriting {}", side.word()));
                        Draft::Stuck(residual)
                    }
                })
            }

            // Another identity, cited where it occurs.
            //
            // Its left side is found here — the claim's two sides are a
            // `Pair` like any other, and the match is held to `check_match`
            // like any other — and the claim's own certified run is carried
            // in through that embedding, so what lands is ordinary rewrites
            // the kernel replays without knowing where they came from. Only
            // a claim that closed is in the table at all, and the citation
            // order is a DAG or the corpus refused to run.
            Step::By { side, of } => {
                let Body::Lemma(idx) = *of else {
                    return Ok(Draft::Stuck(gave_up(
                        &goal,
                        "`by` was handed something that is not an identity",
                    )));
                };
                let name = self.library.identities[idx].name.clone();
                let Some(lemma) = self.lemmas.get(&idx) else {
                    let why = format!(
                        "`{}(by {})`: that identity is not proved, so there is nothing to \
                         cite",
                        side.word(),
                        name
                    );
                    return Ok(Draft::Stuck(gave_up(&goal, &why)));
                };
                let mut goal = goal;
                let mut spent: [Vec<kernel::rules::Step>; 2] = [Vec::new(), Vec::new()];
                let picks: &[(Pick, usize)] = match side {
                    OnSide::Lhs => &[(|g| &mut g.lhs, 0)],
                    OnSide::Rhs => &[(|g| &mut g.rhs, 1)],
                    OnSide::Both => &[(|g| &mut g.lhs, 0), (|g| &mut g.rhs, 1)],
                };
                for &(pick, at) in picks {
                    let host = pick(&mut goal);
                    // The first embedding, canonically. Which one is a
                    // choice a proof may need to make some day; today the
                    // sweep's own order is the answer, and it is the same
                    // order `fire` takes its proposal in.
                    let Some(here) = graph::find(host, lemma.pair.lhs()).into_iter().next() else {
                        let why = format!(
                            "`{}(by {})`: that identity's left side does not occur here",
                            side.word(),
                            name
                        );
                        return Ok(Draft::Stuck(gave_up(&goal, &why)));
                    };
                    // The cited claim's own run, carried in and re-applied
                    // here: what a citation *means*, spent in full at every
                    // use. Nothing is taken on trust, and the checker sees
                    // ordinary rewrites without knowing where they came from.
                    let outcome = rules::transplant(host, lemma.pair.lhs(), &here, &lemma.run)
                        .map(|ran| ran.steps().cloned().collect::<Vec<_>>())
                        .map_err(|e| e.to_string());
                    match outcome {
                        Ok(steps) => spent[at] = steps,
                        Err(e) => {
                            let why = format!("`{}(by {})`: {}", side.word(), name, e);
                            return Ok(Draft::Stuck(gave_up(&goal, &why)));
                        }
                    }
                }
                let [lhs, rhs] = spent;
                Ok(match self.run(ctx, rest, goal)? {
                    Draft::Closed(sub) => Draft::Closed(Proof::Rewrote {
                        side: side.word(),
                        lhs,
                        rhs,
                        sub: Box::new(sub),
                    }),
                    Draft::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, format!("after citing {} on the {}", name, side.word()));
                        Draft::Stuck(residual)
                    }
                })
            }

            Step::Via {
                waypoint,
                left,
                right,
            } => {
                let Body::Stone(waypoint) = *waypoint else {
                    unreachable!("the loader reads a via body as a stone");
                };
                // The cut is a claim, so a waypoint whose stack effect cannot
                // sit between the sides is refused here, loudly, rather than
                // producing goals nothing could ever close.
                if ctx.arity(waypoint).net() != goal.lhs.arity().net() {
                    let why = format!(
                        "the `via` waypoint's net stack change ({}) is not the goal's ({})",
                        ctx.arity(waypoint).net(),
                        goal.lhs.arity().net()
                    );
                    return Ok(Draft::Stuck(gave_up(&goal, &why)));
                }
                // Two goals, fully independent from here: each side takes its
                // own road, and proving both proves the whole by transitivity.
                // A narrower waypoint is padded as a term before it builds;
                // a wider one would pad the *goal*, which is not a step a
                // run can carry, so a proof may not cut there.
                if ctx.arity(waypoint).inputs > goal.lhs.arity().inputs {
                    let why = format!(
                        "the `via` waypoint takes {} input(s) and the goal {}: a waypoint may \
                         be narrower than the goal, not wider",
                        ctx.arity(waypoint).inputs,
                        goal.lhs.arity().inputs
                    );
                    return Ok(Draft::Stuck(gave_up(&goal, &why)));
                }
                let (lhs, stone) = against(ctx, &goal.lhs, waypoint);
                let sub = Goal { lhs, rhs: stone };
                let left_sub = match self.side(ctx, "in the left half of the cut", left, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Draft::Stuck(residual)),
                };
                let (rhs, stone) = against(ctx, &goal.rhs, waypoint);
                let sub = Goal { lhs: stone, rhs };
                let right_sub = match self.side(ctx, "in the right half of the cut", right, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Draft::Stuck(residual)),
                };
                Ok(Draft::Closed(Proof::Cut {
                    waypoint,
                    left_sub,
                    right_sub,
                }))
            }

            // The other splitter, and the one that eliminates a branch
            // rather than introducing one: the left side answers with a
            // `select`, so the goal `select(c, T, E) = B` is the two goals
            // `T = B` and `E = B`, each on its own road. What licenses
            // putting them back together is the law the step is named for
            // — a branch both of whose blocks are `B` is `B` — and the
            // condition goes with the branch, discarded the way every
            // untaken arm is.
            //
            // `cases` is this step with an η in front of it — it makes
            // the branch that holds the hypothesis and then comes here;
            // this one spends the branch a goal already has. Either way a
            // proof stops having to find one rewriting that suits both
            // blocks. It reads the left side, so `symm` is how a proof
            // says the branch is on the other one.
            Step::SelectSame { then_arm, else_arm } => {
                let Some((then, els)) = proof::blocks(&goal.lhs) else {
                    return Ok(Draft::Stuck(gave_up(
                        &goal,
                        "`select-same` needs the left side to answer with one branch, and                          its last box is not a `select` the whole answer reads",
                    )));
                };
                let sub = Goal {
                    lhs: then,
                    rhs: goal.rhs.clone(),
                };
                let then_sub = match self.side(ctx, "in the branch's then block", then_arm, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Draft::Stuck(residual)),
                };
                let sub = Goal {
                    lhs: els,
                    rhs: goal.rhs.clone(),
                };
                let else_sub = match self.side(ctx, "in the branch's else block", else_arm, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Draft::Stuck(residual)),
                };
                Ok(Draft::Closed(Proof::SelectSame { then_sub, else_sub }))
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
                Ok(match self.run(ctx, rest, swapped)? {
                    Draft::Closed(sub) => Draft::Closed(Proof::Swapped(Box::new(sub))),
                    Draft::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, "with the sides swapped".to_string());
                        Draft::Stuck(residual)
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
                let mut goal = goal;
                let lhs = proof::inline(&mut goal.lhs, ctx, self.library, only)?;
                let rhs = proof::inline(&mut goal.rhs, ctx, self.library, only)?;
                if lhs.is_empty() && rhs.is_empty() {
                    let why = match only {
                        None => "`inline` found no calls to open".to_string(),
                        Some(idx) => format!(
                            "`inline({})` found no call to it here",
                            self.library.names[idx]
                        ),
                    };
                    return Ok(Draft::Stuck(gave_up(&goal, &why)));
                }
                let name = only.map(|idx| self.library.names[idx].clone());
                Ok(match self.run(ctx, rest, goal)? {
                    Draft::Closed(sub) => Draft::Closed(Proof::Inlined {
                        target: only,
                        name,
                        lhs,
                        rhs,
                        sub: Box::new(sub),
                    }),
                    stuck => stuck,
                })
            }
        }
    }

    /// One subgoal of a splitter, under its own strategy or the default,
    /// its residual labelled with where it lives.
    fn side(
        &self,
        ctx: &mut Context,
        label: &str,
        strategy: &Option<Strategy<Body>>,
        sub: Goal,
    ) -> Result<Result<Box<Proof>, Residual>, Error> {
        let default = default_strategy();
        let strategy = strategy.as_ref().unwrap_or(&default);
        Ok(match self.run(ctx, strategy, sub)? {
            Draft::Closed(p) => Ok(Box::new(p)),
            Draft::Stuck(mut residual) => {
                residual.path.insert(0, label.to_string());
                Err(residual)
            }
        })
    }

    /// One `cases` step: η on the named wire, and then the branch it made
    /// split exactly the way [`Step::SelectSame`] splits one a goal
    /// already has.
    ///
    /// The expansion is the **left** side's, because the blocks are carved
    /// off the left and `select-same` is what puts them back — so a wire
    /// only the right side computes is reached by turning the goal round
    /// with `symm`, the same as for `select-same`. What the two cases are
    /// proved against is the whole right side, untouched: the hypothesis
    /// is the block each stands in.
    fn cases_step(
        &self,
        ctx: &mut Context,
        goal: Goal,
        at: &Prefix,
        then_arm: &Option<Strategy<Body>>,
        else_arm: &Option<Strategy<Body>>,
    ) -> Result<Draft, Error> {
        let mut goal = goal;
        let mut deriv = Derivation::default();
        // Resolved live, against the side as it now stands, under the
        // discipline every other address in this language is under: the
        // box, no box, or several — and the three are different mistakes.
        let wire = match goal.lhs.lookup(at) {
            Named::One(node) => node,
            Named::Many(found) => {
                let why = format!(
                    "`cases({})` is {} boxes of the left side: {}",
                    at,
                    found.len(),
                    found
                        .iter()
                        .map(Address::to_string)
                        .collect::<Vec<String>>()
                        .join(" ")
                );
                return Ok(Draft::Stuck(gave_up(&goal, &why)));
            }
            Named::Nothing => {
                // The friendliest thing a report can say here is which way
                // round the goal is: a wire the right side computes and the
                // left does not is a `symm` away.
                let why = match goal.rhs.lookup(at) {
                    Named::Nothing => format!(
                        "`cases({})` names no live box of the left side: an address is a name \
                         for what a box computes, and nothing there computes that",
                        at
                    ),
                    _ => format!(
                        "`cases({})` names a box of the right side and none of the left, and \
                         the blocks are carved off the left — `symm` says the branch is on \
                         the other side",
                        at
                    ),
                };
                return Ok(Draft::Stuck(gave_up(&goal, &why)));
            }
        };
        // Three checked rewrites, landing in the left side's record like
        // any others. A decline leaves nothing behind — the last of the
        // three is the one that would refuse an empty body, and it is
        // asked before anything moves.
        match kernel::rules::case_split(&mut goal.lhs, &mut deriv, wire) {
            Ok(Some(_)) => {}
            Ok(None) => {
                let why = format!(
                    "`cases({})` names a box and finds nothing to split on: nothing promises \
                     its answer is a bool, or nothing reads it",
                    at
                );
                return Ok(Draft::Stuck(gave_up(&goal, &why)));
            }
            Err(e) => {
                let why = format!("`cases` proposed a split the checker refused: {}", e);
                return Ok(Draft::Stuck(gave_up(&goal, &why)));
            }
        }
        let lhs: Vec<kernel::rules::Step> = deriv.steps().cloned().collect();

        let Some((then, els)) = proof::blocks(&goal.lhs) else {
            let why = format!(
                "`cases({})` expanded the wire and the left side's answer is not one branch: \
                 an output the wire says nothing about is an output the split cannot carve",
                at
            );
            return Ok(Draft::Stuck(gave_up(&goal, &why)));
        };
        let sub = Goal {
            lhs: then,
            rhs: goal.rhs.clone(),
        };
        let then_sub = match self.side(ctx, "in the true case of the split", then_arm, sub)? {
            Ok(p) => p,
            Err(residual) => return Ok(Draft::Stuck(residual)),
        };
        let sub = Goal {
            lhs: els,
            rhs: goal.rhs.clone(),
        };
        let else_sub = match self.side(ctx, "in the false case of the split", else_arm, sub)? {
            Ok(p) => p,
            Err(residual) => return Ok(Draft::Stuck(residual)),
        };
        Ok(Draft::Closed(Proof::Cases {
            lhs,
            then_sub,
            else_sub,
        }))
    }
}

/// A residual for a strategy that failed before any engine ran: the goal as
/// it stands, and why the step gave up. For a failed tactic "as it stands"
/// is the point: the graph reflects the last rewrite that landed.
fn gave_up(goal: &Goal, why: &str) -> Residual {
    Residual {
        lhs_graph: goal.lhs.clone(),
        rhs_graph: goal.rhs.clone(),
        path: Vec::new(),
        stopped: why.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hant::parse_hant;
    use crate::kernel::graph::{NodeId, NodeKind, Source};
    use crate::kernel::term::Prim;
    use bytecode::{Value, assemble};

    /// The live boxes of a graph, in id order: what a residual's side is,
    /// checked without going through the listing that prints it.
    fn kinds(graph: &Graph) -> Vec<NodeKind> {
        graph.live().map(|(_, kind)| kind.clone()).collect()
    }

    /// What a proof writes to name the one box a predicate holds of: the
    /// shortest prefix of its address, exactly as a residual listing
    /// prints it — which is where an author of a `cases` reads one.
    fn address(graph: &Graph, holds: impl Fn(&Graph, NodeId) -> bool) -> String {
        let mut found = graph
            .live()
            .map(|(id, _)| id)
            .filter(|&id| holds(graph, id));
        let id = found.next().expect("a box the predicate holds of");
        assert!(found.next().is_none(), "one box the predicate holds of");
        format!("#{}", graph.shortest(id))
    }

    /// The goal's two sides as some steps leave them, got the way a proof's
    /// author gets them: `exact` on an open goal fails and prints what it
    /// was reached with.
    fn standing(code: &str, name: &str, steps: &str) -> (Graph, Graph) {
        let (_ctx, outcome) = prove_with(code, name, Some(&format!("{} exact", steps)));
        match outcome {
            Outcome::Stuck(residual) => (residual.lhs_graph, residual.rhs_graph),
            _ => panic!("`exact` reached on an open goal fails and shows it"),
        }
    }

    /// Proves the identity named `name`, with the strategy written as a
    /// `.hant` entry body, or the default when `strategy` is `None` —
    /// reading `via` bodies exactly as `corpus::load` does.
    ///
    /// The arena comes back with the outcome: a residual names its terms by
    /// index, so reading one means keeping the context it was built in.
    fn prove_with(code: &str, name: &str, strategy: Option<&str>) -> (Context, Outcome) {
        let entries = strategy
            .map(|s| parse_hant(&format!("proof {} = {};", name, s)).unwrap())
            .unwrap_or_default();
        let library = assemble(code).unwrap();
        let mut ctx = Context::new();
        let strategy = entries
            .first()
            .map(|e| crate::corpus::attach(&mut ctx, &e.strategy, &library).unwrap());
        let idx = library.identity_by_name(name).unwrap();
        let goal = Goal::of_identity(&mut ctx, &library, idx).unwrap();
        let outcome = Prover::new(&library)
            .prove(&mut ctx, goal, strategy.as_ref())
            .unwrap();
        (ctx, outcome)
    }

    fn prove_identity(code: &str, name: &str) -> (Context, Outcome) {
        prove_with(code, name, None)
    }

    #[test]
    fn the_default_is_the_diagram_alone() {
        let (_ctx, outcome) = prove_identity(
            "identity probe { drop 0 is_bool is_bool } = { drop 0 drop 0 push true };",
            "probe",
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("the sides are one diagram");
        };
        assert_eq!(proof.summary(), "the two sides are one diagram");
    }

    #[test]
    fn differing_arms_close_as_one_diagram() {
        let (_ctx, outcome) = prove_identity(
            "identity probe { branch { is_bool is_bool } { not } } = { branch { is_int is_bool } { not } };",
            "probe",
        );
        assert!(matches!(outcome, Outcome::Closed { .. }));
    }

    #[test]
    fn a_call_stays_closed_until_a_proof_says_inline() {
        let code = r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
        "#;
        // The default does not spend the library's definitions…
        let (_ctx, outcome) = prove_identity(code, "probe");
        assert!(matches!(outcome, Outcome::Stuck(_)));
        // …a written proof does.
        let (_ctx, outcome) = prove_with(code, "probe", Some("inline diagram"));
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("expected the opened goal to close");
        };
        assert_eq!(proof.summary(), "inline; the two sides are one diagram");
    }

    #[test]
    fn exact_closes_what_a_manipulation_made_identical() {
        // Inlining the call leaves the two sides one term, so the claim holds
        // and no engine ever runs.
        let (_ctx, outcome) = prove_with(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { jump crate::drop_and_true } = { drop 0 push true };
            "#,
            "probe",
            Some("inline exact"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("the opened goal is one graph");
        };
        assert_eq!(proof.summary(), "inline; the two sides are one graph");
    }

    #[test]
    fn a_failed_exact_reports_the_goal_untouched() {
        // `is_bool ; is_bool` = `drop 0 ; push true` is provable — `diagram`
        // closes it — but `exact` claims more, fails, and shows the goal
        // exactly as it stands: no normalization, nothing spent. That
        // unaltered residual is what the step is for.
        let (_ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { drop 0 push true };",
            "probe",
            Some("exact"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the sides are not one graph as written");
        };
        assert!(residual.stopped.contains("`exact`"), "{}", residual.stopped);
        assert_eq!(
            kinds(&residual.lhs_graph),
            vec![NodeKind::Op(Prim::IsBool), NodeKind::Op(Prim::IsBool)],
            "the left is the two tests it was written as"
        );
        assert_eq!(
            kinds(&residual.rhs_graph),
            vec![NodeKind::Op(Prim::Push(Value::Bool(true)))],
            "the right is the literal it was written as; the `drop 0` is \
             not a box, it is the boundary not naming what it discards"
        );
        assert!(residual.path.is_empty());
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
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some("inline(outer) via { call inner } (right: inline)"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("the opened goal is `call inner` against the claim");
        };
        assert_eq!(
            proof.summary(),
            "inline outer; cut (left: the two sides are one graph; \
             right: inline; the two sides are one graph)"
        );
    }

    #[test]
    fn a_label_naming_an_uncalled_sentence_fails_loudly() {
        let code = r#"
            #[arity(1,1)] sentence elsewhere { drop 0 push false }
            identity probe { is_bool is_bool } = { drop 0 push true };
        "#;
        let (_ctx, outcome) = prove_with(code, "probe", Some("inline(elsewhere) diagram"));
        let Outcome::Stuck(residual) = outcome else {
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
        let entries = parse_hant("proof probe = inline(nowhere) diagram;").unwrap();
        let err =
            crate::corpus::attach(&mut Context::new(), &entries[0].strategy, &library).unwrap_err();
        assert!(err.contains("no sentence is called"), "{}", err);
    }

    /// The tactic steps: a side rewritten until the sides are one graph
    /// closes by the auto-close, and the proof says which sides were spent.
    #[test]
    fn a_rewritten_side_closes_by_isomorphism() {
        // A directed law leads the left and the driver alone takes the
        // right: the two sides settle on the one graph.
        let (_ctx, outcome) = prove_with(
            "identity probe { push 1 push 2 add } = { push 2 push 1 add };",
            "probe",
            Some("lhs(fire(fold)) rhs(decide) exact"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("the two spellings settle together");
        };
        let summary = proof.summary();
        assert!(
            summary.starts_with("lhs: ")
                && summary.contains("; rhs: ")
                && summary.ends_with("the two sides are one graph"),
            "{}",
            summary
        );

        // `both` spends each side in turn.
        let (_ctx, outcome) = prove_with(
            "identity probe { not not not } = { as_bool not };",
            "probe",
            Some("both(saturate(not-not)) exact"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("the double negative is the coercion on both sides");
        };
        let summary = proof.summary();
        assert!(
            summary.starts_with("both: ") && summary.ends_with("the two sides are one graph"),
            "{}",
            summary
        );
    }

    /// A failed tactic reports the goal **as it now stands** — the fatal
    /// failure left the graph at the last rewrite that landed, and the
    /// residual carries that state.
    #[test]
    fn a_stuck_tactic_shows_the_goal_standing() {
        let (_ctx, outcome) = prove_with(
            "identity probe { push 1 push 2 add } = { push 4 };",
            "probe",
            Some("lhs(fire(fold) fire(tuple-cancel)) exact"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("there is no tuple to cancel");
        };
        assert!(
            residual.stopped.contains("`lhs(…)`") && residual.stopped.contains("found nothing"),
            "{}",
            residual.stopped
        );
        // The fold landed and stands.
        let graph = &residual.lhs_graph;
        let folded: Vec<NodeId> = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(Value::Int(3)))))
            .map(|(id, _)| id)
            .collect();
        assert_eq!(folded.len(), 1, "the sum was worked out:\n{}", graph);
    }

    #[test]
    fn a_step_that_does_nothing_fails_loudly() {
        let code = "identity probe { is_bool is_bool } = { drop 0 push true };";
        let (_ctx, outcome) = prove_with(code, "probe", Some("inline diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("there are no calls to open");
        };
        assert!(
            residual.stopped.contains("`inline`"),
            "{}",
            residual.stopped
        );
        let (_ctx, outcome) = prove_with(code, "probe", Some("lhs(fire(tuple-cancel)) diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("there is no tuple to cancel");
        };
        assert!(
            residual.stopped.contains("`lhs(…)`"),
            "{}",
            residual.stopped
        );
    }

    /// The introduction, spent in a proof: a side that never packs meets
    /// one that does. `on` states the cancelling pair onto the bare wires
    /// — no search could find it, `id(2)` anchoring nowhere — and the two
    /// sides are one graph.
    #[test]
    fn a_stated_pair_carries_a_side_to_the_packed_shape() {
        let code = "identity probe { swap swap } = { tuple 2 untuple 2 };";
        let (_ctx, outcome) =
            prove_with(code, "probe", Some("lhs(on(in0 in1, tuple-cancel)) exact"));
        let Outcome::Closed { .. } = outcome else {
            panic!("the stated pair meets the packed side: {:?}", outcome);
        };

        // The wire order is the window's shape: the other order states
        // the other tuple, which is not the one the right side builds.
        let (_ctx, outcome) =
            prove_with(code, "probe", Some("lhs(on(in1 in0, tuple-cancel)) exact"));
        let Outcome::Stuck(_) = outcome else {
            panic!("the swapped statement is a different pair: {:?}", outcome);
        };
    }

    #[test]
    fn a_cut_splits_the_goal_and_closes_each_half() {
        // `is_bool ; is_bool` = `is_int ; is_bool`, cut at the normal form
        // both sides reach: two independent goals, each decided by the
        // diagram.
        let (_ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            Some("via { drop(1) ; push true }"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("both halves close");
        };
        assert_eq!(
            proof.summary(),
            "cut (left: the two sides are one diagram; right: the two sides are one diagram)"
        );
    }

    #[test]
    fn a_cut_lets_each_half_take_its_own_road() {
        // The right half compares the waypoint against a call, so it inlines;
        // the left half needs no such thing. Fully independent strategies.
        let (_ctx, outcome) = prove_with(
            r#"
            sentence drop_and_true { drop 0 push true }
            identity probe { is_bool is_bool } = { jump crate::drop_and_true };
            "#,
            "probe",
            Some("via { drop(1) ; push true } (right: inline diagram)"),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("both halves close");
        };
        assert_eq!(
            proof.summary(),
            "cut (left: the two sides are one diagram; right: inline; the two sides are one graph)"
        );
    }

    #[test]
    fn a_swapped_goal_that_sticks_says_which_way_round_it_is() {
        let (_ctx, outcome) = prove_with(
            "identity probe { push 1 } = { push 2 };",
            "probe",
            Some("symm diagram"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("push 2 is not push 1 either way round");
        };
        assert!(
            residual.path.iter().any(|step| step.contains("swapped")),
            "{:?}",
            residual.path
        );
        assert_eq!(
            kinds(&residual.lhs_graph),
            vec![NodeKind::Op(Prim::Push(Value::Int(2)))],
            "`symm` swapped the sides, so the left is what the goal stated \
             on the right"
        );
    }

    #[test]
    fn a_wrong_waypoint_fails_its_half_by_name() {
        // `not` has the right arity but is no midpoint: the left goal,
        // `is_bool ; is_bool` = `not`, is false and says so.
        let (_ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            Some("via { not }"),
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
        let (_ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { is_int is_bool };",
            "probe",
            Some("via { push 1 }"),
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
        let (_ctx, outcome) = prove_identity("identity probe { push 1 } = { push 2 };", "probe");
        let Outcome::Stuck(residual) = outcome else {
            panic!("push 1 is not push 2");
        };
        assert!(
            residual.stopped.contains("different diagrams"),
            "{}",
            residual.stopped
        );
        assert_eq!(
            kinds(&residual.lhs_graph),
            vec![NodeKind::Op(Prim::Push(Value::Int(1)))]
        );
        assert_eq!(
            kinds(&residual.rhs_graph),
            vec![NodeKind::Op(Prim::Push(Value::Int(2)))]
        );
    }

    /// A proof answers for itself: `prove` flattens every close to a run and
    /// certifies it against the goal as stated before answering. A draft
    /// that lies does not flatten, and a run written for a different goal
    /// does not certify, since its steps name boxes this goal never had.
    #[test]
    fn a_proof_that_lies_is_refused() {
        let false_lib = assemble("identity probe { push 1 } = { push 2 };").unwrap();
        let mut ctx = Context::new();
        let idx = false_lib.identity_by_name("probe").unwrap();
        let false_goal = Goal::of_identity(&mut ctx, &false_lib, idx).unwrap();

        // Claimed trivial, and the sides are not one graph: no run.
        let err = proof::flatten(&Proof::Trivial, &false_goal, &mut ctx).unwrap_err();
        assert!(err.contains("not one graph"), "{}", err);

        // An honest run for a different claim does not certify this one:
        // its steps name boxes this goal does not have.
        let true_lib = assemble("identity probe { push 1 push 2 add } = { push 3 };").unwrap();
        let mut true_ctx = Context::new();
        let idx = true_lib.identity_by_name("probe").unwrap();
        let true_goal = Goal::of_identity(&mut true_ctx, &true_lib, idx).unwrap();
        let outcome = Prover::new(&true_lib)
            .prove(&mut true_ctx, true_goal, None)
            .unwrap();
        let Outcome::Closed { run: stolen, .. } = outcome else {
            panic!("the sum folds");
        };
        let err = goal::certify(&false_goal, &stolen, &mut ctx, &false_lib).unwrap_err();
        assert!(err.contains("does not apply"), "{}", err);
    }

    /// `cases` is η and then `select-same`, and the sub-proofs are goals
    /// like any other: the split closes, and the close **certifies**,
    /// which is the load-bearing assertion — the expansion's steps and
    /// each block's spliced run replay blind through the kernel, and the
    /// branch the step put there is closed by the law it is named after.
    #[test]
    fn a_case_split_is_an_expansion_and_a_branch_split() {
        // `is_bool` of anything is a bool, which no window sees: the split
        // is what says the answer is `true` or it is `false`.
        let code = "identity probe { is_bool is_bool } = { drop 0 push true };";
        // The inner test — the one that reads the input. The outer one
        // reads *it*, and is a box of its own, with a name of its own.
        let (lhs, _) = standing(code, "probe", "");
        let at = address(&lhs, |g, id| {
            matches!(g.kind(id), NodeKind::Op(Prim::IsBool)) && g.sources(id) == [Source::Input(0)]
        });
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("cases({}) (true: diagram, false: diagram)", at)),
        );
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("both cases fold on the machine once the answer is a literal");
        };
        let summary = proof.summary();
        assert!(
            summary.starts_with("cases: ") && summary.contains("(true:"),
            "{}",
            summary
        );
    }

    /// A case that fails names which one it stood in, on top of whatever
    /// its own strategy complained about — the same labelling a `via`
    /// half or a `select-same` block gets.
    #[test]
    fn a_failed_case_names_itself() {
        let code = "identity probe { is_bool is_bool } = { drop 0 push true };";
        let (lhs, _) = standing(code, "probe", "");
        let at = address(&lhs, |g, id| {
            matches!(g.kind(id), NodeKind::Op(Prim::IsBool)) && g.sources(id) == [Source::Input(0)]
        });
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!(
                "cases({}) (true: both(fire(tuple-cancel)), false: diagram)",
                at
            )),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("a case of this split holds no tuple to cancel");
        };
        assert!(
            residual
                .path
                .iter()
                .any(|p| p.contains("in the true case of the split")),
            "{:?}",
            residual.path
        );
        assert!(
            residual.stopped.contains("`both(…)`"),
            "{}",
            residual.stopped
        );
    }

    /// The blocks are carved off the **left** side, so a wire only the
    /// right side computes is a `symm` away — and the report says so
    /// rather than leaving an author to guess, which is the same answer
    /// `select-same` gives to the same mistake.
    #[test]
    fn a_wire_on_the_other_side_is_told_which_way_round_the_goal_is() {
        let code = "identity probe { drop 0 push true } = { is_bool is_bool };";
        let (_, rhs) = standing(code, "probe", "");
        let at = address(&rhs, |g, id| {
            matches!(g.kind(id), NodeKind::Op(Prim::IsBool)) && g.sources(id) == [Source::Input(0)]
        });
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("cases({}) (true: diagram, false: diagram)", at)),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the left side computes no such wire");
        };
        assert!(residual.stopped.contains("`symm`"), "{}", residual.stopped);
        // Said apart from an address nothing answers to anywhere, which is
        // a different mistake and gets a different sentence.
        assert!(
            !residual.stopped.contains("nothing there computes that"),
            "{}",
            residual.stopped
        );
    }

    /// The three ways a `cases` address comes to nothing, said apart —
    /// because they are three different mistakes, and only the report
    /// tells an author which one they made.
    #[test]
    fn a_case_split_says_how_its_address_failed() {
        let code = "identity probe \
             { pick 0 push 7 equal branch { push 7 equal } { drop 0 push false } } \
           = { pick 0 push 7 equal branch { drop 0 push true } { drop 0 push false } };";

        // A name nothing answers to: a listing read from before the steps
        // in front of it changed what that box computes.
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some("cases(#zzzzzzzzzzzz) (true: diagram, false: diagram)"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("no box of either side computes that");
        };
        assert!(
            residual
                .stopped
                .contains("names no live box of the left side"),
            "{}",
            residual.stopped
        );

        // A box both sides hold, and nothing promises its answer is a
        // bool — so there is no second case, and no split to make.
        let (lhs, _) = standing(code, "probe", "");
        let at = address(&lhs, |g, id| {
            matches!(g.kind(id), NodeKind::Op(Prim::Push(Value::Int(7))))
        });
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("cases({}) (true: diagram, false: diagram)", at)),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("a literal seven is no case analysis");
        };
        assert!(
            residual.stopped.contains("finds nothing to split on"),
            "{}",
            residual.stopped
        );

        // And a prefix several boxes answer to is not a name at all: it
        // wants lengthening, and the report says to what. Seventeen boxes
        // against sixteen letters, so two of them start alike whatever
        // the letters turn out to be.
        let wide = "identity wide \
             { push 1 push 2 add push 3 add push 4 add push 5 add push 6 add \
               push 7 add push 8 add push 9 add } = { push 45 };";
        let (lhs, _) = standing(wide, "wide", "");
        let mut sharing: HashMap<char, usize> = HashMap::new();
        for (id, _) in lhs.live() {
            let first = lhs.address(id).letters().chars().next().expect("letters");
            *sharing.entry(first).or_default() += 1;
        }
        let (&letter, _) = sharing
            .iter()
            .find(|(_, held)| **held > 1)
            .expect("sixteen letters cannot tell seventeen boxes apart");
        let (_ctx, outcome) = prove_with(
            wide,
            "wide",
            Some(&format!(
                "cases(#{}) (true: diagram, false: diagram)",
                letter
            )),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("an ambiguous address is not a name");
        };
        assert!(
            residual.stopped.contains("boxes of the left side"),
            "{}",
            residual.stopped
        );
    }

    /// Which of the corpus's identities the bare table decides, pinned:
    /// calls opened, every law to fixpoint, and the sides one graph. The
    /// two that are not here need what no rewrite window can say — a case
    /// split on an opaque answer — and their `.hant` proofs spend it with
    /// `cases`.
    ///
    /// Printed as a list rather than counted so a table change shows
    /// exactly which claims moved — in either direction: one going quiet
    /// is a regression, and one starting to close is the cue to shorten
    /// the proofs.
    #[test]
    fn the_corpus_identities_the_table_decides() {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(std::path::Path::parent)
            .expect("the crate sits in the workspace, beside the corpus")
            .join("hana");
        let mut corpus = crate::corpus::load(&tests).unwrap();
        let library = &corpus.library;
        let terms = &mut corpus.terms;
        let mut closed = Vec::new();
        for (idx, identity) in library.identities.iter_enumerated() {
            let mut goal = Goal::of_identity(terms, library, idx).unwrap();
            proof::inline(&mut goal.lhs, terms, library, None).unwrap();
            proof::inline(&mut goal.rhs, terms, library, None).unwrap();
            for side in [&mut goal.lhs, &mut goal.rhs] {
                let mut deriv = kernel::rules::Derivation::default();
                tactic::run(side, &mut deriv, &tactic::decide()).unwrap();
            }
            if graph::isomorphic(&goal.lhs, &goal.rhs) {
                closed.push(identity.name.clone());
            }
        }
        assert_eq!(
            closed,
            [
                "identities::testing_a_test",
                "identities::a_value_tested_twice",
                "identities::copying_a_constant",
                "identities::discarded_work_on_copies",
                "identities::testing_a_test_by_name",
                "identities::two_spellings_of_one_test",
                "identities::a_test_inside_an_arm",
                "identities::a_test_inside_an_arm_with_a_prefix",
                "identities::the_guard_a_split_leaves",
                "identities::taking_a_frame_off",
                "identities::comparing_two_built_tuples",
                "identities::a_tuple_of_literals_is_a_literal",
                "identities::a_literal_taken_apart_is_its_parts",
                "identities::the_empty_tuple_is_a_literal",
                "identities::untupling_and_retupling_is_the_coercion",
                // The table reaches this one by taking the pair *down* on
                // the right; its `.hant` proof takes the other road — the
                // stated introduction with its reader-split — on purpose.
                "identities::a_pair_for_one_reader_only",
                "identities::a_branch_between_what_it_compared_answers_with_it",
                "identities::a_coerced_tuple_survives_the_round_trip",
                "identities::a_built_tuple_is_the_width_it_was_built",
                "identities::a_built_tuple_is_no_other_width",
                "identities::two_branches_on_one_condition_are_one_branch",
                // The rows that were `not yet written`, each decided by
                // `decide` alone now that it has them — every one of these
                // failed honestly before. `comm` is the one of the new rows
                // missing here, and it is missing on purpose: it permutes
                // rather than shrinking, so no list drives it and
                // `the_operands_of_a_sum_are_interchangeable` names it.
                "identities::an_or_with_a_falsy_literal",
                "identities::an_or_with_a_truthy_literal",
                "identities::a_negated_condition_swaps_the_arms",
                "identities::coercing_to_int_twice_is_coercing_once",
                "identities::coercing_to_a_tuple_twice_is_coercing_once",
                "identities::a_promised_bool_is_no_tuple",
                "identities::a_promised_bool_is_no_integer",
            ],
            "the table's reach changed"
        );
    }

    /// The loop an addressed step exists to close: a stuck goal prints a
    /// listing keyed by address, and the address it printed is what the
    /// next step writes back — in full, or in the prefix the listing
    /// emphasised. `fire` cannot say "that one"; `at` is how the proof
    /// answers the report in the report's own words.
    #[test]
    fn a_proof_can_name_the_box_the_residual_printed() {
        use crate::kernel::graph::NodeKind;
        use crate::render;

        let code = "identity probe { push 1 push 2 add } = { push 3 };";

        // A reached `exact` fails — the report is its whole job.
        let (_ctx, outcome) = prove_with(code, "probe", Some("exact"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("the sides are not one diagram yet");
        };
        let (add, _) = residual
            .lhs_graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Add)))
            .expect("the sum, unspent");
        let address = residual.lhs_graph.address(add);
        let listing = render::listing(&residual.lhs_graph, "left").to_string();
        assert!(
            listing.contains(&address.letters()),
            "the listing names the box a proof would name:\n{}",
            listing
        );

        // …and the name is the whole address, or the prefix the listing
        // emphasised: either is what that box is called.
        for written in [
            address.to_string(),
            format!("#{}", residual.lhs_graph.shortest(add)),
        ] {
            let (_ctx, outcome) = prove_with(
                code,
                "probe",
                Some(&format!("lhs(at({}, fold)) diagram", written)),
            );
            let Outcome::Closed { draft: proof, .. } = outcome else {
                panic!("the named box is a fold the machine can work out");
            };
            assert!(
                proof.summary().contains("lhs: 1 rewrite"),
                "{}",
                proof.summary()
            );
        }

        // A box the side does not have is its own mistake, said as one.
        let (_ctx, outcome) =
            prove_with(code, "probe", Some("lhs(at(#zzzzzzzzzzzz, fold)) diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("no box is called that")
        };
        assert!(
            residual.stopped.contains("#zzzzzzzzzzzz is not a live box"),
            "{}",
            residual.stopped
        );

        // So is a box that is there with nothing of that law to fire.
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("lhs(at({}, equal-refl)) diagram", address)),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("an `add` is no `equal`")
        };
        assert!(
            residual
                .stopped
                .contains(&format!("no forward `equal-refl` match holds {}", address)),
            "{}",
            residual.stopped
        );
    }

    /// The other splitter: the goal's left side answers with a branch, so
    /// each block answers for itself against the right side.
    #[test]
    fn a_branch_answers_block_by_block() {
        let code = r#"
            #[arity(1,1)] sentence drop_and_true { drop 0 push true }
            identity probe
                { branch { jump crate::drop_and_true } { drop 0 push true } }
              = { drop 0 drop 0 push true };
        "#;
        // The driver alone cannot: a call is opaque, so the two blocks are
        // not the one block `select-same` would need to see.
        let (_ctx, outcome) = prove_identity(code, "probe");
        assert!(matches!(outcome, Outcome::Stuck(_)));

        // Split, and each block takes its own road — the false one needing
        // no steps at all, since it is already what the right side says.
        let (_ctx, outcome) = prove_with(code, "probe", Some("select-same (then: inline diagram)"));
        let Outcome::Closed { draft: proof, .. } = outcome else {
            panic!("both blocks answer to the right side");
        };
        assert_eq!(
            proof.summary(),
            "select-same (then: inline; the two sides are one graph; \
             else: the two sides are one graph)"
        );
    }

    /// A block that does not close says which block it was, and shows that
    /// block against the right side rather than the branch it came out of.
    #[test]
    fn a_block_that_sticks_names_itself() {
        let (_ctx, outcome) = prove_with(
            "identity probe { branch { push 1 } { push 2 } } = { drop 0 push 1 };",
            "probe",
            Some("select-same"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("`push 2` is not `push 1`");
        };
        assert!(
            residual.path.iter().any(|p| p.contains("else block")),
            "{:?}",
            residual.path
        );
        assert_eq!(
            kinds(&residual.lhs_graph),
            vec![NodeKind::Op(Prim::Push(Value::Int(2)))],
            "the left is the block, not the branch it was carved from"
        );
    }

    /// The step reads the left side, and says so when the left side is not
    /// a branch — `symm` being how a proof says it is the other one.
    #[test]
    fn a_side_that_is_no_branch_is_refused() {
        let code = "identity probe { drop 0 push true } = { branch { push true } { push true } };";
        let (_ctx, outcome) = prove_with(code, "probe", Some("select-same"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("the left side is a literal");
        };
        assert!(
            residual.stopped.contains("answer with one branch"),
            "{}",
            residual.stopped
        );

        // Turned round, the same claim splits.
        let (_ctx, outcome) = prove_with(code, "probe", Some("symm select-same"));
        assert!(matches!(outcome, Outcome::Closed { .. }));

        // And the checker asks the same question the step did, rather than
        // taking a proof's word that a split happened: it carves the two
        // blocks off the goal itself, so a claimed split of a side that is
        // no branch has nothing to carve.
        let library = assemble(code).unwrap();
        let mut ctx = Context::new();
        let idx = library.identity_by_name("probe").unwrap();
        let goal = Goal::of_identity(&mut ctx, &library, idx).unwrap();
        let draft = Proof::SelectSame {
            then_sub: Box::new(Proof::Trivial),
            else_sub: Box::new(Proof::Trivial),
        };
        let err = proof::flatten(&draft, &goal, &mut ctx).unwrap_err();
        assert!(err.contains("does not answer with one branch"), "{}", err);
    }

    /// A branch is not the *whole* answer when something else is answered
    /// beside it: two answers, and the law has nothing to say about them.
    /// Either end of the answer is enough to refuse it.
    #[test]
    fn a_branch_answering_only_part_is_refused() {
        for (lhs, rhs) in [
            // The branch answers the top, something else the rest…
            (
                "push 9 roll 1 branch { push 1 } { push 1 }",
                "drop 0 push 9 push 1",
            ),
            // …and the other way round.
            (
                "branch { push 1 } { push 1 } push 9",
                "drop 0 push 1 push 9",
            ),
        ] {
            let code = format!("identity probe {{ {} }} = {{ {} }};", lhs, rhs);
            let (_ctx, outcome) = prove_with(&code, "probe", Some("select-same"));
            let Outcome::Stuck(residual) = outcome else {
                panic!("`{}` answers more than the branch does", lhs);
            };
            assert!(
                residual.stopped.contains("answer with one branch"),
                "{}",
                residual.stopped
            );
        }
    }
}
