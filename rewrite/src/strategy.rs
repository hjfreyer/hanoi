//! The interpreter for the strategy language of [`crate::hant`].
//!
//! A proof mirrors a tree of goals, and a goal is two
//! [graphs](crate::diagram2). A strategy acts on one: manipulations
//! transform it — the tactic steps rewrite a side in place, `inline` opens
//! calls, `symm` turns it — a splitter (`via`) replaces it with independent
//! subgoals each carrying its own strategy, and `diagram` closes it. A goal
//! whose sides have become **isomorphic** closes on its own, before any
//! step runs, which is what `exact`'s claim tests. The default — what an
//! identity with no written proof gets — is `diagram` alone.
//!
//! The closer **is** the table now: `diagram` rewrites both sides by
//! [`tactic::decide`](crate::diagram2::tactic::decide) — every law, to
//! fixpoint, `view-value` held to last — and asks whether they landed on
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
//! [`Derivation::push`](crate::diagram2::rules::Derivation::push): the
//! whole file is untrusted convenience over the table.
//!
//! A stuck goal's residual is **narrowed** for the report — the two sides
//! read back into terms, shared affixes stripped, the differing arm
//! entered — because when the engine says no, where the difference lives
//! is the thing worth printing. A stuck *tactic* reports the goal as it
//! now stands: a failed run leaves its graph at the last step that landed,
//! and showing that state is the point of the guarantee.

use std::collections::HashSet;

use std::collections::HashMap;

use bytecode::{IdentityIndex, Library};

use crate::diagram2::rules::{self, Derivation, Law};
use crate::diagram2::tactic::{Region, Tactic};
use crate::diagram2::{self, read_back, tactic};
use crate::goal::{Goal, Outcome, Proof, Residual, against};
use crate::graph::{self, BranchId, Graph, NodeId, Source};
use crate::hant::{Body, OnSide, Step, Strategy, default_strategy};
use crate::term::{Context, Error, Prim, Term, TermIndex};

/// One side of a goal, picked out for a mutation that borrows it alone.
type Pick = fn(&mut Goal) -> &mut Graph;

/// An identity already proved, in the form another proof can spend it: the
/// left side as it was built, and the run that took it to the right.
struct Lemma {
    lhs: Graph,
    run: Vec<diagram2::rules::Step>,
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
    /// What each closed identity left behind: the run a `by` may spend, or
    /// why its proof is not one. Keeping the refusal is the point — a claim
    /// that closed and cannot be carried is a different report from one that
    /// has not closed at all, and a proof that names it deserves to be told
    /// which.
    lemmas: HashMap<IdentityIndex, Result<Lemma, String>>,
}

impl<'l> Prover<'l> {
    pub fn new(library: &'l Library) -> Self {
        Prover {
            library,
            lemmas: HashMap::new(),
        }
    }

    /// Records a closed identity so later proofs may spend it with `by`.
    ///
    /// `lhs` is the goal's left side as it was *built* — a `by` looks for
    /// that graph, so it has to be the same one the run was written against.
    /// The run itself is [`Proof::one_sided`]'s answer, and where there is
    /// none the reason is recorded in its place, to be handed to whatever
    /// `by` goes looking.
    pub fn learn(&mut self, idx: IdentityIndex, lhs: Graph, proof: &Proof) {
        let learned = proof.one_sided().map(|run| Lemma { lhs, run });
        self.lemmas.insert(idx, learned);
    }

    /// Runs a strategy on a goal — the written one, or the default
    /// `diagram` when the identity carries no proof — and **re-checks**
    /// whatever proof comes back against the goal as stated, before
    /// answering. A close is never this module's word: [`Proof::check`]
    /// replays every recorded step through the table and asks every
    /// isomorphism again, and a proof that does not check comes back
    /// [`Outcome::Stuck`] — fail closed — naming the prover bug it is.
    pub fn prove(
        &self,
        ctx: &mut Context,
        goal: Goal,
        strategy: Option<&Strategy<Body>>,
    ) -> Result<Outcome, Error> {
        let default = default_strategy();
        let strategy = strategy.unwrap_or(&default);
        let stated = goal.clone();
        let outcome = self.run(ctx, strategy, goal)?;
        if let Outcome::Closed(proof) = &outcome
            && let Err(why) = proof.check(stated.clone(), ctx, self.library)
        {
            let why = format!(
                "the proof did not re-check — a prover bug, and the claim is not \
                 accepted on its word: {}",
                why
            );
            return Ok(Outcome::Stuck(gave_up(ctx, &stated, &why)));
        }
        Ok(outcome)
    }

    /// One strategy on one goal. A goal whose sides are one graph —
    /// isomorphic — is closed before any step runs, at every level, so a
    /// cut's side that a manipulation made trivial needs no steps of its
    /// own.
    fn run(
        &self,
        ctx: &mut Context,
        strategy: &[Step<Body>],
        goal: Goal,
    ) -> Result<Outcome, Error> {
        if graph::isomorphic(&goal.lhs, &goal.rhs) {
            return Ok(Outcome::Closed(Proof::Trivial));
        }
        let Some((head, rest)) = strategy.split_first() else {
            return Ok(Outcome::Stuck(gave_up(
                ctx,
                &goal,
                "the strategy ended with the goal still open",
            )));
        };
        match head {
            // Both sides rewritten by the whole table to fixpoint; either
            // they land on one diagram or the claim is beyond the table.
            // Every rewrite is an instance of a named law checked by
            // `rules::apply`, so the closer's verdict is a derivation's
            // worth of checked steps and one isomorphism. The residual
            // reads back what each side became, narrowed to where they
            // differ.
            Step::Diagram => {
                let mut goal = goal;
                let mut spent: [Vec<diagram2::rules::Step>; 2] = [Vec::new(), Vec::new()];
                let picks: [Pick; 2] = [|g| &mut g.lhs, |g| &mut g.rhs];
                for (pick, record) in picks.into_iter().zip(&mut spent) {
                    let mut deriv = diagram2::rules::Derivation::default();
                    if let Err(e) = tactic::run(pick(&mut goal), &mut deriv, &tactic::decide()) {
                        let why = format!("`diagram`'s drive failed: {}", e);
                        return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                    }
                    *record = deriv.steps().cloned().collect();
                }
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    let [lhs, rhs] = spent;
                    return Ok(Outcome::Closed(Proof::Diagram { lhs, rhs }));
                }
                let (l, r) = (read_back(&goal.lhs, ctx), read_back(&goal.rhs, ctx));
                let (mut path, lhs, rhs) = narrow(ctx, l, r);
                path.insert(0, "as diagrams".to_string());
                Ok(Outcome::Stuck(Residual {
                    lhs_graph: goal.lhs.clone(),
                    rhs_graph: goal.rhs.clone(),
                    lhs,
                    rhs,
                    path,
                    stopped: "the two sides rewrite to different diagrams: the claim is \
                              false, or true only for reasons the table cannot yet say"
                        .to_string(),
                }))
            }

            // Case analysis on an intermediate result, as a checked
            // rewrite: the operation's answer is `true` or `false` and
            // nothing else, so everything downstream of it becomes a
            // branch over both assumptions — the table's Shannon row,
            // fired once per side through `apply` like any rewrite. The
            // step picks the earliest such answer (the box with the least
            // upstream), because splitting on a late result says nothing
            // usable about the computations feeding it; a side without
            // the operation is left standing, and everything after the
            // expansion is the table's business. A manipulation, not a
            // closer: what it leaves is a goal.
            //
            // The arms, when the proof wrote them, run per-case
            // sub-strategies scoped to the fresh branch — the hypothesis
            // spent as structure — landing their steps in the same
            // per-side records as the split, so the proof object and its
            // checker never learn a hypothesis existed.
            Step::Cases {
                prim,
                literal,
                then_arm,
                else_arm,
            } => {
                let mut goal = goal;
                let mut derivs = [Derivation::default(), Derivation::default()];
                let counts = match self.cases_step(
                    ctx,
                    &mut goal,
                    &mut derivs,
                    [Scope::Whole, Scope::Whole],
                    prim,
                    literal.as_deref(),
                    then_arm,
                    else_arm,
                ) {
                    Ok(counts) => counts,
                    Err(residual) => return Ok(Outcome::Stuck(*residual)),
                };
                let [l, r] = derivs;
                let (lhs, rhs) = (l.steps().cloned().collect(), r.steps().cloned().collect());
                let arms = (then_arm.is_some() || else_arm.is_some())
                    .then_some((counts.then_steps, counts.else_steps));
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Cases {
                        lhs,
                        rhs,
                        splits: counts.splits,
                        arms,
                        sub: Box::new(sub),
                    }),
                    Outcome::Stuck(mut residual) => {
                        residual.path.insert(0, "after the case split".to_string());
                        Outcome::Stuck(residual)
                    }
                })
            }

            // A goal whose sides are one graph closed above, before any
            // step ran — so an `exact` that is reached is an `exact` whose
            // claim is false, and its whole job is the report: the goal
            // exactly as it stands, no normalization to reshape it and no
            // narrowing to walk into it. That unaltered residual is what
            // the step is usually written for — `exact` alone shows the
            // identity as built and aligned, and after a manipulation it
            // shows what the manipulation left, in the language a waypoint
            // is written in.
            Step::Exact => Ok(Outcome::Stuck(gave_up(
                ctx,
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
                let mut spent: [Vec<diagram2::rules::Step>; 2] = [Vec::new(), Vec::new()];
                let picks: &[(Pick, usize)] = match side {
                    OnSide::Lhs => &[(|g| &mut g.lhs, 0)],
                    OnSide::Rhs => &[(|g| &mut g.rhs, 1)],
                    OnSide::Both => &[(|g| &mut g.lhs, 0), (|g| &mut g.rhs, 1)],
                };
                for &(pick, at) in picks {
                    let mut deriv = diagram2::rules::Derivation::default();
                    match tactic::run(pick(&mut goal), &mut deriv, tactic) {
                        Ok(_) => spent[at] = deriv.steps().cloned().collect(),
                        Err(e) => {
                            let why = format!("`{}(…)`: {}", side.word(), e);
                            return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                        }
                    }
                }
                let [lhs, rhs] = spent;
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Rewrote {
                        side: side.word(),
                        lhs,
                        rhs,
                        sub: Box::new(sub),
                    }),
                    Outcome::Stuck(mut residual) => {
                        residual
                            .path
                            .insert(0, format!("after rewriting {}", side.word()));
                        Outcome::Stuck(residual)
                    }
                })
            }

            // Another identity, spent where it occurs. Not an axiom: what
            // lands is that identity's own proof, carried through the
            // embedding of its left side in this one — so the steps recorded
            // here are ordinary rewrites in this goal's coordinates, and
            // `Proof::check` re-applies them knowing nothing of lemmas.
            Step::By { side, of } => {
                let Body::Lemma(idx) = *of else {
                    return Ok(Outcome::Stuck(gave_up(
                        ctx,
                        &goal,
                        "`by` was handed something that is not an identity",
                    )));
                };
                let name = self.library.identities[idx].name.as_str();
                let lemma = match self.lemmas.get(&idx) {
                    Some(Ok(lemma)) => lemma,
                    Some(Err(why)) => {
                        let why = format!(
                            "`{}(by {})`: that identity closed, but its proof cannot be \
                             carried anywhere — {}",
                            side.word(),
                            name,
                            why
                        );
                        return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                    }
                    None => {
                        let why = format!(
                            "`{}(by {})`: that identity is not proved, so there is nothing \
                             to spend",
                            side.word(),
                            name
                        );
                        return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                    }
                };
                let mut goal = goal;
                let mut spent: [Vec<diagram2::rules::Step>; 2] = [Vec::new(), Vec::new()];
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
                    let Some(found) = graph::find(host, &lemma.lhs).into_iter().next() else {
                        let why = format!(
                            "`{}(by {})`: that identity's left side does not occur here",
                            side.word(),
                            name
                        );
                        return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                    };
                    match rules::transplant(host, &lemma.lhs, &found, &lemma.run) {
                        Ok(run) => spent[at] = run.steps().cloned().collect(),
                        Err(e) => {
                            let why = format!("`{}(by {})`: {}", side.word(), name, e);
                            return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                        }
                    }
                }
                let [lhs, rhs] = spent;
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Rewrote {
                        side: side.word(),
                        lhs,
                        rhs,
                        sub: Box::new(sub),
                    }),
                    Outcome::Stuck(mut residual) => {
                        residual.path.insert(
                            0,
                            format!("after spending an identity on the {}", side.word()),
                        );
                        Outcome::Stuck(residual)
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
                    return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                }
                // Two goals, fully independent from here: each side takes its
                // own road, and proving both proves the whole by transitivity.
                let (lhs, stone) = against(ctx, &goal.lhs, waypoint);
                let sub = Goal { lhs, rhs: stone };
                let left_sub = match self.side(ctx, "in the left half of the cut", left, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                let (rhs, stone) = against(ctx, &goal.rhs, waypoint);
                let sub = Goal { lhs: stone, rhs };
                let right_sub = match self.side(ctx, "in the right half of the cut", right, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                Ok(Outcome::Closed(Proof::Cut {
                    waypoint,
                    left_sub,
                    right_sub,
                }))
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
                let mut goal = goal;
                let opened = diagram2::inline(&mut goal.lhs, ctx, self.library, only)?
                    + diagram2::inline(&mut goal.rhs, ctx, self.library, only)?;
                if opened == 0 {
                    let why = match only {
                        None => "`inline` found no calls to open".to_string(),
                        Some(idx) => format!(
                            "`inline({})` found no call to it here",
                            self.library.names[idx]
                        ),
                    };
                    return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                }
                let name = only.map(|idx| self.library.names[idx].clone());
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined {
                        target: only,
                        name,
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
            Outcome::Closed(p) => Ok(Box::new(p)),
            Outcome::Stuck(mut residual) => {
                residual.path.insert(0, label.to_string());
                Err(residual)
            }
        })
    }

    /// One `cases` step, bare or structured, possibly nested: fire the
    /// split per goal side, then run each written arm. Everything lands in
    /// `derivs` — one derivation per goal side, alive for the whole step
    /// so a structured split's arm steps append after its own, which is
    /// what lets [`Proof::Cases`] replay flat.
    #[allow(clippy::too_many_arguments)]
    fn cases_step(
        &self,
        ctx: &mut Context,
        goal: &mut Goal,
        derivs: &mut [Derivation; 2],
        scopes: [Scope; 2],
        prim: &Prim,
        literal: Option<&str>,
        then_arm: &Option<Strategy<Body>>,
        else_arm: &Option<Strategy<Body>>,
    ) -> Result<CaseCounts, Box<Residual>> {
        let mut counts = CaseCounts {
            splits: 0,
            then_steps: 0,
            else_steps: 0,
        };
        let mut branches: [Option<BranchId>; 2] = [None, None];
        let picks: [Pick; 2] = [|g| &mut g.lhs, |g| &mut g.rhs];
        for i in 0..2 {
            let within = match &scopes[i] {
                Scope::Whole => None,
                Scope::In(set) => Some(set),
                Scope::Skip => continue,
            };
            let side = picks[i](goal);
            let Some(wire) = outermost(side, prim, literal, within) else {
                continue;
            };
            let split = diagram2::rules::propose(side, &[Law::Shannon], wire)
                .into_iter()
                .next();
            let Some(split) = split else {
                continue;
            };
            if let Err(e) = derivs[i].push(side, split) {
                let why = format!("`cases` proposed a split the checker refused: {}", e);
                return Err(Box::new(gave_up(ctx, goal, &why)));
            }
            // The Shannon replacement mints its select's branch after the
            // arms it implants, so the introduced branch is the last one
            // the recorded inverse carries — the handle the arms scope to.
            branches[i] = derivs[i]
                .latest_undo()
                .and_then(|back| back.at.branches.last().copied());
            counts.splits += 1;
        }
        if branches.iter().all(Option::is_none) {
            return Err(Box::new(gave_up(
                ctx,
                goal,
                "`cases` finds nothing to split on: no side holds the operation \
                 with anything downstream of its answer",
            )));
        }
        counts.then_steps = self.arm(ctx, goal, derivs, &branches, prim, true, then_arm)?;
        counts.else_steps = self.arm(ctx, goal, derivs, &branches, prim, false, else_arm)?;
        Ok(counts)
    }

    /// One written arm of a structured `cases`: its steps, run with every
    /// rewrite scoped to this case's side of the fresh branch on each goal
    /// side that still holds it. A goal side that never split — or whose
    /// branch earlier work already collapsed, discharge being the point —
    /// skips quietly, the way a bare `cases` leaves a side without the
    /// operation standing. Answers how many steps the arm landed.
    #[allow(clippy::too_many_arguments)]
    fn arm(
        &self,
        ctx: &mut Context,
        goal: &mut Goal,
        derivs: &mut [Derivation; 2],
        branches: &[Option<BranchId>; 2],
        prim: &Prim,
        case: bool,
        strategy: &Option<Strategy<Body>>,
    ) -> Result<usize, Box<Residual>> {
        let Some(strategy) = strategy else {
            return Ok(0);
        };
        let case_word = if case { "true" } else { "false" };
        let stood_in = |residual: &mut Residual| {
            residual.path.insert(
                0,
                format!("in the {} case of the split on `{}`", case_word, prim),
            );
        };
        // Which goal sides still hold the branch, read at entry; a branch
        // that vanishes mid-arm is the next step's business, loudly.
        let active: [Option<BranchId>; 2] = [0, 1].map(|i| {
            branches[i].filter(|&branch| {
                let side = if i == 0 { &goal.lhs } else { &goal.rhs };
                tactic::arm_nodes(side, branch, case).is_some()
            })
        });
        let mut landed = 0;
        for step in strategy {
            match step {
                Step::Rewrite { side, tactic: t } => {
                    let sides: &[usize] = match side {
                        OnSide::Lhs => &[0],
                        OnSide::Rhs => &[1],
                        OnSide::Both => &[0, 1],
                    };
                    for &i in sides {
                        let Some(branch) = active[i] else {
                            continue;
                        };
                        let wrapped = Tactic::Within(
                            Region::Arm { branch, side: case },
                            Box::new((**t).clone()),
                        );
                        let graph = if i == 0 { &mut goal.lhs } else { &mut goal.rhs };
                        let mark = derivs[i].len();
                        if let Err(e) = tactic::run(graph, &mut derivs[i], &wrapped) {
                            let why = format!("`{}(…)`: {}", side.word(), e);
                            let mut residual = gave_up(ctx, goal, &why);
                            stood_in(&mut residual);
                            return Err(Box::new(residual));
                        }
                        landed += derivs[i].len() - mark;
                    }
                }
                Step::Cases {
                    prim: inner,
                    literal,
                    then_arm,
                    else_arm,
                } => {
                    let scopes = [0, 1].map(|i| match active[i] {
                        None => Scope::Skip,
                        Some(branch) => {
                            let side = if i == 0 { &goal.lhs } else { &goal.rhs };
                            match tactic::arm_nodes(side, branch, case) {
                                Some(set) => Scope::In(set),
                                None => Scope::Skip,
                            }
                        }
                    });
                    let sub = self
                        .cases_step(
                            ctx,
                            goal,
                            derivs,
                            scopes,
                            inner,
                            literal.as_deref(),
                            then_arm,
                            else_arm,
                        )
                        .map_err(|mut residual| {
                            stood_in(&mut residual);
                            residual
                        })?;
                    landed += sub.splits + sub.then_steps + sub.else_steps;
                }
                other => unreachable!(
                    "validate refused `{}` inside a `cases` arm at parse time",
                    other
                ),
            }
        }
        Ok(landed)
    }
}

/// How a `cases` step scopes each goal side when it looks for the wire to
/// split on: the whole side at the top level; an enclosing arm's boxes
/// when nested, so the split picks the arm's own retest rather than the
/// test the enclosing split already spent; or not at all, for a side the
/// enclosing split never touched.
enum Scope {
    Whole,
    In(HashSet<NodeId>),
    Skip,
}

/// What one `cases` step spent, for the proof's summary: how many
/// expansions fired, and how many steps each written arm landed (both
/// goal sides summed, nested splits included).
struct CaseCounts {
    splits: usize,
    then_steps: usize,
    else_steps: usize,
}

/// Whether one of a box's operands is the pushed literal `want` names —
/// by its full spelling, or by any tail of it from a `::` boundary, the
/// way an `inline` label names a sentence.
fn names_literal(g: &Graph, id: NodeId, want: &str) -> bool {
    g.sources(id).iter().any(|src| match *src {
        Source::Port { node, port: 0 } => match g.kind(node) {
            graph::NodeKind::Op(Prim::Push(v)) => {
                let spelled = format!("{}", v);
                spelled == want || spelled.ends_with(&format!("::{}", want))
            }
            _ => false,
        },
        _ => false,
    })
}

/// The box of one operation with the least upstream — the outermost
/// decision, which is the one worth splitting on first: everything
/// downstream of it is what the split decides. Ties break by id. Held to
/// `within` when a nested split looks only inside its enclosing arm, and
/// to the boxes testing against a named literal when the proof addressed
/// the wire by what it tests.
fn outermost(
    g: &Graph,
    prim: &Prim,
    literal: Option<&str>,
    within: Option<&HashSet<NodeId>>,
) -> Option<NodeId> {
    let cone = |id: NodeId| {
        let mut seen = HashSet::new();
        let mut todo = vec![id];
        while let Some(node) = todo.pop() {
            if !seen.insert(node) {
                continue;
            }
            for src in g.sources(node) {
                if let Source::Port { node, .. } = *src {
                    todo.push(node);
                }
            }
        }
        seen.len()
    };
    g.live()
        .filter(|(id, _)| within.is_none_or(|set| set.contains(id)))
        .filter(|(_, k)| matches!(k, graph::NodeKind::Op(p) if p == prim))
        .filter(|(id, _)| literal.is_none_or(|want| names_literal(g, *id, want)))
        .map(|(id, _)| id)
        .min_by_key(|&id| (cone(id), id))
}

/// A residual for a strategy that failed before any engine ran: the goal as
/// it stands — read back into the term language a report is written in —
/// and why the step gave up. For a failed tactic "as it stands" is the
/// point: the graph reflects the last rewrite that landed.
fn gave_up(ctx: &mut Context, goal: &Goal, why: &str) -> Residual {
    Residual {
        lhs_graph: goal.lhs.clone(),
        rhs_graph: goal.rhs.clone(),
        lhs: read_back(&goal.lhs, ctx),
        rhs: read_back(&goal.rhs, ctx),
        path: Vec::new(),
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
/// Sound for pointing (any remaining difference must live inside what is
/// kept), and only for pointing: the narrowed pair may be equal for reasons
/// the stripped context supplied.
fn narrow(
    ctx: &mut Context,
    lhs: TermIndex,
    rhs: TermIndex,
) -> (Vec<String>, TermIndex, TermIndex) {
    let mut path = Vec::new();
    let (mut lhs, mut rhs) = (lhs, rhs);
    loop {
        if let Some(((l, r), prefix, suffix)) = peel(ctx, lhs, rhs) {
            path.push(match (prefix, suffix) {
                (p, 0) => format!("past {} shared leading part(s)", p),
                (0, s) => format!("before {} shared trailing part(s)", s),
                (p, s) => format!("between {} shared leading and {} trailing part(s)", p, s),
            });
            (lhs, rhs) = (l, r);
            continue;
        }
        if let (
            &Term::Branch {
                if_true: t1,
                if_false: e1,
            },
            &Term::Branch {
                if_true: t2,
                if_false: e2,
            },
        ) = (ctx.get(lhs), ctx.get(rhs))
        {
            let (thens, elses) = (ctx.equal(t1, t2), ctx.equal(e1, e2));
            if thens && !elses {
                path.push("in the else arm".to_string());
                (lhs, rhs) = (e1, e2);
                continue;
            }
            if elses && !thens {
                path.push("in the then arm".to_string());
                (lhs, rhs) = (t1, t2);
                continue;
            }
        }
        return (path, lhs, rhs);
    }
}

/// Strips what the two compose spines share at either end. Answers the
/// narrowed pair and how much went, or `None` when nothing does. Report
/// machinery: it reads the *terms* a residual is written in, and the goal
/// itself never comes here.
fn peel(
    ctx: &mut Context,
    l: TermIndex,
    r: TermIndex,
) -> Option<((TermIndex, TermIndex), usize, usize)> {
    let lhs = spine(ctx, l);
    let rhs = spine(ctx, r);

    let prefix = lhs
        .iter()
        .zip(&rhs)
        .take_while(|(a, b)| ctx.equal(**a, **b))
        .count();
    // Never peel a whole side away twice over: if the spines are equal the
    // pair was trivial, and the caller handled it.
    let rest = lhs.len().min(rhs.len()) - prefix;
    let suffix = lhs
        .iter()
        .rev()
        .zip(rhs.iter().rev())
        .take(rest)
        .take_while(|(a, b)| ctx.equal(**a, **b))
        .count();
    if prefix + suffix == 0 {
        return None;
    }

    // The width flowing across the cut, read off the last stripped part.
    let boundary = if prefix > 0 {
        ctx.arity(lhs[prefix - 1]).outputs
    } else {
        ctx.arity(l).inputs
    };
    let narrowed = (
        rebuild(ctx, &lhs[prefix..lhs.len() - suffix], boundary),
        rebuild(ctx, &rhs[prefix..rhs.len() - suffix], boundary),
    );
    Some((narrowed, prefix, suffix))
}

/// A term's compose spine, outermost first: the flattening of `;`.
fn spine(ctx: &Context, term: TermIndex) -> Vec<TermIndex> {
    fn walk(ctx: &Context, term: TermIndex, out: &mut Vec<TermIndex>) {
        match ctx.get(term) {
            &Term::Compose(a, b) => {
                walk(ctx, a, out);
                walk(ctx, b, out);
            }
            _ => out.push(term),
        }
    }
    let mut out = Vec::new();
    walk(ctx, term, &mut out);
    out
}

/// A spine segment back as a term; an empty segment is the identity on the
/// width that flowed across it.
///
/// The parts are pointed at rather than copied: what a peel keeps is the same
/// subterms the goal was already made of.
fn rebuild(ctx: &mut Context, parts: &[TermIndex], width_if_empty: usize) -> TermIndex {
    let Some((first, rest)) = parts.split_first() else {
        return ctx.id(width_if_empty);
    };
    rest.iter()
        .fold(*first, |acc, next| ctx.push(Term::Compose(acc, *next)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hant::parse_hant;
    use bytecode::assemble;

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
        let Outcome::Closed(proof) = outcome else {
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
        assert!(matches!(outcome, Outcome::Closed(_)));
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
        let Outcome::Closed(proof) = outcome else {
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
        let Outcome::Closed(proof) = outcome else {
            panic!("the opened goal is one graph");
        };
        assert_eq!(proof.summary(), "inline; the two sides are one graph");
    }

    #[test]
    fn a_failed_exact_reports_the_goal_untouched() {
        // `is_bool ; is_bool` = `drop 0 ; push true` is provable — `diagram`
        // closes it — but `exact` claims more, fails, and shows the goal
        // exactly as it stands: no normalization, no narrowing. That
        // unaltered residual is what the step is for.
        let (ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { drop 0 push true };",
            "probe",
            Some("exact"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the sides are not one term as written");
        };
        assert!(residual.stopped.contains("`exact`"), "{}", residual.stopped);
        assert_eq!(
            format!("{}", ctx.display(residual.lhs)),
            "is_bool ; is_bool"
        );
        assert_eq!(
            format!("{}", ctx.display(residual.rhs)),
            "drop(1) ; push true"
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
        let Outcome::Closed(proof) = outcome else {
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
        // A directed law leads the left — `dedup`, then the cleanup — and
        // the driver alone takes the right: the two spellings settle on the
        // one graph, a literal read twice.
        let (_ctx, outcome) = prove_with(
            "identity probe { push 1 push 1 add } = { push 1 pick 0 add };",
            "probe",
            Some("lhs(fire(dedup) saturate) rhs(saturate) exact"),
        );
        let Outcome::Closed(proof) = outcome else {
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

        // `both` spends each side in turn — the right side's rewrites
        // include the very `id` the goal's own padding built, which
        // nothing but a rewrite takes back out.
        let (_ctx, outcome) = prove_with(
            "identity probe { swap swap not } = { not };",
            "probe",
            Some("both(saturate) exact"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("two crossings and a padding wire, all spent");
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
    /// residual reads that state back.
    #[test]
    fn a_stuck_tactic_shows_the_goal_standing() {
        let (ctx, outcome) = prove_with(
            "identity probe { push 1 push 1 add } = { push 2 };",
            "probe",
            Some("lhs(fire(dedup) fire(fork-dedup)) exact"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("there is no fork to dedup");
        };
        assert!(
            residual.stopped.contains("`lhs(…)`") && residual.stopped.contains("found nothing"),
            "{}",
            residual.stopped
        );
        // The dedup landed and stands: one literal read twice, which the
        // read-back spells as the copy it is.
        let lhs = format!("{}", ctx.display(residual.lhs));
        assert!(lhs.contains("copy(1)"), "{}", lhs);
        assert_eq!(lhs.matches("push 1").count(), 1, "{}", lhs);
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
        let (_ctx, outcome) = prove_with(code, "probe", Some("lhs(fire(copy-elim)) diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("there is no copy to spend");
        };
        assert!(
            residual.stopped.contains("`lhs(…)`"),
            "{}",
            residual.stopped
        );
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
        let Outcome::Closed(proof) = outcome else {
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
        let Outcome::Closed(proof) = outcome else {
            panic!("both halves close");
        };
        assert_eq!(
            proof.summary(),
            "cut (left: the two sides are one diagram; right: inline; the two sides are one graph)"
        );
    }

    #[test]
    fn a_swapped_goal_that_sticks_says_which_way_round_it_is() {
        let (ctx, outcome) = prove_with(
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
        assert_eq!(format!("{}", ctx.display(residual.lhs)), "push 2");
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
        let (ctx, outcome) = prove_identity("identity probe { push 1 } = { push 2 };", "probe");
        let Outcome::Stuck(residual) = outcome else {
            panic!("push 1 is not push 2");
        };
        assert!(
            residual.stopped.contains("different diagrams"),
            "{}",
            residual.stopped
        );
        assert_eq!(format!("{}", ctx.display(residual.lhs)), "push 1");
        assert_eq!(format!("{}", ctx.display(residual.rhs)), "push 2");
    }

    #[test]
    fn a_stuck_goal_names_where_the_difference_lives() {
        // A false claim buried behind shared context: the residual strips
        // what the two read-backs share rather than printing two whole
        // terms. (The read-back spells a branch flat, so the narrowing
        // peels the shared spelling rather than entering an arm.)
        let (ctx, outcome) = prove_identity(
            "identity probe { drop 0 branch { drop 0 push 1 } { not } } = { drop 0 branch { drop 0 push 2 } { not } };",
            "probe",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the arms differ");
        };
        assert!(
            residual.path.iter().any(|step| step.contains("shared")),
            "{:?}",
            residual.path
        );
        assert!(
            format!("{}", ctx.display(residual.lhs)).contains("push 1"),
            "{}",
            ctx.display(residual.lhs)
        );
        assert!(
            format!("{}", ctx.display(residual.rhs)).contains("push 2"),
            "{}",
            ctx.display(residual.rhs)
        );
    }

    /// A proof answers for itself: `prove` re-checks every close against
    /// the goal as stated before answering, and `Proof::check` refuses a
    /// proof that lies — or one written for a different goal, whose
    /// recorded steps name boxes this goal never had.
    #[test]
    fn a_proof_that_lies_is_refused() {
        let false_lib = assemble("identity probe { push 1 } = { push 2 };").unwrap();
        let mut ctx = Context::new();
        let idx = false_lib.identity_by_name("probe").unwrap();
        let false_goal = Goal::of_identity(&mut ctx, &false_lib, idx).unwrap();

        // Claimed trivial, and the sides are not one graph.
        let err = crate::goal::Proof::Trivial
            .check(false_goal.clone(), &mut ctx, &false_lib)
            .unwrap_err();
        assert!(err.contains("not one graph"), "{}", err);

        // An honest proof of a different claim does not transplant: its
        // recorded drive re-applies against boxes this goal does not have.
        let true_lib = assemble("identity probe { swap swap } = { pick 0 drop 0 };").unwrap();
        let mut true_ctx = Context::new();
        let idx = true_lib.identity_by_name("probe").unwrap();
        let true_goal = Goal::of_identity(&mut true_ctx, &true_lib, idx).unwrap();
        let outcome = Prover::new(&true_lib)
            .prove(&mut true_ctx, true_goal, None)
            .unwrap();
        let Outcome::Closed(stolen) = outcome else {
            panic!("two crossings and a copied drop close");
        };
        let err = stolen.check(false_goal, &mut ctx, &false_lib).unwrap_err();
        assert!(err.contains("does not re-apply"), "{}", err);
    }

    /// A structured `cases` closes what the flat one does, with each arm's
    /// work scoped to its side of the split — and the close re-checks,
    /// which is the load-bearing assertion: the arm steps appended to the
    /// split's record replay blind through `Proof::check`.
    #[test]
    fn a_structured_case_split_scopes_its_arms() {
        let code = "identity probe \
             { pick 0 push 7 equal branch { push 7 equal } { drop 0 push false } } \
           = { pick 0 push 7 equal branch { drop 0 push true } { drop 0 push false } };";
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some("both(decide) cases(equal) (true: both(decide), false: both(decide)) diagram"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the structured split closes what the flat one does");
        };
        let summary = proof.summary();
        assert!(
            summary.contains("(true:") && summary.contains("false:"),
            "{}",
            summary
        );
    }

    /// An arm that fails names whose case it stood in, on top of the
    /// tactic's own complaint.
    #[test]
    fn a_failed_arm_names_its_case() {
        let code = "identity probe \
             { pick 0 push 7 equal branch { push 7 equal } { drop 0 push false } } \
           = { pick 0 push 7 equal branch { drop 0 push true } { drop 0 push false } };";
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some("both(decide) cases(equal) (true: both(fire(fork-dedup))) diagram"),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("a split's branch has no fork to dedup");
        };
        assert!(
            residual
                .path
                .iter()
                .any(|p| p.contains("in the true case of the split on")),
            "{:?}",
            residual.path
        );
        assert!(
            residual.stopped.contains("`both(…)`"),
            "{}",
            residual.stopped
        );
    }

    /// A goal side that never split skips the arms quietly — the same
    /// tolerance the bare step keeps for a side without the operation.
    #[test]
    fn a_side_without_the_operation_skips_the_arms_quietly() {
        let (_ctx, outcome) = prove_with(
            "identity probe { is_bool is_bool } = { drop 0 push true };",
            "probe",
            Some("cases(is_bool) (true: both(decide), false: both(decide)) diagram"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the right side has no test, and the left's split closes");
        };
        let summary = proof.summary();
        assert!(
            summary.starts_with("cases: 1 split(s) (true:"),
            "{}",
            summary
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
            .expect("the crate sits in the workspace")
            .join("tests");
        let mut corpus = crate::corpus::load(&tests).unwrap();
        let library = &corpus.library;
        let terms = &mut corpus.terms;
        let mut closed = Vec::new();
        for (idx, identity) in library.identities.iter_enumerated() {
            let mut goal = Goal::of_identity(terms, library, idx).unwrap();
            diagram2::inline(&mut goal.lhs, terms, library, None).unwrap();
            diagram2::inline(&mut goal.rhs, terms, library, None).unwrap();
            for side in [&mut goal.lhs, &mut goal.rhs] {
                let mut deriv = diagram2::rules::Derivation::default();
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
                "identities::untupling_and_retupling_is_the_coercion",
                "identities::a_coerced_tuple_survives_the_round_trip",
                "identities::a_built_tuple_is_the_width_it_was_built",
                "identities::a_built_tuple_is_no_other_width",
            ],
            "the table's reach changed"
        );
    }

    /// The loop an addressed step exists to close: a stuck goal prints a
    /// listing keyed by box id, and the id it printed is what the next
    /// step writes back. `fire` cannot say "that one"; `at` is how the
    /// proof answers the report in the report's own words.
    #[test]
    fn a_proof_can_name_the_box_the_residual_printed() {
        use crate::diagram2::render;
        use crate::graph::NodeKind;

        let code = "identity probe { pick 1 pick 1 equal drop 0 } = { };";

        // `exact` fails on purpose — the report is its whole job.
        let (_ctx, outcome) = prove_with(code, "probe", Some("exact"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("the sides are not one diagram yet");
        };
        let (dead, _) = residual
            .lhs_graph
            .live()
            .find(|(_, kind)| matches!(kind, NodeKind::Drop(_)))
            .expect("the discarded comparison");
        let listing = render::listing(&residual.lhs_graph, "left").to_string();
        assert!(
            listing.contains(&dead.to_string()),
            "the listing names the box a proof would name:\n{}",
            listing
        );

        // …and that is the address, written exactly as it was printed.
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("lhs(at({}, dead-node)) diagram", dead)),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("the named box is dead and `dead-node` collects it");
        };
        assert!(
            proof.summary().contains("lhs: 1 rewrite"),
            "{}",
            proof.summary()
        );

        // A box the side does not have is its own mistake, said as one.
        let (_ctx, outcome) = prove_with(code, "probe", Some("lhs(at(#999, dead-node)) diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("there is no #999")
        };
        assert!(
            residual.stopped.contains("#999 is not a live box"),
            "{}",
            residual.stopped
        );

        // So is a box that is there with nothing of that law to fire.
        let (_ctx, outcome) = prove_with(
            code,
            "probe",
            Some(&format!("lhs(at({}, equal-refl)) diagram", dead)),
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("a `drop` is no `equal`")
        };
        assert!(
            residual
                .stopped
                .contains(&format!("no forward `equal-refl` match holds {}", dead)),
            "{}",
            residual.stopped
        );
    }
}
