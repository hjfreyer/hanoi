//! A goal is two graphs and the claim that they are the same program.
//!
//! The sides used to be terms; they are [`crate::diagram2`] graphs now, so
//! that a proof can *rewrite* them — the tactic language acts on a side in
//! place, and equality-as-stated is [isomorphism](crate::graph::isomorphic)
//! rather than one term twice. The terms are still where a goal comes from:
//! an identity lowers, aligns, and **builds**.
//!
//! The compiler holds an identity to equal **net** change rather than equal
//! arity — `pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`, and every
//! counit reads that way. That asymmetry still lives in exactly one place:
//! here, where the narrower side is padded with
//! [`under`](crate::term::Context::under) until the two arities agree,
//! before either side becomes a graph. Everything downstream is then
//! arity-exact, which is what lets two graphs share one boundary.

use bytecode::{IdentityIndex, Library, SentenceIndex};

use crate::diagram2;
use crate::diagram2::rules::{Step, replay};
use crate::graph::{self, Direction, Graph, Match, Pair};
use crate::term::{Context, Error, TermIndex, lower};

/// Two graphs of one arity, claimed to be the same program.
#[derive(Debug, Clone, PartialEq)]
pub struct Goal {
    pub lhs: Graph,
    pub rhs: Graph,
}

impl Goal {
    /// The goal an `identity` declaration states.
    ///
    /// Lowers both sides and pads the narrower; the compiler already refused
    /// any identity whose sides differ in net change, so padding always
    /// brings the arities together.
    pub fn of_identity(
        ctx: &mut Context,
        library: &Library,
        idx: IdentityIndex,
    ) -> Result<Goal, Error> {
        let identity = &library.identities[idx];
        let lhs = lower(ctx, library, identity.lhs)?;
        let rhs = lower(ctx, library, identity.rhs)?;
        Ok(Goal::aligned(ctx, lhs, rhs))
    }

    /// Two terms padded to one arity, then built as graphs.
    pub fn aligned(ctx: &mut Context, lhs: TermIndex, rhs: TermIndex) -> Goal {
        let (la, ra) = (ctx.arity(lhs), ctx.arity(rhs));
        let (lhs, rhs) = if la.inputs < ra.inputs {
            (ctx.under(lhs, ra.inputs - la.inputs), rhs)
        } else {
            (lhs, ctx.under(rhs, la.inputs - ra.inputs))
        };
        debug_assert_eq!(
            ctx.arity(lhs),
            ctx.arity(rhs),
            "an identity's sides differ by more than padding, which check_identities refuses"
        );
        Goal {
            lhs: diagram2::build(ctx, lhs),
            rhs: diagram2::build(ctx, rhs),
        }
    }
}

/// Which side of the *goal* a claim's left side currently is.
///
/// A goal's sides swap under `symm` and the claim's do not, so a traversal
/// looking for the run that drives the left onto the right has to carry
/// which is which. Nothing but [`Proof::Swapped`] moves it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Left,
    Right,
}

impl Side {
    /// The run being driven, and the one that must be empty for it to be a
    /// run at all.
    fn of<'p>(self, lhs: &'p [Step], rhs: &'p [Step]) -> (&'p [Step], &'p [Step]) {
        match self {
            Side::Left => (lhs, rhs),
            Side::Right => (rhs, lhs),
        }
    }

    fn flipped(self) -> Side {
        match self {
            Side::Left => Side::Right,
            Side::Right => Side::Left,
        }
    }
}

/// Why a proof that drives both sides cannot be carried anywhere.
fn met_in_the_middle(steps: usize) -> String {
    format!(
        "it spends {} step(s) on the side it is not driving, so it takes the two together \
         rather than one onto the other",
        steps
    )
}

/// How a goal was discharged — and **everything needed to check that it
/// was**. A proof is not the prover's word for it: each rewriting variant
/// carries the very [`Step`]s that landed, each definitional variant
/// carries what re-performs it, and [`Proof::check`] walks the tree
/// against the goal as stated, holding every step to
/// [`rules::apply`](crate::diagram2::rules::apply) again and every leaf to
/// [`isomorphic`](graph::isomorphic) again. Finding and checking are
/// different jobs; this is the artifact that keeps them apart.
///
/// [`summary`][Proof::summary] prints it one-line for the per-identity
/// report.
#[derive(Debug)]
pub enum Proof {
    /// The two sides are one graph — isomorphic as they stand.
    Trivial,
    /// A `lhs(…)`, `rhs(…)` or `both(…)` ran a graph tactic; the rewritten
    /// goal closed. The steps each side spent are the record.
    Rewrote {
        side: &'static str,
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        sub: Box<Proof>,
    },
    /// An `inline` opened calls — every one, or the one sentence `target`
    /// names — and the opened goal closed. Deterministic given the target,
    /// so the checker re-performs it rather than trusting a transcript.
    Inlined {
        target: Option<SentenceIndex>,
        name: Option<String>,
        sub: Box<Proof>,
    },
    /// A `by` **cited** another identity where its left side occurred, and
    /// the goal that citation left closed.
    ///
    /// The one node whose claim this proof does not discharge. It records a
    /// name and, per side, the [`Match`] saying where the cited claim's left
    /// side sat — enough for [`check`](Proof::check) to rebuild that claim's
    /// two graphs from the library, hold the match to
    /// [`check_match`](crate::graph::check_match), and put the right side
    /// down. What it does **not** do is ask whether the cited claim is true.
    /// That is the corpus's job, and the corpus does it: every identity is
    /// proved, the citation order is a DAG, and a claim that did not close
    /// is never citable in the first place.
    ///
    /// So a `Proof` holding one of these stands **given the corpus** rather
    /// than on its own, and [`cites`](Proof::cites) is how a caller reads
    /// off exactly what that means for this one. The alternative — carrying
    /// the cited proof's steps at every use site and re-checking them there
    /// — is [`one_sided`](Proof::one_sided) and
    /// [`transplant`](crate::diagram2::rules::transplant), which is what
    /// discharges a citation when something asks.
    ///
    /// The pair is rebuilt from the name rather than recorded beside it, on
    /// purpose: a claim's sides are the library's to say, and a proof that
    /// carried its own copy could carry a copy of something else. The
    /// checker holds the library already — [`Proof::Inlined`] needs it too —
    /// so there is nothing to gain by writing them down twice.
    Cited {
        of: IdentityIndex,
        /// The name as written, for the report; the index is what is read.
        name: String,
        /// Where the cited claim's left side sat on the goal's left, if it
        /// was spent there.
        lhs: Option<Match>,
        /// The same on the right.
        rhs: Option<Match>,
        sub: Box<Proof>,
    },
    /// A `symm` swapped the sides, and the swapped goal closed. It records
    /// nothing but itself: the claim either way is the same one.
    Swapped(Box<Proof>),
    /// A `via` cut the goal at the waypoint; each half closed
    /// independently, and the checker rebuilds both halves from the
    /// waypoint the same way the prover did.
    Cut {
        waypoint: TermIndex,
        left_sub: Box<Proof>,
        right_sub: Box<Proof>,
    },
    /// A `cases` expanded a boolean-valued wire — η, spent as the table's
    /// own Shannon law — on each side that held one, and the expanded goal
    /// closed. The per-side records hold the split(s) and, when the step
    /// carried per-case sub-strategies, every step those landed inside the
    /// arms, in order — all ordinary rewrites, replayed blind by the
    /// checker. `splits` and `arms` are presentation only: how many
    /// expansions fired, and how many rewrites each case's sub-strategy
    /// spent (both sides summed), when arms were written.
    Cases {
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        splits: usize,
        arms: Option<(usize, usize)>,
        sub: Box<Proof>,
    },
    /// A `diagram` drove both sides to fixpoint and they were one diagram.
    /// The two drives are the record, and the isomorphism is asked again.
    Diagram { lhs: Vec<Step>, rhs: Vec<Step> },
}

impl Proof {
    /// Re-checks the whole proof against the goal it claims to close.
    ///
    /// Nothing here trusts the prover: recorded steps re-apply through
    /// [`replay`] — every match re-verified port by port — definitional
    /// moves (`inline`, the cut's alignment, the swap) are re-performed
    /// from what the proof names, and every branch of the tree ends in an
    /// [`isomorphic`](graph::isomorphic) that is asked fresh. `Ok(())`
    /// means the claim closes by exactly what the proof says; an `Err`
    /// says where it does not, and a prover that produced one has a bug.
    pub fn check(&self, goal: Goal, ctx: &mut Context, library: &Library) -> Result<(), String> {
        let mut goal = goal;
        match self {
            Proof::Trivial => {
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    Ok(())
                } else {
                    Err("claimed trivial, and the sides are not one graph".to_string())
                }
            }
            Proof::Rewrote { lhs, rhs, sub, .. } | Proof::Cases { lhs, rhs, sub, .. } => {
                replay(&mut goal.lhs, lhs)
                    .map_err(|e| format!("a recorded left step does not re-apply: {}", e))?;
                replay(&mut goal.rhs, rhs)
                    .map_err(|e| format!("a recorded right step does not re-apply: {}", e))?;
                sub.check(goal, ctx, library)
            }
            Proof::Diagram { lhs, rhs } => {
                replay(&mut goal.lhs, lhs)
                    .map_err(|e| format!("a recorded left step does not re-apply: {}", e))?;
                replay(&mut goal.rhs, rhs)
                    .map_err(|e| format!("a recorded right step does not re-apply: {}", e))?;
                if graph::isomorphic(&goal.lhs, &goal.rhs) {
                    Ok(())
                } else {
                    Err("the recorded drives do not land on one diagram".to_string())
                }
            }
            Proof::Inlined { target, sub, .. } => {
                diagram2::inline(&mut goal.lhs, ctx, library, *target)
                    .map_err(|e| format!("the recorded inline does not re-open: {}", e))?;
                diagram2::inline(&mut goal.rhs, ctx, library, *target)
                    .map_err(|e| format!("the recorded inline does not re-open: {}", e))?;
                sub.check(goal, ctx, library)
            }
            Proof::Cited {
                of,
                name,
                lhs,
                rhs,
                sub,
            } => {
                // Rebuilt, not read off the proof: what a name means is the
                // library's to say.
                let cited = Goal::of_identity(ctx, library, *of)
                    .map_err(|e| format!("the cited identity {} does not build: {}", name, e))?;
                let pair = Pair::new(cited.lhs, cited.rhs)
                    .map_err(|e| format!("the cited identity {} is no pair: {}", name, e))?;
                for (at, side) in [(lhs, true), (rhs, false)] {
                    let Some(at) = at else { continue };
                    let host = if side { &mut goal.lhs } else { &mut goal.rhs };
                    pair.apply(host, Direction::Forward, at).map_err(|e| {
                        format!(
                            "the recorded citation of {} does not apply to the {}: {}",
                            name,
                            if side { "left" } else { "right" },
                            e
                        )
                    })?;
                }
                sub.check(goal, ctx, library)
            }
            Proof::Swapped(sub) => {
                let swapped = Goal {
                    lhs: goal.rhs,
                    rhs: goal.lhs,
                };
                sub.check(swapped, ctx, library)
            }
            Proof::Cut {
                waypoint,
                left_sub,
                right_sub,
            } => {
                let (lhs, stone) = against(ctx, &goal.lhs, *waypoint);
                left_sub
                    .check(Goal { lhs, rhs: stone }, ctx, library)
                    .map_err(|e| format!("in the left half of the cut: {}", e))?;
                let (rhs, stone) = against(ctx, &goal.rhs, *waypoint);
                right_sub
                    .check(Goal { lhs: stone, rhs }, ctx, library)
                    .map_err(|e| format!("in the right half of the cut: {}", e))
            }
        }
    }

    /// The run this proof spends driving the claim's left side onto its
    /// right, or why it is not one.
    ///
    /// What [`transplant`](crate::diagram2::rules::transplant) needs to
    /// carry a proved identity into another goal: a flat list of ordinary
    /// rewrites taking one side of the claim to the other. A proof that
    /// closes by driving the left onto the right is already that list, with
    /// the tree flattened away.
    ///
    /// A `symm` costs nothing here. It swaps which side of the *goal* the
    /// steps after it act on, and the claim is untouched — so what a run
    /// looks for swaps with it, and `symm rhs(…) rhs(…)` is the same run
    /// spelled from the other end.
    ///
    /// Two shapes still refuse, and both refuse for want of one thing —
    /// a **join**, the isomorphism between what one run landed on and where
    /// the next was written to start:
    ///
    /// - **A step on the other side.** The runs are `A ⟶ M` and `B ⟶ M'`
    ///   meeting in the middle, so `A ⟶ B` is the first, then the second
    ///   backwards, rebased through `M ≅ M'`.
    /// - **`via`.** The halves really do compose — `A ⟶ C` then `C ⟶ B` —
    ///   but the waypoint is *rebuilt* for each half, so what the left run
    ///   lands on is only isomorphic to the graph the right run names. Same
    ///   join, no inversion.
    ///
    /// And one refuses for a different reason:
    ///
    /// - **`inline`.** An open *is* a rewrite — one call's window against
    ///   its body's graph, which is exactly how
    ///   [`inline`](crate::diagram2::inline) performs it. What it is not is
    ///   a recorded [`Step`]: [`sides`](crate::diagram2::rules::sides) has
    ///   no library to build a body from, so nothing in the table can state
    ///   an open, and [`Proof::Inlined`] therefore records the *sentence*
    ///   and re-performs the open rather than carrying a transcript. So
    ///   what there is to carry is a whole-graph operation rather than a
    ///   window's worth of steps, and the honest fix today is to state the
    ///   opened form as its own identity.
    pub fn one_sided(&self) -> Result<Vec<Step>, String> {
        self.run_on(Side::Left)
    }

    /// [`one_sided`](Proof::one_sided), tracking which side of the *goal*
    /// the claim's left has become. Every `symm` flips it, and nothing else
    /// touches it.
    fn run_on(&self, side: Side) -> Result<Vec<Step>, String> {
        match self {
            Proof::Trivial => Ok(Vec::new()),
            Proof::Rewrote { lhs, rhs, sub, .. } | Proof::Cases { lhs, rhs, sub, .. } => {
                let (driven, other) = side.of(lhs, rhs);
                if !other.is_empty() {
                    return Err(met_in_the_middle(other.len()));
                }
                let mut run = driven.to_vec();
                run.extend(sub.run_on(side)?);
                Ok(run)
            }
            Proof::Diagram { lhs, rhs } => {
                let (driven, other) = side.of(lhs, rhs);
                if !other.is_empty() {
                    return Err(met_in_the_middle(other.len()));
                }
                Ok(driven.to_vec())
            }
            // The claim is the same claim either way round; what moved is
            // which side of the goal it is written on.
            Proof::Swapped(sub) => sub.run_on(side.flipped()),
            Proof::Cited { name, .. } => Err(format!(
                "it cites {}, and a citation is one rewrite by that claim rather than the \
                 steps behind it: expand it first, or carry it as the citation it is",
                name
            )),
            Proof::Inlined { .. } => Err(
                "it opens calls across the whole graph rather than inside a window, and \
                 records the sentence rather than the steps, so there is nothing localized \
                 to carry: state the opened form as its own identity and prove that"
                    .to_string(),
            ),
            Proof::Cut { .. } => Err(
                "it cuts at a waypoint, and the waypoint is rebuilt for each half, so the two \
                 halves do not meet on the nose"
                    .to_string(),
            ),
        }
    }

    /// Every identity this proof **leans on** rather than discharges.
    ///
    /// A [`Cited`](Proof::Cited) node is checked against the claim it names
    /// without asking whether that claim holds, so a proof holding one is
    /// conditional. This is the condition, read off the tree — what a corpus
    /// needs in order to say that a run of proofs adds up to more than each
    /// of them separately.
    pub fn cites(&self, out: &mut Vec<IdentityIndex>) {
        match self {
            Proof::Trivial | Proof::Diagram { .. } => {}
            Proof::Cited { of, sub, .. } => {
                if !out.contains(of) {
                    out.push(*of);
                }
                sub.cites(out);
            }
            Proof::Rewrote { sub, .. } | Proof::Cases { sub, .. } | Proof::Inlined { sub, .. } => {
                sub.cites(out)
            }
            Proof::Swapped(sub) => sub.cites(out),
            Proof::Cut {
                left_sub,
                right_sub,
                ..
            } => {
                left_sub.cites(out);
                right_sub.cites(out);
            }
        }
    }

    /// One line saying how the goal closed, for the per-identity report.
    pub fn summary(&self) -> String {
        match self {
            Proof::Trivial => "the two sides are one graph".to_string(),
            Proof::Rewrote {
                side,
                lhs,
                rhs,
                sub,
            } => format!(
                "{}: {} rewrite(s); {}",
                side,
                lhs.len() + rhs.len(),
                sub.summary()
            ),
            Proof::Inlined { name, sub, .. } => match name {
                None => format!("inline; {}", sub.summary()),
                Some(name) => format!("inline {}; {}", name, sub.summary()),
            },
            Proof::Cited { name, sub, .. } => format!("by {}; {}", name, sub.summary()),
            Proof::Swapped(sub) => format!("symm; {}", sub.summary()),
            Proof::Cut {
                left_sub,
                right_sub,
                ..
            } => format!(
                "cut (left: {}; right: {})",
                left_sub.summary(),
                right_sub.summary()
            ),
            Proof::Cases {
                splits, arms, sub, ..
            } => match arms {
                None => format!("cases: {} split(s); {}", splits, sub.summary()),
                Some((t, e)) => format!(
                    "cases: {} split(s) (true: {} rewrite(s); false: {} rewrite(s)); {}",
                    splits,
                    t,
                    e,
                    sub.summary()
                ),
            },
            Proof::Diagram { .. } => "the two sides are one diagram".to_string(),
        }
    }
}

/// A goal's side and a waypoint, brought to one arity: the narrower is
/// padded — the term with [`Context::under`] before it builds, the graph
/// with [`graph::under`] — and the waypoint comes back as a graph. Both
/// the prover's `via` and the checker's re-walk of a [`Proof::Cut`] build
/// their halves here, so the two cannot disagree about what a cut means.
pub(crate) fn against(ctx: &mut Context, side: &Graph, waypoint: TermIndex) -> (Graph, Graph) {
    let (ga, wa) = (side.arity(), ctx.arity(waypoint));
    if wa.inputs < ga.inputs {
        let padded = ctx.under(waypoint, ga.inputs - wa.inputs);
        (side.clone(), diagram2::build(ctx, padded))
    } else {
        (
            graph::under(side, wa.inputs - ga.inputs),
            diagram2::build(ctx, waypoint),
        )
    }
}

/// What is left when a goal did not close: what each side became, twice
/// over — as the graphs the tactics left, and as terms narrowed to where
/// the two differ.
///
/// Both, because the two answer different questions. The graphs are what
/// there is to *read*: they are what a step acted on, they carry the boxes
/// a next step would name, and a box's id is stable across a step so two
/// reports of one proof can be compared. The terms are what there is to
/// *write*: a `via` waypoint is a term, so the report hands back one in the
/// language the answer is written in.
///
/// This output is the deliverable of a failed run — it is what says what to
/// try next, so it is kept as data rather than printed on the spot.
#[derive(Debug)]
pub struct Residual {
    /// The two sides as they stand, which is what the report *shows*: a
    /// graph is what the tactics act on, and a box in one has a name that
    /// survives a step, so two of these compare. See
    /// [`render`](crate::diagram2::render).
    pub lhs_graph: Graph,
    pub rhs_graph: Graph,
    /// The same two sides read back as terms, narrowed to the difference.
    /// This is what a stuck goal is *answered* with: a `via` waypoint is
    /// written in the term language, so the report prints one to copy and
    /// edit rather than to translate.
    pub lhs: TermIndex,
    pub rhs: TermIndex,
    /// How the report walked from the goal to the difference: each step of
    /// stripping shared context or entering the one arm that differs.
    pub path: Vec<String>,
    /// Why the step gave up.
    pub stopped: String,
}

/// The answer for one goal.
#[derive(Debug)]
pub enum Outcome {
    Closed(Proof),
    Stuck(Residual),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What a lemma has to be for [`Proof::one_sided`] to answer, and what
    /// each refusal says.
    #[test]
    fn only_a_run_from_one_side_to_the_other_can_be_carried() {
        // Nothing to do at all is a run of no steps.
        assert_eq!(Proof::Trivial.one_sided(), Ok(Vec::new()));

        // The other side untouched is the shape a lemma is written in, and
        // the tree flattens to the steps the driven side spent, in order.
        let left_only = Proof::Rewrote {
            side: "lhs",
            lhs: vec![countable()],
            rhs: Vec::new(),
            sub: Box::new(Proof::Diagram {
                lhs: vec![countable()],
                rhs: Vec::new(),
            }),
        };
        assert_eq!(left_only.one_sided().map(|run| run.len()), Ok(2));

        // A drive that met in the middle is two runs, not one.
        let met = Proof::Diagram {
            lhs: Vec::new(),
            rhs: vec![countable()],
        };
        let why = met.one_sided().unwrap_err();
        assert!(
            why.contains("1 step(s) on the side it is not driving"),
            "{}",
            why
        );

        // Neither an `inline` nor a `via` leaves steps that compose.
        let opened = Proof::Inlined {
            target: None,
            name: None,
            sub: Box::new(Proof::Trivial),
        };
        assert!(
            opened
                .one_sided()
                .unwrap_err()
                .contains("nothing localized to carry")
        );
    }

    /// A citation is the one thing a proof leans on rather than discharges,
    /// so it is the one thing a caller has to be able to read off the tree.
    #[test]
    fn what_a_proof_leans_on_is_readable_from_it() {
        let cite = |of: usize, sub| Proof::Cited {
            of: IdentityIndex::from(of),
            name: format!("#{}", of),
            lhs: None,
            rhs: None,
            sub: Box::new(sub),
        };
        let mut leans_on = Vec::new();
        Proof::Trivial.cites(&mut leans_on);
        assert!(
            leans_on.is_empty(),
            "a proof that cites nothing leans on nothing"
        );

        // Nested, through the shapes that carry sub-proofs, and each named
        // once however often it is spent.
        let proof = Proof::Swapped(Box::new(Proof::Cut {
            waypoint: crate::term::TermIndex::from(0),
            left_sub: Box::new(cite(1, cite(2, Proof::Trivial))),
            right_sub: Box::new(cite(1, Proof::Trivial)),
        }));
        let mut leans_on = Vec::new();
        proof.cites(&mut leans_on);
        assert_eq!(
            leans_on,
            vec![IdentityIndex::from(1), IdentityIndex::from(2)]
        );

        // And a citation is not a run: spending one is a rewrite by the
        // claim, not the argument behind it.
        assert!(
            cite(1, Proof::Trivial)
                .one_sided()
                .unwrap_err()
                .contains("citation is one rewrite by that claim")
        );
    }

    /// A `symm` moves which side of the goal the claim's left side is, and
    /// costs the run nothing: the same proof written from the other end is
    /// the same run.
    #[test]
    fn a_swap_is_free() {
        let forwards = Proof::Rewrote {
            side: "lhs",
            lhs: vec![countable()],
            rhs: Vec::new(),
            sub: Box::new(Proof::Trivial),
        };
        let backwards = Proof::Swapped(Box::new(Proof::Rewrote {
            side: "rhs",
            lhs: Vec::new(),
            rhs: vec![countable()],
            sub: Box::new(Proof::Trivial),
        }));
        assert_eq!(forwards.one_sided(), backwards.one_sided());
        assert_eq!(backwards.one_sided().map(|run| run.len()), Ok(1));

        // And it is the *swap* that moves, not the reading: under one
        // `symm`, steps on the goal's left are steps on the claim's right.
        let wrong_end = Proof::Swapped(Box::new(Proof::Rewrote {
            side: "lhs",
            lhs: vec![countable()],
            rhs: Vec::new(),
            sub: Box::new(Proof::Trivial),
        }));
        assert!(
            wrong_end
                .one_sided()
                .unwrap_err()
                .contains("side it is not driving")
        );

        // Two swaps are the identity on the reading, as they are on the goal.
        let twice = Proof::Swapped(Box::new(Proof::Swapped(Box::new(Proof::Rewrote {
            side: "lhs",
            lhs: vec![countable()],
            rhs: Vec::new(),
            sub: Box::new(Proof::Trivial),
        }))));
        assert_eq!(twice.one_sided().map(|run| run.len()), Ok(1));
    }

    /// A step whose only job is to be counted — `one_sided` moves steps
    /// around and never reads inside one.
    fn countable() -> Step {
        use crate::diagram2::rules::Rule;
        use crate::graph::{Direction, Match};
        Step {
            rule: Rule::SwapElim,
            dir: Direction::Forward,
            at: Match {
                nodes: Vec::new(),
                inputs: Vec::new(),
                outputs: Vec::new(),
                branches: Vec::new(),
            },
        }
    }
}
