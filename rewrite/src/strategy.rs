//! The interpreter for the strategy language of [`crate::hant`].
//!
//! A proof mirrors a tree of goals. A strategy acts on one goal:
//! manipulations transform it, a splitter (`via`, `descend`) replaces it
//! with independent subgoals each carrying its own strategy, and `diagram`
//! closes it. The default — what an identity with no written proof gets —
//! is `diagram` alone.
//!
//! The closer is the [`crate::diagram`] engine: both sides normalize into
//! one arena and either they are one diagram or they are not. It is a
//! decision procedure, not a search — there is no budget to run out of —
//! so a stuck `diagram` means the claim is false, or true only for reasons
//! the canonical form cannot see (η, and whatever of the branch layer no
//! ordering reaches). Every other step exists to *direct* it: `inline`
//! spends the library's defining equations, since the engine never opens a
//! call on its own; `via` cuts at a waypoint so a report can say which
//! half of a journey failed; `peel`, `descend` and `symm` narrow and turn
//! the goal; `exact` claims the sides are one term as written, and its
//! failure prints the goal untouched — the way to *see* one.
//!
//! A stuck goal's residual is **narrowed** for the report — the two sides
//! reified back into terms, shared affixes stripped, the differing arm
//! entered — because when the engine says no, where the difference lives
//! is the thing worth printing.

use bytecode::{Library, SentenceIndex};

use crate::diagram::{Ctx, normalize, reify};
use crate::goal::{Goal, Outcome, Proof, Residual};
use crate::hant::{Body, Step, Strategy, default_strategy};
use crate::term::{Context, Error, Term, TermIndex, lower};

/// Proves goals against one library.
///
/// Every step reads the goal's terms out of a [`Context`] and writes the
/// terms it makes back into it, so the one arena is threaded through: a
/// waypoint read at load time, the goal, and every subgoal a strategy carves
/// out of it are all places in it.
pub struct Prover<'l> {
    pub library: &'l Library,
}

impl<'l> Prover<'l> {
    pub fn new(library: &'l Library) -> Self {
        Prover { library }
    }

    /// Runs a strategy on a goal — the written one, or the default
    /// `diagram` when the identity carries no proof.
    pub fn prove(
        &self,
        ctx: &mut Context,
        goal: Goal,
        strategy: Option<&Strategy<Body>>,
    ) -> Result<Outcome, Error> {
        let default = default_strategy();
        let strategy = strategy.unwrap_or(&default);
        self.run(ctx, strategy, goal)
    }

    /// One strategy on one goal. A goal whose sides are one term as written
    /// is closed before any step runs — at every level, so a `descend` arm
    /// or a cut's side that became trivial needs no steps of its own.
    fn run(
        &self,
        ctx: &mut Context,
        strategy: &[Step<Body>],
        goal: Goal,
    ) -> Result<Outcome, Error> {
        if ctx.equal(goal.lhs, goal.rhs) {
            return Ok(Outcome::Closed(Proof::Trivial));
        }
        let Some((head, rest)) = strategy.split_first() else {
            return Ok(Outcome::Stuck(gave_up(
                goal,
                "the strategy ended with the goal still open",
            )));
        };
        match head {
            // Both sides into one arena; either they are one diagram or the
            // claim is beyond the canonical form. The residual reifies what
            // each side became, narrowed to where they differ.
            Step::Diagram => {
                let mut diagrams = Ctx::default();
                let lhs = normalize(&mut diagrams, ctx, goal.lhs);
                let rhs = normalize(&mut diagrams, ctx, goal.rhs);
                if lhs == rhs {
                    return Ok(Outcome::Closed(Proof::Diagram));
                }
                let inputs = ctx.arity(goal.lhs).inputs;
                let (lhs, rhs) = (
                    reify(&diagrams, ctx, lhs, inputs),
                    reify(&diagrams, ctx, rhs, inputs),
                );
                let (mut path, lhs, rhs) = narrow(ctx, lhs, rhs);
                path.insert(0, "as diagrams".to_string());
                Ok(Outcome::Stuck(Residual {
                    lhs,
                    rhs,
                    path,
                    stopped: "the two sides normalize to different diagrams: the claim is \
                              false, or true only for reasons the canonical form cannot see"
                        .to_string(),
                }))
            }

            // A goal whose sides are one term closed above, before any step
            // ran — so an `exact` that is reached is an `exact` whose claim
            // is false, and its whole job is the report: the goal untouched,
            // no normalization to reshape it and no narrowing to walk into
            // it. That unaltered residual is what the step is usually
            // written for — `exact` alone shows the identity as lowered and
            // aligned, and after a manipulation it shows what the
            // manipulation left, in the language a waypoint is written in.
            Step::Exact => Ok(Outcome::Stuck(gave_up(
                goal,
                "`exact` claims the sides are one term as written, and they are not",
            ))),

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
                if ctx.arity(waypoint).net() != ctx.arity(goal.lhs).net() {
                    let why = format!(
                        "the `via` waypoint's net stack change ({}) is not the goal's ({})",
                        ctx.arity(waypoint).net(),
                        ctx.arity(goal.lhs).net()
                    );
                    return Ok(Outcome::Stuck(gave_up(goal, &why)));
                }
                // Two goals, fully independent from here: each side takes its
                // own road, and proving both proves the whole by transitivity.
                let sub = Goal::aligned(ctx, goal.lhs, waypoint);
                let left_sub = match self.side(ctx, "left", left, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                let sub = Goal::aligned(ctx, waypoint, goal.rhs);
                let right_sub = match self.side(ctx, "right", right, sub)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                Ok(Outcome::Closed(Proof::Cut {
                    left_sub,
                    right_sub,
                }))
            }

            Step::Peel => {
                let Some((narrowed, prefix, suffix)) = peel(ctx, goal) else {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "`peel` found nothing shared to strip",
                    )));
                };
                Ok(match self.run(ctx, rest, narrowed)? {
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
                if !has_calls(ctx, goal.lhs, only) && !has_calls(ctx, goal.rhs, only) {
                    let why = match only {
                        None => "`inline` found no calls to open".to_string(),
                        Some(idx) => format!(
                            "`inline({})` found no call to it here",
                            self.library.names[idx]
                        ),
                    };
                    return Ok(Outcome::Stuck(gave_up(goal, &why)));
                }
                let lhs = inline_calls(ctx, self.library, goal.lhs, only)?;
                let rhs = inline_calls(ctx, self.library, goal.rhs, only)?;
                let opened = Goal::aligned(ctx, lhs, rhs);
                let target = only.map(|idx| self.library.names[idx].clone());
                Ok(match self.run(ctx, rest, opened)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined {
                        target,
                        sub: Box::new(sub),
                    }),
                    stuck => stuck,
                })
            }

            Step::Descend { then_arm, else_arm } => {
                let (
                    &Term::Branch {
                        if_true: t1,
                        if_false: e1,
                    },
                    &Term::Branch {
                        if_true: t2,
                        if_false: e2,
                    },
                ) = (ctx.get(goal.lhs), ctx.get(goal.rhs))
                else {
                    return Ok(Outcome::Stuck(gave_up(
                        goal,
                        "`descend` needs a branch on both sides",
                    )));
                };
                let then_sub = match self.arm(ctx, "then", then_arm, t1, t2)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                let else_sub = match self.arm(ctx, "else", else_arm, e1, e2)? {
                    Ok(p) => p,
                    Err(residual) => return Ok(Outcome::Stuck(residual)),
                };
                Ok(Outcome::Closed(Proof::Descend { then_sub, else_sub }))
            }
        }
    }

    /// One half of a cut, under its own strategy or the default.
    fn side(
        &self,
        ctx: &mut Context,
        name: &str,
        strategy: &Option<Strategy<Body>>,
        sub: Goal,
    ) -> Result<Result<Box<Proof>, Residual>, Error> {
        let default = default_strategy();
        let strategy = strategy.as_ref().unwrap_or(&default);
        Ok(match self.run(ctx, strategy, sub)? {
            Outcome::Closed(p) => Ok(Box::new(p)),
            Outcome::Stuck(mut residual) => {
                residual
                    .path
                    .insert(0, format!("in the {} half of the cut", name));
                Err(residual)
            }
        })
    }

    /// One arm of a `descend`: proved by the strategy written for it, or —
    /// with none written — claimed already equal, and the claim is checked
    /// rather than assumed.
    fn arm(
        &self,
        ctx: &mut Context,
        name: &str,
        strategy: &Option<Strategy<Body>>,
        a: TermIndex,
        b: TermIndex,
    ) -> Result<Result<Option<Box<Proof>>, Residual>, Error> {
        let sub = Goal::aligned(ctx, a, b);
        match strategy {
            Some(s) => Ok(match self.run(ctx, s, sub)? {
                Outcome::Closed(p) => Ok(Some(Box::new(p))),
                Outcome::Stuck(mut residual) => {
                    residual.path.insert(0, format!("in the {} arm", name));
                    Err(residual)
                }
            }),
            None if ctx.equal(a, b) => Ok(Ok(None)),
            None => Ok(Err(Residual {
                path: vec![format!("in the {} arm", name)],
                stopped: format!(
                    "the {} arms are not already equal, and `descend` was given no strategy for them",
                    name
                ),
                ..gave_up(sub, "")
            })),
        }
    }
}

/// A residual for a strategy that failed before any engine ran: the goal as
/// it stood, and why the step gave up.
fn gave_up(goal: Goal, why: &str) -> Residual {
    Residual {
        lhs: goal.lhs,
        rhs: goal.rhs,
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
        if let Some((narrowed, prefix, suffix)) = peel(ctx, Goal { lhs, rhs }) {
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
/// narrowed goal and how much went, or `None` when nothing does.
fn peel(ctx: &mut Context, goal: Goal) -> Option<(Goal, usize, usize)> {
    let lhs = spine(ctx, goal.lhs);
    let rhs = spine(ctx, goal.rhs);

    let prefix = lhs
        .iter()
        .zip(&rhs)
        .take_while(|(a, b)| ctx.equal(**a, **b))
        .count();
    // Never peel a whole side away twice over: if the spines are equal the
    // goal was trivial, and the caller handled it.
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
        ctx.arity(goal.lhs).inputs
    };
    let narrowed = Goal {
        lhs: rebuild(ctx, &lhs[prefix..lhs.len() - suffix], boundary),
        rhs: rebuild(ctx, &rhs[prefix..rhs.len() - suffix], boundary),
    };
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

// ---- inlining ---------------------------------------------------------------

/// Whether there is anything for an `inline` to open: any call at all, or a
/// call to the one sentence a label named.
fn has_calls(ctx: &Context, term: TermIndex, only: Option<SentenceIndex>) -> bool {
    match ctx.get(term) {
        Term::Call { target, .. } => only.is_none_or(|idx| *target == idx),
        &Term::Compose(a, b) | &Term::Par(a, b) => {
            has_calls(ctx, a, only) || has_calls(ctx, b, only)
        }
        &Term::Branch { if_true, if_false } => {
            has_calls(ctx, if_true, only) || has_calls(ctx, if_false, only)
        }
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
    ctx: &mut Context,
    library: &Library,
    term: TermIndex,
    only: Option<SentenceIndex>,
) -> Result<TermIndex, Error> {
    // Copied out of the arena first: the walk writes new nodes into it, and a
    // node is small — the copy is a discriminant and two indices.
    Ok(match ctx.get(term).clone() {
        Term::Call { target, .. } => match only {
            None => {
                let body = lower(ctx, library, target)?;
                inline_calls(ctx, library, body, only)?
            }
            Some(idx) if target == idx => lower(ctx, library, target)?,
            Some(_) => term,
        },
        Term::Compose(a, b) => {
            let (a, b) = (
                inline_calls(ctx, library, a, only)?,
                inline_calls(ctx, library, b, only)?,
            );
            ctx.push(Term::Compose(a, b))
        }
        Term::Par(a, b) => {
            let (a, b) = (
                inline_calls(ctx, library, a, only)?,
                inline_calls(ctx, library, b, only)?,
            );
            ctx.push(Term::Par(a, b))
        }
        Term::Branch { if_true, if_false } => {
            let (if_true, if_false) = (
                inline_calls(ctx, library, if_true, only)?,
                inline_calls(ctx, library, if_false, only)?,
            );
            ctx.push(Term::Branch { if_true, if_false })
        }
        // A leaf is already open, and stays where it is.
        _ => term,
    })
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
            panic!("the opened goal is one term");
        };
        assert_eq!(proof.summary(), "inline; the two sides are one term");
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

    #[test]
    fn a_directed_peel_and_descend_close_and_say_so() {
        let (_ctx, outcome) = prove_with(
            "identity probe { drop 0 branch { is_bool is_bool } { not } } = { drop 0 branch { is_int is_bool } { not } };",
            "probe",
            Some("peel descend(then: diagram)"),
        );
        let Outcome::Closed(proof) = outcome else {
            panic!("expected the goal to close");
        };
        assert_eq!(
            proof.summary(),
            "peel 1+0; descend (then: the two sides are one diagram; else: as written)"
        );
    }

    #[test]
    fn an_omitted_descend_arm_is_checked_not_assumed() {
        let (_ctx, outcome) = prove_with(
            "identity probe { branch { is_bool is_bool } { not } } = { branch { is_int is_bool } { not } };",
            "probe",
            Some("descend(else: diagram)"),
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
        let (_ctx, outcome) = prove_with(code, "probe", Some("peel diagram"));
        let Outcome::Stuck(residual) = outcome else {
            panic!("nothing is shared to peel");
        };
        assert!(residual.stopped.contains("`peel`"), "{}", residual.stopped);
        let (_ctx, outcome) = prove_with(code, "probe", Some("inline diagram"));
        let Outcome::Stuck(residual) = outcome else {
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
            "cut (left: the two sides are one diagram; right: inline; the two sides are one term)"
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
        // A false claim buried in one branch arm behind a shared prefix: the
        // residual walks into the reified diagrams rather than printing two
        // whole terms.
        let (ctx, outcome) = prove_identity(
            "identity probe { drop 0 branch { drop 0 push 1 } { not } } = { drop 0 branch { drop 0 push 2 } { not } };",
            "probe",
        );
        let Outcome::Stuck(residual) = outcome else {
            panic!("the arms differ");
        };
        assert!(
            residual.path.iter().any(|step| step.contains("arm")),
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

    /// Which of the corpus's identities the diagram decides, pinned.
    ///
    /// Printed rather than silently counted so an engine change shows
    /// exactly which claims moved. Two sweeps: the goal as stated (calls
    /// opaque, the default stance), and with every call opened first (the
    /// `inline diagram` stance).
    #[test]
    fn the_corpus_identities_the_diagram_decides() {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the crate sits in the workspace")
            .join("tests");
        let mut corpus = crate::corpus::load(&tests).unwrap();
        let library = &corpus.library;
        let terms = &mut corpus.terms;

        let mut plain = Vec::new();
        let mut opened = Vec::new();
        let mut ctx = Ctx::default();
        for (idx, identity) in library.identities.iter_enumerated() {
            let goal = Goal::of_identity(terms, library, idx).unwrap();
            if normalize(&mut ctx, terms, goal.lhs) == normalize(&mut ctx, terms, goal.rhs) {
                plain.push(identity.name.as_str());
            }
            let lhs = inline_calls(terms, library, goal.lhs, None).unwrap();
            let rhs = inline_calls(terms, library, goal.rhs, None).unwrap();
            let unfolded = Goal::aligned(terms, lhs, rhs);
            if normalize(&mut ctx, terms, unfolded.lhs) == normalize(&mut ctx, terms, unfolded.rhs)
            {
                opened.push(identity.name.as_str());
            }
        }

        assert_eq!(
            plain,
            [
                "identities::testing_a_test",
                "identities::a_value_tested_twice",
                "identities::copying_a_constant",
                "identities::discarded_work_on_copies",
                "identities::two_spellings_of_one_test",
                "identities::a_test_inside_an_arm",
                "identities::a_test_inside_an_arm_with_a_prefix",
                "identities::the_guard_a_split_leaves",
                "identities::taking_a_frame_off",
                "identities::comparing_two_built_tuples",
                "identities::untupling_and_retupling_is_the_coercion",
                "identities::specializing_a_tested_value",
            ],
            "calls-opaque: the diagram's reach changed"
        );
        assert_eq!(
            opened,
            library
                .identities
                .iter()
                .map(|i| i.name.as_str())
                .collect::<Vec<_>>(),
            "calls-opened: the diagram's reach changed"
        );
    }
}
