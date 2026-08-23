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
//! [`rules::apply`](crate::diagram2::rules::apply), so the verdict is a
//! derivation's worth of checked steps and one final isomorphism, rather
//! than one engine's word. A stuck `diagram` means the claim is false, or
//! true only for reasons the table cannot yet say — and `cases` is the
//! step for the largest of those: η, a case split on an opaque
//! boolean-valued wire, spent deliberately the way `inline` spends a
//! definition.
//!
//! A stuck goal's residual is **narrowed** for the report — the two sides
//! read back into terms, shared affixes stripped, the differing arm
//! entered — because when the engine says no, where the difference lives
//! is the thing worth printing. A stuck *tactic* reports the goal as it
//! now stands: a failed run leaves its graph at the last step that landed,
//! and showing that state is the point of the guarantee.

use bytecode::{Library, Value};

use crate::diagram2::{self, read_back, tactic};
use crate::goal::{Goal, Outcome, Proof, Residual};
use crate::hant::{Body, OnSide, Step, Strategy, default_strategy};
use crate::term::{Context, Error, Term, TermIndex};

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
        if diagram2::isomorphic(&goal.lhs, &goal.rhs) {
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
                let picks: [fn(&mut Goal) -> &mut diagram2::Graph; 2] =
                    [|g| &mut g.lhs, |g| &mut g.rhs];
                for pick in picks {
                    let mut deriv = diagram2::rules::Derivation::default();
                    if let Err(e) = tactic::run(pick(&mut goal), &mut deriv, &tactic::decide()) {
                        let why = format!("`diagram`'s drive failed: {}", e);
                        return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                    }
                }
                if diagram2::isomorphic(&goal.lhs, &goal.rhs) {
                    return Ok(Outcome::Closed(Proof::Diagram));
                }
                let (l, r) = (read_back(&goal.lhs, ctx), read_back(&goal.rhs, ctx));
                let (mut path, lhs, rhs) = narrow(ctx, l, r);
                path.insert(0, "as diagrams".to_string());
                Ok(Outcome::Stuck(Residual {
                    lhs,
                    rhs,
                    path,
                    stopped: "the two sides rewrite to different diagrams: the claim is \
                              false, or true only for reasons the table cannot yet say"
                        .to_string(),
                }))
            }

            // Split the goal on a boolean-valued wire — η, spent
            // deliberately, the way `inline` spends a definition. Each
            // side pins its **outermost** box of the operation — the one
            // with the least upstream, because pinning a downstream test
            // severs what would have decided it and leaves a case too
            // strong to prove. When both sides hold one, the two must be
            // the same computation of the boundary, or fixing them
            // together would claim more than a case split does.
            Step::Cases {
                prim,
                if_true,
                if_false,
            } => {
                if !(prim.to_instruction().yields_bool() && prim.arity().outputs == 1) {
                    return Ok(Outcome::Stuck(gave_up(
                        ctx,
                        &goal,
                        "`cases` splits only on an operation the set promises answers a bool",
                    )));
                }
                let (l, r) = (outermost(&goal.lhs, prim), outermost(&goal.rhs, prim));
                if l.is_none() && r.is_none() {
                    return Ok(Outcome::Stuck(gave_up(
                        ctx,
                        &goal,
                        "`cases` finds no such operation on either side",
                    )));
                }
                if let (Some(l), Some(r)) = (l, r)
                    && !same_cone(&goal.lhs, l, &goal.rhs, r)
                {
                    return Ok(Outcome::Stuck(gave_up(
                        ctx,
                        &goal,
                        "`cases` found the operation on both sides, and the two are not \
                         the same computation of the boundary",
                    )));
                }
                let mut halves = Vec::with_capacity(2);
                for (value, strategy, name) in [
                    (true, if_true, "in the true case"),
                    (false, if_false, "in the false case"),
                ] {
                    let mut sub = goal.clone();
                    if let Some(wire) = l {
                        diagram2::pin(&mut sub.lhs, wire, Value::Bool(value));
                    }
                    if let Some(wire) = r {
                        diagram2::pin(&mut sub.rhs, wire, Value::Bool(value));
                    }
                    match self.side(ctx, name, strategy, sub)? {
                        Ok(p) => halves.push(p),
                        Err(residual) => return Ok(Outcome::Stuck(residual)),
                    }
                }
                let false_sub = halves.pop().expect("two");
                let true_sub = halves.pop().expect("two");
                Ok(Outcome::Closed(Proof::Cases {
                    true_sub,
                    false_sub,
                }))
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
                let mut steps = 0;
                let picks: &[fn(&mut Goal) -> &mut diagram2::Graph] = match side {
                    OnSide::Lhs => &[|g| &mut g.lhs],
                    OnSide::Rhs => &[|g| &mut g.rhs],
                    OnSide::Both => &[|g| &mut g.lhs, |g| &mut g.rhs],
                };
                for pick in picks {
                    let mut deriv = diagram2::rules::Derivation::default();
                    match tactic::run(pick(&mut goal), &mut deriv, tactic) {
                        Ok(_) => steps += deriv.len(),
                        Err(e) => {
                            let why = format!("`{}(…)`: {}", side.word(), e);
                            return Ok(Outcome::Stuck(gave_up(ctx, &goal, &why)));
                        }
                    }
                }
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Rewrote {
                        side: side.word(),
                        steps,
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
                let target = only.map(|idx| self.library.names[idx].clone());
                Ok(match self.run(ctx, rest, goal)? {
                    Outcome::Closed(sub) => Outcome::Closed(Proof::Inlined {
                        target,
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
}

/// A goal's side and a waypoint, brought to one arity: the narrower is
/// padded — the term with [`Context::under`] before it builds, the graph
/// with [`diagram2::under`] — and the waypoint comes back as a graph.
fn against(
    ctx: &mut Context,
    side: &diagram2::Graph,
    waypoint: TermIndex,
) -> (diagram2::Graph, diagram2::Graph) {
    let (ga, wa) = (side.arity(), ctx.arity(waypoint));
    if wa.inputs < ga.inputs {
        let padded = ctx.under(waypoint, ga.inputs - wa.inputs);
        (side.clone(), diagram2::build(ctx, padded))
    } else {
        (
            diagram2::under(side, wa.inputs - ga.inputs),
            diagram2::build(ctx, waypoint),
        )
    }
}

/// The box of one operation with the least upstream — the outermost
/// decision, which is the one worth splitting on first: everything
/// downstream of it is what the split decides. Ties break by id.
fn outermost(g: &diagram2::Graph, prim: &crate::term::Prim) -> Option<diagram2::NodeId> {
    let cone = |id: diagram2::NodeId| {
        let mut seen = std::collections::HashSet::new();
        let mut todo = vec![id];
        while let Some(node) = todo.pop() {
            if !seen.insert(node) {
                continue;
            }
            for src in g.sources(node) {
                if let diagram2::Source::Port { node, .. } = *src {
                    todo.push(node);
                }
            }
        }
        seen.len()
    };
    g.live()
        .filter(|(_, k)| matches!(k, diagram2::NodeKind::Op(p) if p == prim))
        .map(|(id, _)| id)
        .min_by_key(|&id| (cone(id), id))
}

/// Whether two wires are the **same computation of the boundary**: the
/// same kind of box at every step of both upstream cones, reading the same
/// boundary inputs in the same places. Sharing does not count — two copies
/// of one literal and one literal read twice compute alike — and neither
/// do branch ids, since a fork and a select are pure functions of what
/// they read. This is what lets a `cases` pin both sides' wires to one
/// value and still be a case split rather than a wish.
fn same_cone(
    a: &diagram2::Graph,
    x: diagram2::NodeId,
    b: &diagram2::Graph,
    y: diagram2::NodeId,
) -> bool {
    fn walk(
        a: &diagram2::Graph,
        x: diagram2::NodeId,
        b: &diagram2::Graph,
        y: diagram2::NodeId,
        seen: &mut std::collections::HashSet<(diagram2::NodeId, diagram2::NodeId)>,
    ) -> bool {
        if !seen.insert((x, y)) {
            return true;
        }
        let fits = match (a.kind(x), b.kind(y)) {
            (
                diagram2::NodeKind::Fork { arity: p, .. },
                diagram2::NodeKind::Fork { arity: q, .. },
            )
            | (
                diagram2::NodeKind::Select { arity: p, .. },
                diagram2::NodeKind::Select { arity: q, .. },
            ) => p == q,
            (p, q) => p == q,
        };
        if !fits {
            return false;
        }
        a.sources(x)
            .iter()
            .zip(b.sources(y))
            .all(|(src, dst)| match (*src, *dst) {
                (diagram2::Source::Input(i), diagram2::Source::Input(j)) => i == j,
                (
                    diagram2::Source::Port { node: n, port: p },
                    diagram2::Source::Port { node: m, port: q },
                ) => p == q && walk(a, n, b, m, seen),
                _ => false,
            })
    }
    walk(a, x, b, y, &mut std::collections::HashSet::new())
}

/// A residual for a strategy that failed before any engine ran: the goal as
/// it stands — read back into the term language a report is written in —
/// and why the step gave up. For a failed tactic "as it stands" is the
/// point: the graph reflects the last rewrite that landed.
fn gave_up(ctx: &mut Context, goal: &Goal, why: &str) -> Residual {
    Residual {
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

// ---- inlining, term-level ---------------------------------------------------

/// The term with calls replaced by their bodies: every call, all the way down,
/// or every call to `only` and no others.
///
/// The unlabelled walk terminates because recursion is forbidden — the call
/// graph of a library that compiled is acyclic — and for the same reason the
/// labelled one needs no recursion into the body it just opened: nothing a
/// sentence calls can reach that sentence again.
///
/// The prover opens calls on the graphs now — [`diagram2::inline`] — and
/// this stays as the term-level sweep the reach-pinning test reads by.
#[cfg(test)]
fn inline_calls(
    ctx: &mut Context,
    library: &Library,
    term: TermIndex,
    only: Option<bytecode::SentenceIndex>,
) -> Result<TermIndex, Error> {
    use crate::term::lower;
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
            if diagram2::isomorphic(&goal.lhs, &goal.rhs) {
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
            ],
            "the table's reach changed"
        );
    }
}
