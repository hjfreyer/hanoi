//! A draft of a proof, and the flat run the kernel is handed instead.
//!
//! A [`Proof`] is what the strategy interpreter ([`crate::strategy`])
//! writes as it runs: a tree mirroring the goals a strategy carved — a
//! rewrite here, a swap there, a cut at a waypoint, a branch proved block
//! by block — with the steps each one spent. It is the prover's account of
//! *why* it believes a claim closed, and it is the shape a report reads
//! ([`Proof::summary`]). Nothing trusts it.
//!
//! What the kernel trusts is one thing only: a **run**. [`flatten`] turns
//! the tree into a flat list of [`Step`]s that takes the goal's left
//! side onto its right, and [`certify`](crate::kernel::goal::certify)
//! replays that list and asks whether it landed. Everything a tree could
//! say — that two sides met in the middle, that a swap costs nothing,
//! that a waypoint composes, that a branch's blocks each answer for
//! themselves — is said here as steps instead, and the kernel never learns
//! a split happened. A draft that does not flatten, or a run that does
//! not replay, is a prover bug, and the claim is refused rather than taken
//! on anyone's word.
//!
//! ## Meeting in the middle
//!
//! Most proofs are valleys: steps take the left to some middle graph, other
//! steps take the right to one that is the same program, and the two are
//! compared. A run has one direction, so the right side's steps are
//! **inverted** — every [`apply`] hands back the step that undoes it — and
//! said again in the left side's coordinates. That last part is
//! [`align`]: the two middles are one program, so their live boxes
//! correspond, and a match naming one names the other. Each step is
//! rebased against the alignment of the moment, since a rewrite hands out
//! new ids on both sides.
//!
//! ## A branch, block by block
//!
//! `select-same` proves `select(c, T, E) = B` as `T = B` and `E = B`, each
//! on a subgraph carved from the whole (`blocks`) that shares the whole's
//! boxes. Both arms are handed the same sources, so a box one arm rewrites
//! may be read by the other, or by the condition, or by the `select`
//! itself. What keeps the arms apart in the flat run is the one choice a
//! [`Match`] carries: its **reader selection**. A step recorded on the
//! `then` subgraph re-pointed every live reader there, which is exactly
//! the then-arm's readers; spliced into the whole it names those readers
//! and no other, so the else-arm and the condition go on reading the box
//! they always read, which is still there. Then each arm's full run lands
//! on a graph that is the right side, over the same sources — and since a
//! box is named by what it computes, the two blocks are *one box*, and
//! the law `select-same` closes the branch as an ordinary step.

use std::collections::HashMap;

use bytecode::{Library, SentenceIndex};

use crate::kernel;
use crate::kernel::goal::Goal;
use crate::kernel::graph::{
    self, Direction, Graph, Match, NodeId, NodeKind, Sink, Source, align, isomorphic,
};
use crate::kernel::rules::{self, Law, Rule, Step, apply, propose, sides};
use crate::kernel::term::{Context, TermIndex, lower};

/// How a goal was discharged, as the prover tells it: a tree of the goals
/// a strategy carved, each with the steps it spent. A **draft** — what
/// [`flatten`] reads a run off, and what [`summary`](Proof::summary) prints
/// one-line for the per-identity report — and not what the kernel checks.
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
    /// names — and the opened goal closed. The opens are ordinary steps by
    /// [`Rule::Open`], one per call, per side.
    Inlined {
        target: Option<SentenceIndex>,
        name: Option<String>,
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        sub: Box<Proof>,
    },
    /// A `symm` swapped the sides, and the swapped goal closed. It records
    /// nothing but itself: the claim either way is the same one.
    Swapped(Box<Proof>),
    /// A `via` cut the goal at the waypoint; each half closed
    /// independently. The halves are rebuilt from the waypoint by
    /// `against`, the same way the prover carved them.
    Cut {
        waypoint: TermIndex,
        left_sub: Box<Proof>,
        right_sub: Box<Proof>,
    },
    /// A `select-same` split the goal at the branch its left side answers
    /// with: `select(c, T, E) = B` became `T = B` and `E = B`, each closed
    /// independently. The halves are `blocks`'s to rebuild, from the
    /// goal, the same way the prover carved them.
    SelectSame {
        then_sub: Box<Proof>,
        else_sub: Box<Proof>,
    },
    /// A `cases` expanded a boolean-valued wire — η, spent as the three
    /// table rows it is — on each side that held one, and the expanded goal
    /// closed. The per-side records hold the split(s) and, when the step
    /// carried per-case sub-strategies, every step those landed inside the
    /// arms, in order — all ordinary rewrites. `splits` and `arms` are
    /// presentation only: how many expansions fired, and how many rewrites
    /// each case's sub-strategy spent (both sides summed), when arms were
    /// written.
    Cases {
        lhs: Vec<Step>,
        rhs: Vec<Step>,
        splits: usize,
        arms: Option<(usize, usize)>,
        sub: Box<Proof>,
    },
    /// A `diagram` drove both sides to fixpoint and they were one diagram.
    Diagram { lhs: Vec<Step>, rhs: Vec<Step> },
}

impl Proof {
    /// One line for the report: what the strategy did, outermost first.
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
            Proof::SelectSame { then_sub, else_sub } => format!(
                "select-same (then: {}; else: {})",
                then_sub.summary(),
                else_sub.summary()
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

// ---- the flat run ------------------------------------------------------------------

/// The run this draft says takes the goal's left side onto its right, or
/// why it says no such thing.
///
/// The tree is walked with the left side **as the run so far has left it**
/// — every node's steps were recorded against the very graph the run
/// reaches, since a replay hands out ids in order — and each node
/// contributes its steps in the one direction: a valley's right-side steps
/// inverted and aligned, a cut's second half aligned onto where the first
/// landed, a branch's blocks narrowed to their own readers. Nothing here
/// is checked beyond what stating a step needs; the run is handed to
/// [`certify`](crate::kernel::goal::certify) for that.
pub fn flatten(proof: &Proof, goal: &Goal, ctx: &mut Context) -> Result<Vec<Step>, String> {
    let mut cur = goal.lhs.clone();
    let mut run = Vec::new();
    extract(proof, &mut cur, &goal.rhs, ctx, &mut run)?;
    Ok(run)
}

/// Drives `cur` — the left side as the run so far has left it — onto
/// `rhs`, appending what it spends to `run`. `cur` is left where the run
/// lands, which a caller reads to know what the next thing is aligned to.
fn extract(
    proof: &Proof,
    cur: &mut Graph,
    rhs: &Graph,
    ctx: &mut Context,
    run: &mut Vec<Step>,
) -> Result<(), String> {
    match proof {
        Proof::Trivial => {
            if isomorphic(cur, rhs) {
                Ok(())
            } else {
                Err("claimed trivial, and the sides are not one graph".to_string())
            }
        }
        Proof::Rewrote {
            lhs, rhs: r, sub, ..
        }
        | Proof::Cases {
            lhs, rhs: r, sub, ..
        }
        | Proof::Inlined {
            lhs, rhs: r, sub, ..
        } => valley(lhs, r, Some(sub), cur, rhs, ctx, run),
        Proof::Diagram { lhs, rhs: r } => valley(lhs, r, None, cur, rhs, ctx, run),
        // The sub-proof drives the right side onto the left; its run, read
        // backwards from where the left stands, is this claim's.
        Proof::Swapped(sub) => {
            let mut other = rhs.clone();
            let mut back = Vec::new();
            extract(sub, &mut other, cur, ctx, &mut back)
                .map_err(|e| format!("with the sides swapped: {}", e))?;
            invert_onto(cur, rhs, &back, run).map_err(|e| format!("undoing the swapped run: {}", e))
        }
        Proof::Cut {
            waypoint,
            left_sub,
            right_sub,
        } => {
            // The first half lands on the waypoint as built for the left;
            // the second was written against the waypoint as built for the
            // right — the same graph, box for box — and is aligned onto
            // where the first landed.
            let (side, stone) = against(ctx, cur, *waypoint);
            if !isomorphic(&side, cur) {
                return Err(
                    "the `via` waypoint is wider than the goal, and padding the goal is not a step"
                        .to_string(),
                );
            }
            extract(left_sub, cur, &stone, ctx, run)
                .map_err(|e| format!("in the left half of the cut: {}", e))?;
            let (_, stone) = against(ctx, rhs, *waypoint);
            let mut from = stone.clone();
            let mut second = Vec::new();
            extract(right_sub, &mut from, rhs, ctx, &mut second)
                .map_err(|e| format!("in the right half of the cut: {}", e))?;
            splice(cur, &stone, &second, None, run)
                .map_err(|e| format!("joining the halves of the cut: {}", e))
        }
        Proof::SelectSame { then_sub, else_sub } => {
            let Some((then, els)) = blocks(cur) else {
                return Err(
                    "claimed a `select-same` split, and the left side does not answer with \
                     one branch"
                        .to_string(),
                );
            };
            for (label, block, sub, port) in
                [("then", then, then_sub, 1), ("else", els, else_sub, 2)]
            {
                let mut from = block.clone();
                let mut arm = Vec::new();
                extract(sub, &mut from, rhs, ctx, &mut arm)
                    .map_err(|e| format!("in the branch's {} block: {}", label, e))?;
                splice(cur, &block, &arm, Some(port), run)
                    .map_err(|e| format!("splicing the {} block's run: {}", label, e))?;
            }
            // Both blocks are the right side now, over the same sources, so
            // they are one box and every select answers it either way.
            let selects: Vec<NodeId> = cur
                .outputs()
                .iter()
                .map(|&out| match out {
                    Source::Port { node, port: 0 }
                        if matches!(cur.kind(node), NodeKind::Select) =>
                    {
                        Ok(node)
                    }
                    _ => Err("the blocks' runs left an output that is not a select".to_string()),
                })
                .collect::<Result<_, _>>()?;
            for select in selects {
                if !cur.is_live(select) {
                    // Two outputs answered by one select: the first firing
                    // took care of both.
                    continue;
                }
                let step = propose(cur, &[Law::SelectSame], select)
                    .into_iter()
                    .next()
                    .ok_or_else(|| {
                        "the blocks' runs did not land on one box, so `select-same` has nothing \
                         to say"
                            .to_string()
                    })?;
                apply(cur, &step).map_err(|e| format!("`select-same` refused: {}", e))?;
                run.push(step);
            }
            Ok(())
        }
    }
}

/// A valley: `lhs` steps on the left, `rhs` steps on the right, and a
/// sub-proof of the goal that leaves — or, without one, the two middles
/// one diagram already. The left's steps are the run's; the sub-proof's
/// follow; the right's are inverted onto where that landed.
fn valley(
    lhs: &[Step],
    rhs_steps: &[Step],
    sub: Option<&Proof>,
    cur: &mut Graph,
    rhs: &Graph,
    ctx: &mut Context,
    run: &mut Vec<Step>,
) -> Result<(), String> {
    for step in lhs {
        apply(cur, step).map_err(|e| format!("a recorded left step does not re-apply: {}", e))?;
        run.push(step.clone());
    }
    let mut other = rhs.clone();
    for step in rhs_steps {
        apply(&mut other, step)
            .map_err(|e| format!("a recorded right step does not re-apply: {}", e))?;
    }
    match sub {
        Some(sub) => extract(sub, cur, &other, ctx, run)?,
        None if isomorphic(cur, &other) => {}
        None => return Err("the recorded drives do not land on one diagram".to_string()),
    }
    invert_onto(cur, rhs, rhs_steps, run)
        .map_err(|e| format!("undoing the right side's steps: {}", e))
}

/// The steps that undo `steps` — a run recorded against `start` — spent on
/// `cur`, which stands where that run landed. Afterwards `cur` is `start`'s
/// program.
///
/// Each undo is the step [`apply`] handed back, which names the boxes the
/// forward step put down in `start`'s arena; it is said in `cur`'s by
/// aligning the two graphs as they stand at that moment.
fn invert_onto(
    cur: &mut Graph,
    start: &Graph,
    steps: &[Step],
    run: &mut Vec<Step>,
) -> Result<(), String> {
    let mut states = vec![start.clone()];
    let mut backs = Vec::with_capacity(steps.len());
    for step in steps {
        let mut next = states.last().expect("seeded").clone();
        backs.push(apply(&mut next, step).map_err(|e| e.to_string())?);
        states.push(next);
    }
    for k in (0..steps.len()).rev() {
        let map = align(&states[k + 1], cur).ok_or_else(|| {
            format!(
                "after step {} of {}, the sides are not one program",
                k + 1,
                steps.len()
            )
        })?;
        let there = Step {
            rule: backs[k].rule.clone(),
            dir: backs[k].dir,
            at: carry(&backs[k].at, &map)?,
        };
        apply(cur, &there).map_err(|e| format!("undoing step {}: {}", k + 1, e))?;
        run.push(there);
    }
    Ok(())
}

/// A run recorded against `from` spent on `cur`, step by step, each one
/// aligned as the two stand. Without `arm`, `cur` is `from`'s program.
/// With `arm`, `cur` is a branch whose every output is a select and
/// `from` is the block that select's port `arm` reads, carved by
/// [`blocks`]: the alignment is against that view of `cur`, and every step
/// is **narrowed** to the readers it had in `from` — the block's own boxes,
/// and, for the block's boundary, the select's port — so the other block
/// and the condition are left reading what they read.
fn splice(
    cur: &mut Graph,
    from: &Graph,
    steps: &[Step],
    arm: Option<usize>,
    run: &mut Vec<Step>,
) -> Result<(), String> {
    let mut from = from.clone();
    for (k, step) in steps.iter().enumerate() {
        let selects = match arm {
            None => Vec::new(),
            Some(port) => output_selects(cur, port)?,
        };
        let view = match arm {
            None => cur.clone(),
            Some(port) => {
                let mut view = cur.clone();
                view.close(selects.iter().map(|&s| cur.sources(s)[port]).collect());
                view
            }
        };
        let map = align(&from, &view)
            .ok_or_else(|| format!("before step {}, the run's graph is not the block", k + 1))?;
        let at = match arm {
            None => carry(&step.at, &map)?,
            Some(port) => {
                // What the step re-pointed in the block, named in the
                // whole: every live reader there, or the ones it chose.
                let pair = sides(&step.rule).map_err(|e| e.to_string())?;
                let pattern = pair.pattern(step.dir);
                let image = |src: Source| match src {
                    Source::Input(i) => step.at.inputs[i],
                    Source::Port { node, port } => Source::Port {
                        node: step.at.nodes[node.index()],
                        port,
                    },
                };
                let chosen: Vec<Vec<Sink>> = match &step.at.sel {
                    Some(sel) => sel.clone(),
                    None => pattern
                        .outputs()
                        .iter()
                        .map(|&src| from.sinks(image(src)))
                        .collect(),
                };
                let sel = chosen
                    .iter()
                    .map(|sinks| {
                        sinks
                            .iter()
                            .map(|&sink| match sink {
                                Sink::Port { node, port } => map
                                    .get(&node)
                                    .map(|&node| Sink::Port { node, port })
                                    .ok_or_else(|| {
                                        format!("step {} names a reader outside the block", k + 1)
                                    }),
                                Sink::Output(i) => Ok(Sink::Port {
                                    node: selects[i],
                                    port,
                                }),
                            })
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                // And the region the rewrite runs in: every reading of the
                // block's own boxes, the select's port for the block, and
                // the boundary, which reads the select. A box the other
                // block shares is rebuilt for this block's readers only;
                // the other block, and the condition, go on reading the one
                // that stood.
                let region: Vec<Sink> = map
                    .values()
                    .flat_map(|&node| {
                        (0..cur.kind(node).arity().inputs)
                            .map(move |port| Sink::Port { node, port })
                    })
                    .chain(selects.iter().map(|&node| Sink::Port { node, port }))
                    .chain((0..cur.outputs().len()).map(Sink::Output))
                    .collect();
                let plain = Match {
                    sel: None,
                    follow: None,
                    ..step.at.clone()
                };
                Match {
                    sel: Some(sel),
                    follow: Some(region),
                    ..carry(&plain, &map)?
                }
            }
        };
        let there = Step {
            rule: step.rule.clone(),
            dir: step.dir,
            at,
        };
        apply(cur, &there).map_err(|e| format!("step {} spliced in: {}", k + 1, e))?;
        run.push(there);
        apply(&mut from, step).map_err(|e| format!("step {} does not re-apply: {}", k + 1, e))?;
    }
    Ok(())
}

/// The select each output of `cur` is answered by, in output order.
fn output_selects(cur: &Graph, port: usize) -> Result<Vec<NodeId>, String> {
    debug_assert!(port == 1 || port == 2);
    cur.outputs()
        .iter()
        .map(|&out| match out {
            Source::Port { node, port: 0 } if matches!(cur.kind(node), NodeKind::Select) => {
                Ok(node)
            }
            _ => Err("the branch's outputs are no longer all selects".to_string()),
        })
        .collect()
}

/// A match said in another graph's names, refusing rather than guessing
/// where a box it names has no counterpart there.
fn carry(at: &Match, map: &HashMap<NodeId, NodeId>) -> Result<Match, String> {
    let mut named: Vec<NodeId> = at.nodes.clone();
    named.extend(at.inputs.iter().filter_map(|&src| match src {
        Source::Port { node, .. } => Some(node),
        Source::Input(_) => None,
    }));
    let sinks = at
        .sel
        .iter()
        .flatten()
        .flatten()
        .chain(at.follow.iter().flatten());
    named.extend(sinks.filter_map(|&sink| match sink {
        Sink::Port { node, .. } => Some(node),
        Sink::Output(_) => None,
    }));
    if let Some(lost) = named.iter().find(|id| !map.contains_key(id)) {
        return Err(format!(
            "the step names box {}, which the program as it stands does not reach",
            lost
        ));
    }
    Ok(at.rebase(map))
}

// ---- opening calls -----------------------------------------------------------------

/// Opens calls in place: every [`NodeKind::Call`] — or, with `only`, every
/// call to that one sentence — replaced by the graph of its body, its
/// readers re-pointed at what the body leaves.
///
/// Definitional unfolding, not a law: each open is a [`Step`] by
/// [`Rule::Open`], the call's own one-box window against the body's graph,
/// and the [`Match`] is read straight off the call, since a window of one
/// box that exports every port has nothing left to choose. Unlabelled, it
/// opens all the way down (recursion is forbidden, so the walk drains);
/// labelled, one pass, and the opened body's own calls stay shut.
///
/// Answers the steps it spent, in order, so a proof carries them; empty is
/// the caller's business to refuse. This is search — which call, in what
/// order — and lives outside the kernel for that reason: the body a step
/// carries is what [`certify`](crate::kernel::goal::certify) holds to the
/// library.
pub fn inline(
    graph: &mut Graph,
    terms: &mut Context,
    library: &Library,
    only: Option<SentenceIndex>,
) -> Result<Vec<Step>, crate::kernel::term::Error> {
    let mut opened = Vec::new();
    // One at a time, asked again each time round. A rewrite rebuilds
    // everything downstream of what it replaced, so a call that sat under
    // an opened one is a *new* box afterwards and the id that named it is
    // stale — which is why the calls are looked for rather than listed.
    //
    // Draining is one pass either way: a sentence may not reach itself, so
    // a call to `target` never appears inside `target`'s own body, and
    // `only` opening until none is left opens exactly the ones that were
    // there.
    loop {
        let call = graph.live().find_map(|(id, kind)| match kind {
            NodeKind::Call { target, .. } if only.is_none_or(|t| t == *target) => {
                Some((id, *target))
            }
            _ => None,
        });
        let Some((id, target)) = call else {
            return Ok(opened);
        };
        let body = lower(terms, library, target)?;
        let step = Step {
            rule: Rule::Open {
                target,
                body: kernel::build(terms, body),
            },
            dir: Direction::Forward,
            at: Match {
                nodes: vec![id],
                inputs: graph.sources(id).to_vec(),
                sel: None,
                follow: None,
            },
        };
        rules::apply(graph, &step).expect("a call is the window its own box fills");
        opened.push(step);
    }
}

// ---- carving a goal ----------------------------------------------------------------

/// A goal's side and a waypoint, brought to one arity: the narrower is
/// padded — the term with [`Context::under`] before it builds, the graph
/// with [`graph::under`] — and the waypoint comes back as a graph. Both
/// the prover's `via` and [`flatten`]'s walk of a [`Proof::Cut`] build
/// their halves here, so the two cannot disagree about what a cut means.
pub(crate) fn against(ctx: &mut Context, side: &Graph, waypoint: TermIndex) -> (Graph, Graph) {
    let (ga, wa) = (side.arity(), ctx.arity(waypoint));
    if wa.inputs < ga.inputs {
        let padded = ctx.under(waypoint, ga.inputs - wa.inputs);
        (side.clone(), kernel::build(ctx, padded))
    } else {
        (
            graph::under(side, wa.inputs - ga.inputs),
            kernel::build(ctx, waypoint),
        )
    }
}

/// The two graphs a side that **answers with one branch** is: the same
/// side reading the `select`s' `then` blocks for its outputs, and the same
/// side reading their `else` blocks.
///
/// A branch is a `select` per answer, so a side answering with one is a
/// `select` per boundary output, every one of them turning on the same
/// wire. That is what this asks for, and `None` where it does not hold: an
/// output that is not a select's answer, or a select turning on some other
/// condition, is a side answering with something besides the branch, and
/// the law has nothing to say about it.
///
/// Nothing is deleted to carve a block out: closing the graph on the
/// blocks' sources leaves the condition — and the other blocks — boxes no
/// boundary output reaches, which is the whole of what discarding means
/// here. The blocks keep the whole's ids, which is what lets a step
/// recorded on one be spliced back into the whole by [`flatten`].
pub(crate) fn blocks(side: &Graph) -> Option<(Graph, Graph)> {
    let outputs = side.outputs().to_vec();
    if outputs.is_empty() {
        return None;
    }
    let mut selects: Vec<NodeId> = Vec::with_capacity(outputs.len());
    let mut cond: Option<Source> = None;
    for out in outputs {
        let Source::Port { node, port: 0 } = out else {
            return None;
        };
        if !matches!(side.kind(node), NodeKind::Select) {
            return None;
        }
        let turns_on = side.sources(node)[0];
        if *cond.get_or_insert(turns_on) != turns_on {
            return None;
        }
        selects.push(node);
    }
    let block =
        |which: usize| -> Vec<Source> { selects.iter().map(|&n| side.sources(n)[which]).collect() };
    let mut then = side.clone();
    then.close(block(1));
    let mut els = side.clone();
    els.close(block(2));
    Some((then, els))
}

// ---- what a run answers ------------------------------------------------------------

/// What is left when a goal did not close: what each side became, as the
/// graphs the tactics left.
///
/// A graph is what there is to read: it is what a step acted on, it carries
/// the boxes a next step would name, and a box's id is stable across a step
/// so two reports of one proof can be compared. There is no term here — the
/// translation runs one way, and a graph is answered by naming its boxes,
/// not by being spelled back out.
///
/// This output is the deliverable of a failed run — it is what says what to
/// try next, so it is kept as data rather than printed on the spot.
#[derive(Debug)]
pub struct Residual {
    /// The two sides as they stand, which is what the report *shows*: a
    /// graph is what the tactics act on, and a box in one has a name that
    /// survives a step, so two of these compare. See
    /// [`render`](crate::render).
    pub lhs_graph: Graph,
    pub rhs_graph: Graph,
    /// How the report walked from the goal as stated to the one that stuck:
    /// each step of the strategy that holds it, outermost first.
    pub path: Vec<String>,
    /// Why the step gave up.
    pub stopped: String,
}

/// The answer for one goal.
#[derive(Debug)]
pub enum Outcome {
    /// The claim closed: the draft the strategy wrote, and the flat run
    /// [`flatten`] read off it, which the kernel has certified against the
    /// goal as stated. The run is what a `by` spends.
    Closed {
        draft: Proof,
        run: Vec<Step>,
    },
    Stuck(Residual),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::goal::certify;
    use crate::kernel::rules::replay;
    use crate::kernel::tests::built;
    use crate::strategy::Prover;
    use bytecode::{Library, assemble};

    fn identity(code: &str) -> (Library, Context, Goal) {
        let library = assemble(code).unwrap();
        let mut ctx = Context::new();
        let idx = library.identity_by_name("probe").unwrap();
        let goal = Goal::of_identity(&mut ctx, &library, idx).unwrap();
        (library, ctx, goal)
    }

    /// The draft the prover writes and the run it certifies, for a proof
    /// written in the strategy language.
    fn prove(code: &str, strategy: &str) -> (Library, Context, Goal, Proof, Vec<Step>) {
        let (library, mut ctx, goal) = identity(code);
        let strategy = crate::hant::parse_hant(&format!("proof probe = {};", strategy))
            .unwrap()
            .remove(0)
            .strategy;
        let strategy = crate::corpus::attach(&mut ctx, &strategy, &library).unwrap();
        let outcome = Prover::new(&library)
            .prove(&mut ctx, goal.clone(), Some(&strategy))
            .unwrap();
        let Outcome::Closed { draft, run } = outcome else {
            panic!("{}: {:?}", code, outcome);
        };
        (library, ctx, goal, draft, run)
    }

    // ---- a valley, and a swap ----

    /// Steps on both sides flatten to one run from the left to the right:
    /// the left's steps, then the right's undone, and the kernel replays
    /// the lot against the goal as stated.
    #[test]
    fn a_valley_flattens_to_one_run() {
        let (library, mut ctx, goal, draft, run) = prove(
            "identity probe { push 1 push 2 add } = { push 0 push 3 add };",
            "diagram",
        );
        let Proof::Diagram { lhs, rhs } = &draft else {
            panic!("{}", draft.summary());
        };
        assert!(!lhs.is_empty() && !rhs.is_empty(), "both sides fold");
        assert_eq!(run.len(), lhs.len() + rhs.len());
        // The run is the flat thing: replayed on the left, it *is* the
        // right, and the draft's own right-side steps are nowhere in it as
        // written — they were turned round.
        assert_eq!(flatten(&draft, &goal, &mut ctx).unwrap(), run);
        certify(&goal, &run, &mut ctx, &library).unwrap();
        let mut lhs = goal.lhs.clone();
        replay(&mut lhs, &run).unwrap();
        assert!(isomorphic(&lhs, &goal.rhs));
    }

    /// `symm` costs nothing: the swapped proof's run, undone, is this one.
    #[test]
    fn a_swap_is_free() {
        let (library, mut ctx, goal, draft, run) = prove(
            "identity probe { push 1 push 2 add } = { push 0 push 3 add };",
            "symm diagram",
        );
        assert!(matches!(draft, Proof::Swapped(_)), "{}", draft.summary());
        certify(&goal, &run, &mut ctx, &library).unwrap();
    }

    // ---- a branch, block by block ----

    /// `select-same` with a box both blocks and the condition read, and a
    /// box the two blocks share below it: each block's run rewrites the
    /// shared boxes for that block's readers only, the two blocks land on
    /// one box, and the law closes the branch. The condition, and the
    /// other block until its own run, go on reading what they read.
    #[test]
    fn select_same_keeps_the_blocks_apart() {
        // `b = not not x`; `s = b * 3`, read by the condition and by both
        // blocks; then `s + (1 + 2)`, else `s + 3`. The right side is
        // `as_bool x * 3 + 3`, which each block is once `not-not` has
        // rewritten `b` — and, for the then block, the sum has folded.
        let (library, mut ctx, goal, draft, run) = prove(
            "identity probe \
               { not not push 3 multiply pick 0 is_bool branch { push 1 push 2 add add } { push 3 add } } \
             = { as_bool push 3 multiply push 3 add };",
            "select-same (then: lhs(fire(not-not)) lhs(fire(fold)), else: lhs(fire(not-not)))",
        );
        assert!(
            matches!(draft, Proof::SelectSame { .. }),
            "{}",
            draft.summary()
        );
        let laws: Vec<Law> = run.iter().map(|s| s.rule.law()).collect();
        assert_eq!(
            laws,
            vec![Law::NotNot, Law::Fold, Law::NotNot, Law::SelectSame]
        );
        certify(&goal, &run, &mut ctx, &library).unwrap();

        // After the then block's run, its block is the right side's sum
        // over `as_bool x` — and the else block and the condition still
        // read `s` as it was, over `not not x`. The shared `s` was
        // rebuilt for the then block's readers and for nobody else.
        let mut lhs = goal.lhs.clone();
        for step in &run[..2] {
            assert!(step.at.follow.is_some(), "narrowed to the block");
            apply(&mut lhs, step).unwrap();
        }
        let (select, _) = lhs
            .live()
            .find(|(_, k)| matches!(k, NodeKind::Select))
            .unwrap();
        let [cond, then, els] = lhs.sources(select)[..] else {
            panic!()
        };
        use crate::kernel::term::Prim;
        let producer = |src: Source| -> NodeId {
            let Source::Port { node, .. } = src else {
                panic!()
            };
            node
        };
        // then: add(s', 3) with s' = mul(as_bool x, 3)
        let s_then = producer(lhs.sources(producer(then))[0]);
        assert_eq!(lhs.kind(s_then), &NodeKind::Op(Prim::Multiply));
        assert_eq!(
            lhs.kind(producer(lhs.sources(s_then)[0])),
            &NodeKind::Op(Prim::AsBool)
        );
        // else: add(s, 3) with s = mul(not not x, 3), the box that stood
        let s_else = producer(lhs.sources(producer(els))[0]);
        assert_ne!(
            s_then, s_else,
            "the shared box was rebuilt for one block only"
        );
        assert_eq!(lhs.kind(s_else), &NodeKind::Op(Prim::Multiply));
        assert_eq!(
            lhs.kind(producer(lhs.sources(s_else)[0])),
            &NodeKind::Op(Prim::Not)
        );
        // and the condition reads the box that stood too
        assert_eq!(producer(lhs.sources(producer(cond))[0]), s_else);
    }

    /// A draft that claims a split of a side that is no branch has nothing
    /// to carve, and says so.
    #[test]
    fn a_split_of_no_branch_does_not_flatten() {
        let (_library, mut ctx, goal) = identity("identity probe { push 1 } = { push 1 };");
        let draft = Proof::SelectSame {
            then_sub: Box::new(Proof::Trivial),
            else_sub: Box::new(Proof::Trivial),
        };
        let err = flatten(&draft, &goal, &mut ctx).unwrap_err();
        assert!(err.contains("does not answer with one branch"), "{}", err);
    }

    // ---- opening a call ----

    /// A call opened in place is the body's boxes on the call's wires —
    /// the same graph building the opened term would have made — and the
    /// opens are steps a run carries.
    #[test]
    fn a_call_opens_in_place() {
        let code = r#"
            #[arity(1,1)] sentence inner { not not }
            #[arity(1,1)] sentence outer { jump crate::inner }
            sentence probe { jump crate::outer }
        "#;
        let library = assemble(code).unwrap();
        let named = |name: &str| {
            library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(idx, _)| idx)
                .unwrap()
        };
        let mut terms = Context::new();
        let term = lower(&mut terms, &library, named("probe")).unwrap();
        let mut graph = kernel::build(&terms, term);

        // A labelled inline opens that sentence and leaves what it calls
        // shut.
        let mut labelled = graph.clone();
        let opened = inline(&mut labelled, &mut terms, &library, Some(named("outer"))).unwrap();
        assert_eq!(opened.len(), 1);
        labelled.check().unwrap();
        assert!(matches!(
            labelled.live().next().map(|(_, k)| k),
            Some(NodeKind::Call { target, .. }) if *target == named("inner")
        ));

        // Unlabelled opens all the way down, and lands on the graph the
        // opened term builds.
        let before = graph.clone();
        let opened = inline(&mut graph, &mut terms, &library, None).unwrap();
        assert_eq!(opened.len(), 2);
        graph.check().unwrap();
        let (_t, flat) = built("not not");
        assert!(isomorphic(&graph, &flat), "\n{}\n{}", graph, flat);
        assert!(
            inline(&mut graph, &mut terms, &library, None)
                .unwrap()
                .is_empty()
        );

        // The opens are ordinary steps: replayed on the graph as it was,
        // they land on the same program.
        let mut again = before;
        replay(&mut again, &opened).unwrap();
        assert!(isomorphic(&again, &graph), "\n{}\n{}", again, graph);
    }

    /// An `Open` carries the body it opens to, and the kernel holds that
    /// body to the library: a run that opens a call to some other program
    /// is refused before the step is spent, however well the step applies.
    #[test]
    fn a_body_the_library_did_not_say_does_not_open() {
        let code = r#"
            #[arity(1,1)] sentence inner { not not }
            identity probe { jump crate::inner } = { as_bool };
        "#;
        let (library, mut ctx, goal, draft, run) = prove(code, "inline diagram");
        assert!(
            matches!(draft, Proof::Inlined { .. }),
            "{}",
            draft.summary()
        );
        certify(&goal, &run, &mut ctx, &library).unwrap();

        // The same run, its open lying about the body: `as_bool` is the
        // claim's own right side, so the run would land — and is refused.
        let mut lying = run.clone();
        let Rule::Open { body, .. } = &mut lying[0].rule else {
            panic!("the first step opens the call");
        };
        let (_t, other) = built("as_bool");
        *body = other;
        let err = certify(&goal, &lying, &mut ctx, &library).unwrap_err();
        assert!(err.contains("not its own"), "{}", err);
    }

    /// A run written for one claim does not certify another: its steps
    /// name boxes the other goal never had.
    #[test]
    fn a_run_answers_for_its_own_claim_only() {
        let (library, mut ctx, goal, _draft, run) = prove(
            "identity probe { push 1 push 2 add } = { push 3 };",
            "diagram",
        );
        let (other_lib, mut other_ctx, other) = identity("identity probe { push 1 } = { push 2 };");
        let err = certify(&other, &run, &mut other_ctx, &other_lib).unwrap_err();
        assert!(err.contains("does not apply"), "{}", err);
        // And an empty run for a claim whose sides differ does not land.
        let err = certify(&other, &[], &mut other_ctx, &other_lib).unwrap_err();
        assert!(err.contains("does not land"), "{}", err);
        certify(&goal, &run, &mut ctx, &library).unwrap();
    }
}
