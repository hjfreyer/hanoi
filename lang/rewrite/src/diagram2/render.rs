//! A graph written for someone reading a proof.
//!
//! [`Display for Graph`](super::Graph) is the other listing, and it is for a
//! different reader: it dumps the links in id order so that a broken one can
//! be found, which is what [`Graph::check`](super::Graph::check) wants when
//! it panics. This one is for a goal that did not close. It says the same
//! facts and orders them so a person can follow the program, which is a
//! different job and is worth its own code.
//!
//! The report used to be the goal read back as a *term*, and a term is the
//! wrong shape for it twice over. A graph is a DAG and a term is a spine, so
//! [`read_back`](super::read_back) has to reimpose a stack and pay for it in
//! routing; and a term has no name for a box, so two consecutive steps of a
//! proof cannot be compared. A [`NodeId`] is stable for the life of a graph —
//! nodes are only ever deleted, never moved — so a listing keyed by one is a
//! diff, and "31 boxes went, the branches are gone" is a sentence about what
//! a tactic did.
//!
//! The term has not gone anywhere. It is the language a `via` waypoint is
//! written in, so a stuck goal still prints one to copy from; this is what
//! is printed to *understand* the goal, and that is the split.
//!
//! ## A branch is a block
//!
//! The two ends of a branch are not boxes a reader wants to see as boxes.
//! What they want is where the arms begin and end, and every reader of code
//! already knows how to read that:
//!
//! ```text
//!   #6    if #5.1                     on #3.0            → #7 #15
//!   #7    | copy(1)                   ← #6.0             → #8 #9
//!   ...
//!         else #5.1
//!   #15   | negate                    ← #6.1             → #16
//!   #16   endif #5.1                  then #14.0  else #15.0   → out0
//! ```
//!
//! The condition is named on all three lines, so a block deep in a nest
//! says which wire it turns on without a reader counting bars. The `if` is
//! the [`Fork`](super::NodeKind::Fork) where there is one and the `endif`
//! is always the [`Select`](super::NodeKind::Select), so both keep their
//! ids and their links: the right-hand columns still say what the box
//! reads and who reads it, which is what a next proof step names. A line
//! with an **empty id column** is one the listing drew rather than a box —
//! every `else`, and the `if` of a branch with no fork.
//!
//! ## What makes 351 boxes legible
//!
//! Five decisions, and the listing is a wall without any of them.
//!
//! **Branch membership is computed.** A node is inside a branch when it is
//! downstream of the [`Fork`](super::NodeKind::Fork) and upstream of the
//! [`Select`](super::NodeKind::Select) it is paired with — a forward reach
//! and a backward reach, intersected. So the indentation is a fact about the
//! graph rather than a guess from what happens to sit between two lines, and
//! an arm that reaches out of itself still reads as an arm.
//!
//! **A branch's boxes come out as one run.** The schedule
//! [`read_back`](super::read_back) uses is min-id-first, which is
//! topological and nothing else: it hoists the constants an arm pushes out
//! of the arm, and the arm stops reading as a unit. Nor is a greedy "stay
//! where you are" enough — preferring the ready box that shares the most
//! branches with the last one *leaves* a region whenever nothing inside it
//! is ready, and comes back later, which is what makes an `if` and its
//! `endif` land at different depths. The regions are **laminar**
//! (any two disjoint or nested, since a branch's arms lie wholly between
//! its ends), so [`schedule`] contracts each to a single unit at its
//! parent's level and orders the units: a region is placed whole, and
//! leaving one is not a move the schedule has.
//!
//! **A box that reads nothing sits just before the box that reads it — but
//! outside any branch it is not part of.** A `push` is ready before
//! everything, so left alone the whole constant pool lands in one slab at
//! the top and an `equal`'s operand is forty lines from the `equal`. Every
//! topological order may put such a box anywhere before its first reader,
//! so it goes immediately before — backing out first past any branch that
//! reader is in and it is not, since a literal several arms share belongs
//! to none of them and dropping it inside one would break the run the
//! schedule just made.
//!
//! **The arms come out in the order a reader reads them.** A branch's
//! region splits in two — every box in it is upstream of one of the
//! select's two block lists and never of both — so the schedule emits the
//! then side, then the else side, and [`arms`] is the reading that says
//! which is which. An `else` is drawn where the second begins, and left
//! out where the else arm owns no boxes at all: the `endif` names both
//! blocks, and a separator with nothing after it says only that the
//! listing draws separators.
//!
//! **A branch that owns no boxes still gets its block.** Its arms are
//! wholly boxes a branch around it also holds, so `nesting` gives them to
//! neither and there is no first box to hang an opening `if` on. The
//! listing draws one against the `select` itself rather than printing an
//! `endif` that closes nothing.
//!
//! **`id` and `copy` are read through.** They are what the structural laws
//! delete, and a `copy` says what the links already say — a value read
//! twice. On the corpus's biggest goal that is 156 boxes of 351. They are
//! still there and [`Listing::all_boxes`] shows them, because a proof about
//! a `copy` needs to see it.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::graph::{Graph, NodeId, NodeKind, Sink, Source};

/// One side of a goal, written out. Build it with [`listing`].
pub struct Listing<'g> {
    graph: &'g Graph,
    tag: &'g str,
    elide: bool,
}

/// A graph as a listing, `id` and `copy` read through.
pub fn listing<'g>(graph: &'g Graph, tag: &'g str) -> Listing<'g> {
    Listing {
        graph,
        tag,
        elide: true,
    }
}

impl<'g> Listing<'g> {
    /// Every box, `id` and `copy` included — what a proof about one of them
    /// needs, and what the boundary of a rewrite is stated in.
    pub fn all_boxes(mut self) -> Self {
        self.elide = false;
        self
    }
}

/// Whether the rewriting is there to delete this, which is also whether a
/// reader is better off looking straight through it.
fn structural(kind: &NodeKind) -> bool {
    matches!(kind, NodeKind::Id(_) | NodeKind::Copy(_))
}

/// Everything reachable from `from`, forwards or backwards.
fn reach(graph: &Graph, from: NodeId, forward: bool) -> HashSet<NodeId> {
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([from]);
    while let Some(node) = queue.pop_front() {
        if !seen.insert(node) {
            continue;
        }
        if forward {
            for port in 0..graph.kind(node).arity().outputs {
                for &sink in graph.sinks(Source::Port { node, port }) {
                    if let Sink::Port { node, .. } = sink {
                        queue.push_back(node);
                    }
                }
            }
        } else {
            for &source in graph.sources(node) {
                if let Source::Port { node, .. } = source {
                    queue.push_back(node);
                }
            }
        }
    }
    seen
}

/// Which branches each box lies inside.
///
/// A box is inside branch `b` when it is downstream of `b`'s fork and
/// upstream of `b`'s select — exactly the boxes that are `b`'s arms, however
/// the schedule happens to order them. The two ends are not inside
/// themselves; a listing draws them as the brackets they are.
///
/// A branch whose arms read nothing off the stack has **no fork**: a
/// `fork(0)` would hand out no views and [`build`](super::build) does not
/// emit one. Then what is downstream of the fork is not a question that can
/// be asked, and the arms are instead what feeds the select's arm ports —
/// less whatever also feeds its condition, and less anything read from
/// outside, since a box two regions share is inside neither.
///
/// A box that reads nothing belongs to no branch by that test and still
/// *belongs* to the arm that reads it — a `push` is an operand, and the arm
/// is where a reader looks for it. Such a box goes where everything reading
/// it agrees it is: the intersection of its readers' branches, to fixpoint,
/// so a constant feeding a constant follows along.
fn nesting(graph: &Graph) -> HashMap<NodeId, BTreeSet<u32>> {
    let mut forks = HashMap::new();
    let mut selects = HashMap::new();
    for (id, kind) in graph.live() {
        match kind {
            NodeKind::Fork { branch, .. } => forks.insert(branch.index(), id),
            NodeKind::Select { branch, .. } => selects.insert(branch.index(), id),
            _ => None,
        };
    }
    let mut inside: HashMap<NodeId, BTreeSet<u32>> = HashMap::new();
    for (&branch, &select) in &selects {
        let arms = match forks.get(&branch) {
            Some(&fork) => {
                let mut arms = reach(graph, fork, true);
                arms.retain(|node| reach(graph, select, false).contains(node));
                arms.remove(&fork);
                arms
            }
            None => armless(graph, select),
        };
        for node in arms {
            if node != select {
                inside.entry(node).or_default().insert(branch as u32);
            }
        }
    }

    let ids: Vec<NodeId> = graph.live().map(|(id, _)| id).collect();
    loop {
        let mut moved = false;
        for &id in ids.iter().rev() {
            if inside.contains_key(&id) || !graph.sources(id).is_empty() {
                continue;
            }
            let mut readers: Vec<BTreeSet<u32>> = Vec::new();
            for port in 0..graph.kind(id).arity().outputs {
                for &sink in graph.sinks(Source::Port { node: id, port }) {
                    readers.push(match sink {
                        // A value the boundary reads is inside nothing, and
                        // an intersection with it is empty, which is right.
                        Sink::Output(_) => BTreeSet::new(),
                        Sink::Port { node, .. } => inside.get(&node).cloned().unwrap_or_default(),
                    });
                }
            }
            let Some(first) = readers.first().cloned() else {
                continue;
            };
            let agreed = readers
                .iter()
                .fold(first, |acc, set| acc.intersection(set).copied().collect());
            if !agreed.is_empty() {
                inside.insert(id, agreed);
                moved = true;
            }
        }
        if !moved {
            break;
        }
    }

    // A branch nested inside another is wholly inside it: its ends are, so
    // its arms are too. Each branch above was asked on its own, and a
    // forkless branch's arms can read nothing at all — no fork to be
    // downstream of, so no reach to place them by — which leaves them
    // knowing their own branch and no other. This is where they learn the
    // rest, and it is what makes the depth a box is drawn at agree with
    // the depth its brackets open at.
    loop {
        let mut moved = false;
        for (&branch, &select) in &selects {
            let branch = branch as u32;
            let outer = inside.get(&select).cloned().unwrap_or_default();
            if outer.is_empty() {
                continue;
            }
            let held: Vec<NodeId> = inside
                .iter()
                .filter(|(_, mine)| mine.contains(&branch))
                .map(|(&id, _)| id)
                .collect();
            for id in held {
                let mine = inside.get_mut(&id).expect("it was just listed");
                for enclosing in &outer {
                    moved |= mine.insert(*enclosing);
                }
            }
        }
        if !moved {
            break;
        }
    }
    inside
}

/// The arms of a branch that has no fork: what feeds the select's arm ports
/// and nothing else.
///
/// Without a fork nothing marks an arm's boxes as the arm's own, so the
/// question is asked from the other end. Start from everything upstream of
/// the arm ports, drop what is also upstream of the condition — that is
/// shared context, computed before the branch was ever reached — and then
/// shrink to a fixpoint by dropping any box something outside the region
/// reads, because a box two regions share belongs to neither.
fn armless(graph: &Graph, select: NodeId) -> HashSet<NodeId> {
    let upstream = |source: &Source| match *source {
        Source::Port { node, .. } => reach(graph, node, false),
        Source::Input(_) => HashSet::new(),
    };
    let sources = graph.sources(select);
    let Some((condition, arms)) = sources.split_first() else {
        return HashSet::new();
    };
    let shared = upstream(condition);
    let mut region: HashSet<NodeId> = arms
        .iter()
        .flat_map(upstream)
        .filter(|node| !shared.contains(node))
        .collect();
    loop {
        let escapes: Vec<NodeId> = region
            .iter()
            .copied()
            .filter(|&node| {
                (0..graph.kind(node).arity().outputs).any(|port| {
                    graph
                        .sinks(Source::Port { node, port })
                        .iter()
                        .any(|sink| match sink {
                            Sink::Output(_) => true,
                            Sink::Port { node, .. } => *node != select && !region.contains(node),
                        })
                })
            })
            .collect();
        if escapes.is_empty() {
            return region;
        }
        for node in escapes {
            region.remove(&node);
        }
    }
}

/// Which arm of each branch a box belongs to — `true` for the then side.
///
/// A branch's region splits cleanly in two. Every box in it is upstream of
/// one of the `select`'s two block lists, and never of both: the sides are
/// backward reaches from disjoint sets of blocks, so a box the then side
/// reads is a then-side box by that very fact. That is what lets the
/// listing draw an `else`, and it is why the split is a **reading** rather
/// than a choice.
fn arms(graph: &Graph, inside: &HashMap<NodeId, BTreeSet<u32>>) -> HashMap<(NodeId, u32), bool> {
    let mut region: HashMap<u32, HashSet<NodeId>> = HashMap::new();
    for (&id, branches) in inside {
        for &branch in branches {
            region.entry(branch).or_default().insert(id);
        }
    }
    let mut out: HashMap<(NodeId, u32), bool> = HashMap::new();
    for (select, kind) in graph.live() {
        let NodeKind::Select { arity, branch } = kind else {
            continue;
        };
        let branch = branch.index() as u32;
        let Some(mine) = region.get(&branch) else {
            continue;
        };
        let sources = graph.sources(select).to_vec();
        for (blocks, side) in [(&sources[1..=*arity], true), (&sources[1 + arity..], false)] {
            let mut todo: Vec<Source> = blocks.to_vec();
            let mut seen: HashSet<NodeId> = HashSet::new();
            while let Some(source) = todo.pop() {
                let Source::Port { node, .. } = source else {
                    continue;
                };
                if !mine.contains(&node) || !seen.insert(node) {
                    continue;
                }
                let was = out.insert((node, branch), side);
                debug_assert!(
                    was.is_none_or(|was| was == side),
                    "{} is on both sides of branch {}",
                    node,
                    branch
                );
                todo.extend(graph.sources(node).iter().copied());
            }
        }
    }
    out
}

/// A topological order in which every branch's boxes come out as **one
/// run**, so the brackets a listing draws nest instead of interleaving.
///
/// The regions [`nesting`] computes are laminar — any two are disjoint or
/// nested, since a branch's arms lie wholly between its ends — so they form
/// a forest and a nested drawing is possible in principle. Getting one is
/// [`nested_order`]: the forest is scheduled level by level with each
/// region **contracted to a single unit** at its parent's level, so a
/// region is placed as a whole and its insides are ordered only against
/// each other.
///
/// A greedy "stay where you are" pass cannot do this, and the corpus's
/// biggest goal is the proof: preferring the ready box that shares the most
/// branches with the last one left a region and came back to it for 11 of
/// its 20 branches, which is what made two brackets appear to open at one
/// depth and close at another. Contraction cannot leave a region, because
/// leaving is not a move it has.
///
/// [`nested_order`] answers `None` where contracting makes a cycle — two
/// regions each feeding the other cannot both be a run — and the greedy
/// pass is what runs then. No graph in the corpus needs it; it is here
/// because "there is no contiguous order" is a real answer and a listing
/// still has to print.
fn schedule(
    graph: &Graph,
    inside: &HashMap<NodeId, BTreeSet<u32>>,
    arms: &HashMap<(NodeId, u32), bool>,
) -> Vec<NodeId> {
    let order = nested_order(graph, inside, arms).unwrap_or_else(|| wherever_ready(graph, inside));
    debug_assert_eq!(order.len(), graph.live_count(), "the graph is acyclic");
    operands_last(graph, inside, order)
}

/// A topological order in which every branch's boxes are contiguous, or
/// `None` where contracting the regions makes a cycle.
fn nested_order(
    graph: &Graph,
    inside: &HashMap<NodeId, BTreeSet<u32>>,
    arms: &HashMap<(NodeId, u32), bool>,
) -> Option<Vec<NodeId>> {
    let mut held: HashMap<u32, usize> = HashMap::new();
    for branches in inside.values() {
        for &branch in branches {
            *held.entry(branch).or_default() += 1;
        }
    }
    // A box's branches, outermost first. The family is laminar, so a box's
    // branches are a chain under containment and the bigger region is the
    // enclosing one — which makes the size the depth.
    let mut chains: HashMap<NodeId, Vec<u32>> = HashMap::new();
    for (id, _) in graph.live() {
        let mut mine: Vec<u32> = inside
            .get(&id)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect();
        mine.sort_by_key(|branch| (std::cmp::Reverse(held[branch]), *branch));
        chains.insert(id, mine);
    }
    let all: Vec<NodeId> = graph.live().map(|(id, _)| id).collect();
    let mut order = Vec::with_capacity(all.len());
    emit_level(graph, &chains, arms, &all, 0, &mut order).then_some(order)
}

/// One level of [`nested_order`]: group these boxes by the region each
/// enters next, order the groups, and recurse into every group that is one.
///
/// `false` when the groups at this level cannot be ordered — a cycle among
/// the contracted regions, which is the one thing that makes a contiguous
/// listing impossible.
fn emit_level(
    graph: &Graph,
    chains: &HashMap<NodeId, Vec<u32>>,
    arms: &HashMap<(NodeId, u32), bool>,
    members: &[NodeId],
    depth: usize,
    order: &mut Vec<NodeId>,
) -> bool {
    // A unit is one child region, or one box that enters none.
    let mut units: Vec<(Option<u32>, Vec<NodeId>)> = Vec::new();
    let mut which: HashMap<u32, usize> = HashMap::new();
    for &id in members {
        match chains[&id].get(depth).copied() {
            Some(branch) => {
                let at = *which.entry(branch).or_insert_with(|| {
                    units.push((Some(branch), Vec::new()));
                    units.len() - 1
                });
                units[at].1.push(id);
            }
            None => units.push((None, vec![id])),
        }
    }
    let mut unit_of: HashMap<NodeId, usize> = HashMap::new();
    for (at, (_, held)) in units.iter().enumerate() {
        for &id in held {
            unit_of.insert(id, at);
        }
    }
    // Contracted edges: a link between two units is a link between the
    // regions. Links leaving this level are the parent's business.
    let mut ahead: Vec<HashSet<usize>> = vec![HashSet::new(); units.len()];
    let mut unmet = vec![0usize; units.len()];
    for (at, (_, held)) in units.iter().enumerate() {
        for &id in held {
            for port in 0..graph.kind(id).arity().outputs {
                for &sink in graph.sinks(Source::Port { node: id, port }) {
                    if let Sink::Port { node, .. } = sink
                        && let Some(&to) = unit_of.get(&node)
                        && to != at
                        && ahead[at].insert(to)
                    {
                        unmet[to] += 1;
                    }
                }
            }
        }
    }
    // Ties by the least id a unit holds, so the order is a fact about the
    // graph rather than about the hashing.
    let least: Vec<usize> = units
        .iter()
        .map(|(_, held)| {
            held.iter()
                .map(|id| id.index())
                .min()
                .expect("a unit holds a box")
        })
        .collect();
    let mut ready: Vec<usize> = (0..units.len()).filter(|&at| unmet[at] == 0).collect();
    let mut placed = 0;
    while !ready.is_empty() {
        let pick = ready
            .iter()
            .enumerate()
            .min_by_key(|(_, at)| least[**at])
            .map(|(i, _)| i)
            .expect("the list is not empty");
        let at = ready.swap_remove(pick);
        placed += 1;
        if let Some(branch) = units[at].0 {
            let held = std::mem::take(&mut units[at].1);
            // The then side, then the else side: the two are backward
            // reaches from disjoint blocks, so no link crosses between them
            // and either order is topological. Which one the listing wants
            // is the one a reader reads — `if`, then arm, `else`, else arm.
            let (yes, no): (Vec<NodeId>, Vec<NodeId>) = held
                .iter()
                .partition(|id| arms.get(&(**id, branch)).copied().unwrap_or(true));
            for side in [yes, no] {
                if !side.is_empty() && !emit_level(graph, chains, arms, &side, depth + 1, order) {
                    return false;
                }
            }
            units[at].1 = held;
        } else {
            order.push(units[at].1[0]);
        }
        for &to in &ahead[at] {
            unmet[to] -= 1;
            if unmet[to] == 0 {
                ready.push(to);
            }
        }
    }
    placed == units.len()
}

/// The fallback: of the boxes that are ready, take one sharing the most
/// enclosing branches with the box just placed, deeper before shallower,
/// lower id last.
///
/// This was the schedule, and it is kept for the one case
/// [`nested_order`] declines. Any order it produces is valid — the choice
/// is only among boxes whose sources are all already placed — so what it
/// trades is legibility and nothing else.
fn wherever_ready(graph: &Graph, inside: &HashMap<NodeId, BTreeSet<u32>>) -> Vec<NodeId> {
    let mut unmet: HashMap<NodeId, usize> = graph
        .live()
        .map(|(id, _)| {
            let count = graph
                .sources(id)
                .iter()
                .filter(|source| matches!(source, Source::Port { .. }))
                .count();
            (id, count)
        })
        .collect();
    let mut ready: Vec<NodeId> = unmet
        .iter()
        .filter(|&(_, &n)| n == 0)
        .map(|(&id, _)| id)
        .collect();
    let nowhere = BTreeSet::new();
    let mut here: BTreeSet<u32> = BTreeSet::new();
    let mut order = Vec::with_capacity(ready.len());
    while !ready.is_empty() {
        let pick = ready
            .iter()
            .enumerate()
            .max_by_key(|(_, id)| {
                let mine = inside.get(id).unwrap_or(&nowhere);
                (
                    mine.intersection(&here).count(),
                    mine.len(),
                    std::cmp::Reverse(id.index()),
                )
            })
            .map(|(i, _)| i)
            .expect("the list is not empty");
        let id = ready.swap_remove(pick);
        here = inside.get(&id).unwrap_or(&nowhere).clone();
        order.push(id);
        for port in 0..graph.kind(id).arity().outputs {
            for &sink in graph.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink {
                    let left = unmet.get_mut(&node).expect("a live reader");
                    *left -= 1;
                    if *left == 0 {
                        ready.push(node);
                    }
                }
            }
        }
    }
    debug_assert_eq!(order.len(), unmet.len(), "the graph is acyclic");
    order
}

/// Moves each box that reads nothing to just before the first box that
/// reads it — but never **into** a branch it is not part of.
///
/// Such a box is ready before everything, so any schedule is free to emit
/// the whole constant pool first — and then an `equal`'s operand is forty
/// lines from the `equal`. It is equally free to emit it immediately before
/// its first reader, which is where the term spells it (`push X ; equal`)
/// and where a reader looks.
///
/// The caveat is the whole difference between this and the obvious version.
/// A literal several arms share belongs to no branch — [`nesting`] gives it
/// the *intersection* of its readers', which is empty — so dropping it in
/// front of a reader that is inside one puts a box of no branch inside a
/// branch, and the run [`schedule`] worked to make contiguous is broken by
/// the pass that runs after it. So the box backs out first: it lands just
/// before the outermost branch its reader is in and it is not, which is
/// where the term would spell it too.
fn operands_last(
    graph: &Graph,
    inside: &HashMap<NodeId, BTreeSet<u32>>,
    order: Vec<NodeId>,
) -> Vec<NodeId> {
    let floating: HashSet<NodeId> = order
        .iter()
        .copied()
        .filter(|&id| graph.sources(id).is_empty())
        .collect();
    let solid: Vec<NodeId> = order
        .iter()
        .copied()
        .filter(|id| !floating.contains(id))
        .collect();
    let at: HashMap<NodeId, usize> = solid.iter().enumerate().map(|(i, &id)| (id, i)).collect();

    // Where each branch's run begins, the ends of the branch included: they
    // are the bracket lines, and a box between them reads as inside.
    let mut opens: HashMap<u32, usize> = HashMap::new();
    for (i, &id) in solid.iter().enumerate() {
        let mut branches: BTreeSet<u32> = inside.get(&id).cloned().unwrap_or_default();
        if let NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } = graph.kind(id) {
            branches.insert(branch.index() as u32);
        }
        for branch in branches {
            opens.entry(branch).or_insert(i);
        }
    }

    // One insertion point per floating box: before its first reader, backed
    // out of every branch that reader is in and it is not.
    let mut lands: HashMap<usize, Vec<NodeId>> = HashMap::new();
    let mut tail: Vec<NodeId> = Vec::new();
    for &id in &order {
        if !floating.contains(&id) {
            continue;
        }
        let mut first = None;
        for port in 0..graph.kind(id).arity().outputs {
            for &sink in graph.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink
                    && let Some(&i) = at.get(&node)
                {
                    first = Some(first.map_or(i, |was: usize| was.min(i)));
                }
            }
        }
        // A constant the boundary reads, or one nothing reads at all, still
        // has to appear: a listing that drops a live box is lying.
        let Some(first) = first else {
            tail.push(id);
            continue;
        };
        let mine = inside.get(&id).cloned().unwrap_or_default();
        let landing = inside
            .get(&solid[first])
            .into_iter()
            .flatten()
            .filter(|branch| !mine.contains(branch))
            .filter_map(|branch| opens.get(branch).copied())
            .min()
            .unwrap_or(first)
            .min(first);
        lands.entry(landing).or_default().push(id);
    }

    let mut moved = Vec::with_capacity(order.len());
    for (i, &id) in solid.iter().enumerate() {
        moved.extend(lands.get(&i).map(Vec::as_slice).unwrap_or_default());
        moved.push(id);
    }
    moved.extend(tail);
    debug_assert_eq!(moved.len(), order.len(), "every box is still listed");
    moved
}

/// The first source at or above `source` that survives elision.
///
/// An `id` passes port `i` through, and a `copy(n)` is block-wise, so its
/// outputs `i` and `n + i` both stand for its input `i`. The walk is bounded
/// by the graph's size rather than trusted to terminate: this runs on the
/// failure path, where a graph that should be acyclic may be the very thing
/// that is wrong.
fn resolve(graph: &Graph, source: Source) -> Source {
    let mut source = source;
    for _ in 0..=graph.live_count() {
        let Source::Port { node, port } = source else {
            return source;
        };
        source = match graph.kind(node) {
            NodeKind::Id(_) => graph.sources(node)[port],
            NodeKind::Copy(n) => graph.sources(node)[port % n],
            _ => return source,
        };
    }
    source
}

/// Every reader of `source` that survives elision, looking through the
/// boxes that do not.
fn readers(graph: &Graph, source: Source, found: &mut Vec<Sink>, seen: &mut HashSet<Sink>) {
    for &sink in graph.sinks(source) {
        if !seen.insert(sink) {
            continue;
        }
        match sink {
            Sink::Port { node, .. } if structural(graph.kind(node)) => {
                for port in 0..graph.kind(node).arity().outputs {
                    readers(graph, Source::Port { node, port }, found, seen);
                }
            }
            _ => found.push(sink),
        }
    }
}

/// How the census names a box: the kind without its width or its literal, so
/// that `push 1` and `push true` count together as `push`.
fn census_name(kind: &NodeKind) -> String {
    match kind {
        NodeKind::Id(_) => "id".to_string(),
        NodeKind::Copy(_) => "copy".to_string(),
        NodeKind::Drop(_) => "drop".to_string(),
        NodeKind::Call { .. } => "call".to_string(),
        NodeKind::Fork { .. } | NodeKind::Select { .. } => "branch".to_string(),
        NodeKind::Op(prim) => {
            let spelled = prim.to_string();
            spelled
                .split_whitespace()
                .next()
                .unwrap_or("op")
                .to_string()
        }
    }
}

/// How wide the kind column is before a label is cut short.
const LABEL: usize = 44;

impl fmt::Display for Listing<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let graph = self.graph;
        let inside = nesting(graph);
        let arms = arms(graph, &inside);
        let order = schedule(graph, &inside, &arms);
        let shown = |id: NodeId| !self.elide || !structural(graph.kind(id));

        // A box's branches, outermost first: the chain it is nested in, and
        // so the depth it and each of its brackets are drawn at.
        let mut held: HashMap<u32, usize> = HashMap::new();
        for branches in inside.values() {
            for &branch in branches {
                *held.entry(branch).or_default() += 1;
            }
        }
        let chain = |id: NodeId| -> Vec<u32> {
            let mut mine: Vec<u32> = inside
                .get(&id)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect();
            mine.sort_by_key(|branch| (std::cmp::Reverse(held.get(branch).copied()), *branch));
            mine
        };
        // What each branch decides on, named the way every other wire in
        // the listing is named — so `if #12.0` and the `#12` line above are
        // plainly the same wire.
        let condition: HashMap<u32, String> = graph
            .live()
            .filter_map(|(id, kind)| match kind {
                NodeKind::Select { branch, .. } => {
                    let source = *graph.sources(id).first()?;
                    let source = if self.elide {
                        resolve(graph, source)
                    } else {
                        source
                    };
                    Some((branch.index() as u32, source.to_string()))
                }
                _ => None,
            })
            .collect();
        let gutter = |depth: usize| "| ".repeat(depth);
        // A branch whose else arm owns boxes needs an `else` to say where
        // they start. One whose else arm owns none does not: the `endif`
        // names both blocks, and a separator with nothing after it is a
        // line that says only that the listing draws separators.
        let parts: HashSet<u32> = arms
            .iter()
            .filter(|(_, then)| !**then)
            .map(|(&(_, branch), _)| branch)
            .collect();

        let mut opened: HashSet<u32> = HashSet::new();
        let mut parted: HashSet<u32> = HashSet::new();

        let mut census: BTreeMap<String, usize> = BTreeMap::new();
        for (id, kind) in graph.live() {
            if shown(id) && !matches!(kind, NodeKind::Fork { .. } | NodeKind::Select { .. }) {
                *census.entry(census_name(kind)).or_default() += 1;
            }
        }
        let mut census: Vec<(String, usize)> = census.into_iter().collect();
        census.sort_by_key(|(name, n)| (std::cmp::Reverse(*n), name.clone()));
        let census: Vec<String> = census
            .iter()
            .take(8)
            .map(|(name, n)| format!("{}×{}", n, name))
            .collect();

        // Counted by the select: every branch has one, and a branch whose
        // arms read nothing off the stack has no fork to count.
        let branches = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
            .count();
        let boxes = order.iter().filter(|&&id| shown(id)).count();
        let arity = graph.arity();
        writeln!(
            f,
            "{}  {} box{}  {} branch{}  {} in → {} out{}",
            self.tag,
            boxes,
            if boxes == 1 { "" } else { "es" },
            branches,
            if branches == 1 { "" } else { "es" },
            arity.inputs,
            arity.outputs,
            match graph.live_count() - boxes {
                0 => String::new(),
                hidden => format!("   ({} id/copy read through)", hidden),
            },
        )?;
        if !census.is_empty() {
            writeln!(f, "      {}", census.join("  "))?;
        }
        writeln!(f)?;

        for &id in &order {
            if !shown(id) {
                continue;
            }
            let kind = graph.kind(id);
            let mine = chain(id);
            // The lines a reader needs before this one. A branch opens at
            // its `fork` where it has one, so what is left to draw here is
            // the opening of a forkless branch and every `else` — neither
            // of which is a box, which is what the empty id column says.
            //
            // Each of them sits at the depth of the branch it belongs to,
            // and that is its place in this box's chain: the box is drawn
            // at `mine.len()`, and a branch `mine[k]` holds it from `k`.
            let ends = match kind {
                NodeKind::Fork { branch, .. } | NodeKind::Select { branch, .. } => {
                    Some(branch.index() as u32)
                }
                _ => None,
            };
            let mut ahead: Vec<(&str, u32, usize)> = Vec::new();
            for (depth, &branch) in mine.iter().enumerate() {
                if !opened.contains(&branch) {
                    ahead.push(("if", branch, depth));
                }
                let then = arms.get(&(id, branch)).copied().unwrap_or(true);
                if !then && parts.contains(&branch) && !parted.contains(&branch) {
                    ahead.push(("else", branch, depth));
                }
            }
            // A `select` closes its branch, so anything that branch still
            // owes — an opening it never got because it has no fork and no
            // box of its own, an `else` its else arm was too empty to
            // trigger — is owed here, at the select's own depth. A
            // branch's ends are not inside it, so that is `mine.len()`.
            if let (Some(branch), NodeKind::Select { .. }) = (ends, kind)
                && !opened.contains(&branch)
            {
                ahead.push(("if", branch, mine.len()));
            }
            for (word, branch, depth) in ahead {
                writeln!(
                    f,
                    "  {:<5} {}{} {}",
                    "",
                    gutter(depth),
                    word,
                    condition.get(&branch).map_or("?", String::as_str)
                )?;
                match word {
                    "if" => opened.insert(branch),
                    _ => parted.insert(branch),
                };
            }
            let indent = gutter(mine.len());
            let label = match kind {
                // The two ends of a branch are the block it opens and the
                // block it closes: what a reader wants from them is where
                // the arms begin and end, and `if`/`endif` is how a reader
                // already knows how to read that.
                NodeKind::Fork { .. } | NodeKind::Select { .. } => {
                    let word = if matches!(kind, NodeKind::Fork { .. }) {
                        "if"
                    } else {
                        "endif"
                    };
                    if matches!(kind, NodeKind::Fork { .. })
                        && let Some(branch) = ends
                    {
                        opened.insert(branch);
                    }
                    format!(
                        "{}{} {}",
                        indent,
                        word,
                        ends.and_then(|branch| condition.get(&branch))
                            .map_or("?", String::as_str)
                    )
                }
                other => format!("{}{}", indent, other),
            };
            let label = match label.char_indices().nth(LABEL - 1) {
                Some((cut, _)) => format!("{}…", &label[..cut]),
                None => label,
            };

            let sources: Vec<String> = graph
                .sources(id)
                .iter()
                .map(|&source| {
                    let source = if self.elide {
                        resolve(graph, source)
                    } else {
                        source
                    };
                    source.to_string()
                })
                .collect();
            // Both ends of a branch read the condition at port 0, and the
            // label has already said so — a rule anchored at either end
            // names the same wire — so what is left for this column is
            // what the box does with the rest: the stack a fork hands out,
            // and the two blocks a select chooses between.
            let reads = match kind {
                NodeKind::Fork { .. } if sources.len() > 1 => {
                    format!("on {}", sources[1..].join(" "))
                }
                NodeKind::Select { arity, .. } if sources.len() > 1 => format!(
                    "then {}  else {}",
                    sources[1..=*arity].join(" "),
                    sources[1 + arity..].join(" ")
                ),
                NodeKind::Fork { .. } | NodeKind::Select { .. } => String::new(),
                _ if sources.is_empty() => String::new(),
                _ => format!("← {}", sources.join(" ")),
            };

            let mut sinks = Vec::new();
            let mut seen = HashSet::new();
            for port in 0..kind.arity().outputs {
                let source = Source::Port { node: id, port };
                if self.elide {
                    readers(graph, source, &mut sinks, &mut seen);
                } else {
                    sinks.extend(graph.sinks(source).iter().copied());
                }
            }
            let mut read_by: Vec<String> = sinks
                .iter()
                .map(|sink| match sink {
                    Sink::Output(i) => format!("out{}", i),
                    Sink::Port { node, .. } => node.to_string(),
                })
                .collect();
            read_by.dedup();
            let read_by = match read_by.is_empty() {
                true => "  ·  nothing reads it".to_string(),
                false => format!("  → {}", read_by.join(" ")),
            };

            writeln!(
                f,
                "  {:<5} {:<width$}{:<24}{}",
                id.to_string(),
                label,
                reads,
                read_by,
                width = LABEL + 1
            )?;
        }

        let outputs: Vec<String> = graph
            .outputs()
            .iter()
            .map(|&source| {
                let source = if self.elide {
                    resolve(graph, source)
                } else {
                    source
                };
                source.to_string()
            })
            .collect();
        match outputs.is_empty() {
            true => writeln!(f, "\n  out   ()"),
            false => writeln!(f, "\n  out   ← {}", outputs.join(" ")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::{build, tests::term_of};
    use crate::term::Context;

    /// The graph a body builds, and the arena its term lives in.
    pub(super) fn built(body: &str) -> Graph {
        let mut terms = Context::new();
        let term = term_of(&mut terms, body);
        let graph = build(&terms, term);
        graph.check().unwrap_or_else(|e| panic!("{}", e));
        graph
    }

    #[test]
    fn a_listing_names_every_box_it_shows() {
        let graph = built("push 1 push 2 add");
        let text = listing(&graph, "left").all_boxes().to_string();
        for (id, _) in graph.live() {
            assert!(
                text.contains(&format!("  {} ", id)),
                "{} is missing from\n{}",
                id,
                text
            );
        }
    }

    /// Reading through `id` and `copy` hides boxes and nothing else: what is
    /// left still says where every value it names comes from.
    #[test]
    fn reading_through_structure_hides_only_structure() {
        let graph = built("pick 0 add");
        let lean = listing(&graph, "left").to_string();
        let full = listing(&graph, "left").all_boxes().to_string();
        let structure = graph.live().filter(|(_, kind)| structural(kind)).count();
        assert!(structure > 0, "the body was chosen to have some");
        assert_eq!(
            full.lines().count() - lean.lines().count(),
            structure,
            "one line per hidden box, and no other difference in size"
        );
        assert!(lean.contains("id/copy read through"));
    }

    /// The listing shows every live box when nothing is elided — a report
    /// that quietly drops one is worse than a long one.
    #[test]
    fn nothing_live_goes_unlisted() {
        let graph = built("push 1 pick 0 swap drop 0");
        let text = listing(&graph, "left").all_boxes().to_string();
        let listed = text.lines().filter(|line| line.starts_with("  #")).count();
        assert_eq!(listed, graph.live_count());
    }

    /// An arm indents under the branch it belongs to, and the two ends draw
    /// the bracket.
    #[test]
    fn an_arm_reads_as_an_arm() {
        let graph = built("branch { push 1 } { push 2 }");
        let text = listing(&graph, "left").to_string();
        // A branch reads as the block it is: the condition named on all
        // three lines, an arm indented under each, and the `endif` naming
        // the two blocks it chooses between.
        for want in ["if in0", "else in0", "endif in0", "| push 1", "| push 2"] {
            assert!(text.contains(want), "no `{}` in\n{}", want, text);
        }
        // The arms come out in the order a reader reads them.
        let lines: Vec<&str> = text.lines().collect();
        let at = |want: &str| {
            lines
                .iter()
                .position(|line| line.contains(want))
                .unwrap_or_else(|| panic!("no `{}` in\n{}", want, text))
        };
        assert!(at("if in0") < at("| push 1"), "\n{}", text);
        assert!(at("| push 1") < at("else in0"), "\n{}", text);
        assert!(at("else in0") < at("| push 2"), "\n{}", text);
        assert!(at("| push 2") < at("endif in0"), "\n{}", text);
        // The opening has no box behind it — this branch has no fork —
        // and the empty id column is how the listing says so.
        assert!(
            lines[at("if in0")].starts_with("        "),
            "a forkless opening names a box:\n{}",
            text
        );
    }

    /// A constant sits with the box that reads it, not in a slab at the top.
    #[test]
    fn an_operand_sits_by_its_reader() {
        let graph = built("push 1 push 2 add push 3 add");
        let text = listing(&graph, "left").to_string();
        let rows: Vec<&str> = text
            .lines()
            .filter(|line| line.starts_with("  #"))
            .collect();
        let last_push = rows
            .iter()
            .rposition(|line| line.contains("push"))
            .expect("there are pushes");
        let first_add = rows
            .iter()
            .position(|line| line.contains("add"))
            .expect("there are adds");
        assert!(
            last_push > first_add,
            "every constant was hoisted above the work in\n{}",
            text
        );
    }

    /// The schedule is topological: nothing is listed before something it
    /// reads.
    #[test]
    fn a_box_is_listed_after_what_it_reads() {
        let graph = built("push 1 pick 0 add branch { push 3 } { push 4 }");
        let inside = nesting(&graph);
        let order = schedule(&graph, &inside, &arms(&graph, &inside));
        let mut placed: HashSet<NodeId> = HashSet::new();
        for id in order {
            for &source in graph.sources(id) {
                if let Source::Port { node, .. } = source {
                    assert!(placed.contains(&node), "{} is listed before {}", id, node);
                }
            }
            placed.insert(id);
        }
    }

    /// The invariant the whole listing rests on: a branch's boxes are one
    /// run, so the brackets nest instead of interleaving.
    ///
    /// Checked three ways over goals with branches inside branches — the
    /// order is topological, every region is contiguous, and the drawn
    /// brackets balance — because each catches a different way of getting
    /// it wrong, and the third is what a reader actually sees.
    #[test]
    fn a_branch_is_one_run_and_its_brackets_nest() {
        let bodies = [
            "branch { branch { push 1 } { push 2 } } { drop 0 push 3 }",
            "pick 0 is_tuple 2 branch { untuple 2 is_symbol swap drop 0 } { drop 0 push false }",
            "pick 0 push 1 equal branch { pick 0 is_bool branch { not } { negate } } { negate }",
            "push 1 pick 1 branch { add } { add }",
        ];
        let mut ever_nested = false;
        for body in bodies {
            let graph = built(body);
            let inside = nesting(&graph);
            let order = schedule(&graph, &inside, &arms(&graph, &inside));
            ever_nested |= inside.values().any(|mine| mine.len() > 1);

            assert_eq!(order.len(), graph.live_count(), "{}: every box once", body);
            let mut placed: HashSet<NodeId> = HashSet::new();
            for &id in &order {
                for &source in graph.sources(id) {
                    if let Source::Port { node, .. } = source {
                        assert!(placed.contains(&node), "{}: {} before {}", body, id, node);
                    }
                }
                placed.insert(id);
            }

            // Contiguous: between a region's first and last box sits
            // nothing that is not the region's, its own ends aside.
            let mut region: HashMap<u32, HashSet<NodeId>> = HashMap::new();
            for (&id, branches) in &inside {
                for &branch in branches {
                    region.entry(branch).or_default().insert(id);
                }
            }
            let at: HashMap<NodeId, usize> =
                order.iter().enumerate().map(|(i, &id)| (id, i)).collect();
            for (branch, held) in &region {
                let lo = held.iter().map(|id| at[id]).min().expect("a box");
                let hi = held.iter().map(|id| at[id]).max().expect("a box");
                for &id in &order[lo..=hi] {
                    let ends = matches!(graph.kind(id),
                        NodeKind::Fork { branch: b, .. } | NodeKind::Select { branch: b, .. }
                            if b.index() as u32 == *branch);
                    assert!(
                        held.contains(&id) || ends,
                        "{}: {} sits inside branch #{}, which is not its own:\n{}",
                        body,
                        id,
                        branch,
                        listing(&graph, "left").all_boxes()
                    );
                }
            }

            // And the drawing balances: every `if` reaches an `endif` at
            // the depth it opened, innermost first, with any `else` in
            // between at that same depth.
            let text = listing(&graph, "left").all_boxes().to_string();
            let mut stack: Vec<(String, usize)> = Vec::new();
            let mut blocks = 0;
            for line in text.lines() {
                // Past the id column is the gutter, and past that the word.
                let Some(rest) = line.get(8..) else { continue };
                let depth = rest.matches("| ").count();
                let word = rest.trim_start_matches("| ");
                let condition = |word: &str| {
                    word.split_whitespace()
                        .nth(1)
                        .expect("a block names its condition")
                        .to_string()
                };
                if word.starts_with("if ") {
                    blocks += 1;
                    stack.push((condition(word), depth));
                } else if word.starts_with("else ") {
                    assert_eq!(
                        stack.last(),
                        Some(&(condition(word), depth)),
                        "{}: an `else` outside the block it parts:\n{}",
                        body,
                        text
                    );
                } else if word.starts_with("endif ") {
                    assert_eq!(
                        stack.pop(),
                        Some((condition(word), depth)),
                        "{}: an `endif` out of turn:\n{}",
                        body,
                        text
                    );
                }
            }
            assert!(
                stack.is_empty(),
                "{}: a block never closes:\n{}",
                body,
                text
            );
            assert_eq!(
                blocks,
                graph
                    .live()
                    .filter(|(_, kind)| matches!(kind, NodeKind::Select { .. }))
                    .count(),
                "{}: a branch got no block, or got two:\n{}",
                body,
                text
            );
        }
        assert!(
            ever_nested,
            "the bodies must actually nest, or this proves nothing"
        );
    }
}
