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
//! ## What makes 351 boxes legible
//!
//! Four decisions, and the listing is a wall without any of them.
//!
//! **Branch membership is computed.** A node is inside a branch when it is
//! downstream of the [`Fork`](super::NodeKind::Fork) and upstream of the
//! [`Select`](super::NodeKind::Select) it is paired with — a forward reach
//! and a backward reach, intersected. So the indentation is a fact about the
//! graph rather than a guess from what happens to sit between two lines, and
//! an arm that reaches out of itself still reads as an arm.
//!
//! **The order stays inside a branch once it enters one.** The schedule
//! [`read_back`](super::read_back) uses is min-id-first, which is
//! topological and nothing else: it hoists the constants an arm pushes out
//! of the arm, and the arm stops reading as a unit. Of the boxes that are
//! ready, this takes one that shares the most enclosing branches with the
//! box just placed.
//!
//! **A box that reads nothing sits just before the box that reads it.** A
//! `push` is ready before everything, so left alone the whole constant pool
//! lands in one slab at the top and an `equal`'s operand is forty lines from
//! the `equal`. Every topological order may put such a box anywhere before
//! its first reader, so it goes immediately before.
//!
//! **`id` and `copy` are read through.** They are what the structural laws
//! delete, and a `copy` says what the links already say — a value read
//! twice. On the corpus's biggest goal that is 156 boxes of 351. They are
//! still there and [`Listing::all_boxes`] shows them, because a proof about
//! a `copy` needs to see it.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

use super::{Graph, NodeId, NodeKind, Sink, Source};

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

/// A topological order that stays inside a branch once it enters one.
///
/// Of the boxes that are ready, this takes one sharing the most enclosing
/// branches with the box just placed, deeper before shallower, lower id
/// last. Any order it produces is a valid schedule — the choice is only
/// among boxes whose sources are all already placed — so this trades
/// nothing but which valid order gets printed.
fn schedule(graph: &Graph, inside: &HashMap<NodeId, BTreeSet<u32>>) -> Vec<NodeId> {
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
    operands_last(graph, order)
}

/// Moves each box that reads nothing to just before the first box that
/// reads it.
///
/// Such a box is ready before everything, so any schedule is free to emit
/// the whole constant pool first — and then an `equal`'s operand is forty
/// lines from the `equal`. It is equally free to emit it immediately before
/// its first reader, which is where the term spells it (`push X ; equal`)
/// and where a reader looks.
fn operands_last(graph: &Graph, order: Vec<NodeId>) -> Vec<NodeId> {
    let floating: HashSet<NodeId> = order
        .iter()
        .copied()
        .filter(|&id| graph.sources(id).is_empty())
        .collect();
    let mut feeds: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for &id in &floating {
        for port in 0..graph.kind(id).arity().outputs {
            for &sink in graph.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink {
                    feeds.entry(node).or_default().push(id);
                }
            }
        }
    }
    let mut placed: HashSet<NodeId> = HashSet::new();
    let mut moved = Vec::with_capacity(order.len());
    for &id in &order {
        if floating.contains(&id) {
            continue;
        }
        for &operand in feeds.get(&id).map(Vec::as_slice).unwrap_or_default() {
            if placed.insert(operand) {
                moved.push(operand);
            }
        }
        moved.push(id);
    }
    // A constant the boundary reads, or one nothing reads at all, still has
    // to appear: a listing that drops a live box is lying.
    for &id in &order {
        if floating.contains(&id) && placed.insert(id) {
            moved.push(id);
        }
    }
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
        let order = schedule(graph, &inside);
        let shown = |id: NodeId| !self.elide || !structural(graph.kind(id));

        // A branch with no fork has no box to draw its opening bracket, so
        // the listing draws one itself — with an empty id column, which is
        // how it says the line is a bracket rather than a box. Bigger region
        // first, so nested ones open outermost first.
        let forkless: BTreeMap<u32, usize> = {
            let mut held: BTreeMap<u32, usize> = BTreeMap::new();
            for branches in inside.values() {
                for &branch in branches {
                    *held.entry(branch).or_default() += 1;
                }
            }
            let forked: HashSet<u32> = graph
                .live()
                .filter_map(|(_, kind)| match kind {
                    NodeKind::Fork { branch, .. } => Some(branch.index() as u32),
                    _ => None,
                })
                .collect();
            held.into_iter()
                .filter(|(branch, _)| !forked.contains(branch))
                .collect()
        };
        let mut opened: HashSet<u32> = HashSet::new();

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
            let mine = inside.get(&id).cloned().unwrap_or_default();
            let mut waiting: Vec<u32> = mine
                .iter()
                .copied()
                .filter(|branch| forkless.contains_key(branch) && !opened.contains(branch))
                .collect();
            waiting.sort_by_key(|branch| std::cmp::Reverse(forkless[branch]));
            for branch in waiting {
                let depth = mine.iter().filter(|b| opened.contains(b)).count();
                writeln!(
                    f,
                    "  {:<5} {}┌─ branch #{}  (no fork: the arms read nothing)",
                    "",
                    "│  ".repeat(depth),
                    branch
                )?;
                opened.insert(branch);
            }
            let indent = "│  ".repeat(mine.len());
            let label = match kind {
                // The two ends of a branch are brackets, not boxes: what a
                // reader wants from them is where the arms begin and end.
                NodeKind::Fork { branch, .. } => format!("{}┌─ branch {}  ?", indent, branch),
                NodeKind::Select { branch, .. } => format!("{}└─ branch {}  ⇒", indent, branch),
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
            // Both ends of a branch read the condition at port 0, and
            // saying so apart from the stack is the whole reason it is
            // there: a rule anchored at either end names the same wire.
            let reads = match kind {
                NodeKind::Fork { .. } | NodeKind::Select { .. } if !sources.is_empty() => {
                    format!("if {}  on {}", sources[0], sources[1..].join(" "))
                }
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
    fn built(body: &str) -> Graph {
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
        assert!(
            text.contains("┌─ branch"),
            "no opening bracket in\n{}",
            text
        );
        assert!(
            text.contains("└─ branch"),
            "no closing bracket in\n{}",
            text
        );
        assert!(
            text.lines().any(|line| line.contains("│  push")),
            "no arm indented under its branch in\n{}",
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
        let order = schedule(&graph, &inside);
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
}
