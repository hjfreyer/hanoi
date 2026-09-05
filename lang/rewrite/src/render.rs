//! A graph written for someone reading a proof.
//!
//! [`Display for Graph`](crate::kernel::graph::Graph) is the other listing, and it is for a
//! different reader: it dumps the links in id order so that a broken one can
//! be found, which is what [`Graph::check`](crate::kernel::graph::Graph::check) wants when
//! it panics. This one is for a goal that did not close. It says the same
//! facts and orders them so a person can follow the program, which is a
//! different job and is worth its own code.
//!
//! A **listing of instructions** is the wrong shape for the report twice
//! over. A graph is a DAG and a program text is a spine, so anything
//! writing one has to reimpose a stack and pay for it in routing; and an
//! instruction has no name for the value it computed, so
//! two consecutive steps of a proof cannot be compared. An [`Address`] is
//! a box's name in every graph that computes it — a box is named by what
//! it computes, and nothing edits one — so a listing keyed by one is a
//! diff, and "31 boxes went, the branches are gone" is a sentence about
//! what a tactic did.
//!
//! ## A name, and how much of it to write
//!
//! An address is twelve letters and nobody writes twelve. Every line
//! carries the whole of its box's address with the **shortest prefix no
//! other box on the page shares** emphasised, and every reference to a
//! box — what it reads, what reads it, what a branch turns on — carries
//! just that prefix. So what is bold on a line is exactly what the rest
//! of the page calls that box, and exactly what `at(#nkz, fold)` is
//! written with. The debt is Jujutsu's, whose change ids are read this
//! way for the same reason.
//!
//! The emphasis is an escape sequence, so it is off unless whoever
//! prints the listing says otherwise ([`Listing::bold`]) — one goes into
//! an assertion and a piped log as often as it goes to a terminal.
//!
//! So this is the only reading of a stuck goal, and the one a proof's next
//! step is written off: `at(#nkz, fold)` names the box the listing named.
//!
//! ## A branch is a block
//!
//! A `select` is not a box a reader wants to see as a box. What they want
//! is where the arms begin and end, and every reader of code already knows
//! how to read that:
//!
//! ```text
//!                   if in0
//!   #nyoqvutuxsru   | push 1                        → #k
//!   #kzmrpklnynyw   | add       ← in0 #n.0          → #m
//!                   else in0
//!   #lwyywqnqtorp   | negate    ← in0               → #m
//!   #msowwltslwoo   endif in0   then #k.0 else #l.0 → out0
//! ```
//!
//! The condition is named on all three lines, so a block deep in a nest
//! says which wire it turns on without a reader counting bars. The `endif`
//! is the [`Select`](crate::kernel::graph::NodeKind::Select), so it keeps its name and
//! its links: the right-hand columns still say what the box reads and who
//! reads it, which is what a next proof step names. The `if` and the
//! `else` are lines the listing draws rather than boxes, and their
//! **empty name column** is how a reader tells the two apart.
//!
//! ## A branch is several boxes, and one bracket
//!
//! A [`Select`](crate::kernel::graph::NodeKind::Select) carries one answer, so a source
//! `branch` leaving `n` values is `n` of them reading one condition. A
//! reader wants the one bracket back, and [`grouping`] is where it comes
//! from: peers on one condition are one branch, and one `if` is closed by
//! a **run** of `endif`s, one per answer, each keeping its own address and
//! its own links.
//!
//! ```text
//!                   if in0
//!   #nyoqvutuxsru   | push 1                            → #k
//!   #vknouovwoons   | push 3                            → #z
//!                   else in0
//!   #rrnxuzuvsypt   | push 2                            → #k
//!   #mlrnzlorovlz   | push 4                            → #z
//!   #kqstmypnlprv   endif in0  then #n.0  else #r.0     → out0
//!   #znuqoyxmrslm   endif in0  then #v.0  else #m.0     → out1
//! ```
//!
//! Only peers at one **depth** group. The regions have to stay laminar for
//! [`schedule`] to nest them, and a peer inside some other branch that its
//! fellow is outside of would make a bracket that straddles rather than
//! nests — so the grouping key is the condition and where the select sits,
//! and two selects on one wire at different depths are two brackets, which
//! is what a nested retest should look like anyway.
//!
//! The grouping is not only about brackets. [`arms_of`] asked per select
//! would find work an arm does for two of its answers shared between two
//! regions and give it to neither, which would lift it out of the arm; it
//! is asked of the whole branch, so the arms are what they were when a
//! branch was one box.
//!
//! ## What makes 351 boxes legible
//!
//! Five decisions, and the listing is a wall without any of them.
//!
//! **Branch membership is computed.** A node is inside a branch when the
//! [`Select`](crate::kernel::graph::NodeKind::Select)'s blocks reach it and nothing
//! outside the region does — a backward reach from the blocks, less what
//! also feeds the condition, shrunk until no box in it is read from
//! outside. So the indentation is a fact about the graph rather than a
//! guess from what happens to sit between two lines, and an arm that
//! reaches out of itself still reads as an arm.
//!
//! **A branch's boxes come out as one run.** A plain min-id-first schedule
//! is topological and nothing else: it hoists the constants an arm pushes
//! out of the arm, and the arm stops reading as a unit. Nor is a greedy "stay
//! where you are" enough — preferring the ready box that shares the most
//! branches with the last one *leaves* a region whenever nothing inside it
//! is ready, and comes back later, which is what makes an `if` and its
//! `endif` land at different depths. The regions are **laminar**
//! (any two disjoint or nested, since a branch's arms lie wholly between
//! its ends), so [`schedule`] contracts each to a single unit at its
//! parent's level and orders the units: a region is placed whole, and
//! leaving one is not a move the schedule has.
//!
//! **A box that reads nothing is written wherever it is read.** A `push`
//! is ready before everything, so left alone the whole constant pool
//! lands in one slab at the top and an `equal`'s operand is forty lines
//! from the `equal`. Writing it once before its *first* reader is not
//! enough either: the corpus's biggest goal has a `push false` read 23
//! times by boxes at nine different depths, and no one line can sit
//! beside all of them. So it gets a line in each arm that reads it, and
//! each line names the readers there — a `→` column 23 wide is not one a
//! reader reads.
//!
//! This is the one place the listing writes a box more than once, and it
//! is the only place it can. A box that reads nothing has no `←` column,
//! so a second line of it is the first line character for character: its
//! content **is** its identity, and two lines reading `push true` are not
//! two things a reader can confuse. A box that reads something has a
//! history, and a second copy of a history invites the question "the same
//! box?" — which is what a listing keyed by [`Address`] exists to answer.
//! A value may be written wherever it is used; a computation is written
//! once, and a **parenthesised address** is how a line says which it is.
//!
//! The sharing is still on the page: the `→` columns of a box's lines
//! partition its readers, so their union is the whole of who reads it.
//!
//! **The arms come out in the order a reader reads them.** A branch's
//! region splits in two — every box in it is upstream of one of the
//! select's two block lists — so the schedule emits the then side, then
//! the else side, and [`arms`] is the reading that says which is which.
//! A box upstream of *both* lists is upstream of neither arm, the way a
//! box two regions share is inside neither, and [`arms`] hands it back to
//! the enclosing level as it reads: a branch grown forwards over the work
//! after it reads that work's outside operands from both of its arms. An
//! `else` is drawn where the second begins, and left out where the else
//! arm owns no boxes at all: the `endif` names both blocks, and a
//! separator with nothing after it says only that the listing draws
//! separators.
//!
//! **A branch that owns no boxes still gets its block.** Its arms are
//! wholly boxes a branch around it also holds, so `nesting` gives them to
//! neither and there is no first box to hang an opening `if` on. The
//! listing draws one against the `select` itself rather than printing an
//! `endif` that closes nothing.
//!
//! **Every box the boundary reaches is on the page.** There is nothing a
//! reader would rather look through — every box is an operation, and a
//! value read twice is one box with two `→` entries rather than a box
//! saying so.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::kernel::graph::{Address, Graph, NodeId, NodeKind, Sink, Source};

/// One side of a goal, written out. Build it with [`listing`].
pub struct Listing<'g> {
    graph: &'g Graph,
    tag: &'g str,
    /// Whether the shortest unique prefix of each address is emphasised.
    bold: bool,
}

/// A graph as a listing: every box the boundary reaches, one to a line.
///
/// There is nothing a reader would rather look through — every box is an
/// operation — so there is no dial for how much of one to print.
///
/// Plain by default: the emphasis is an escape sequence, and a listing
/// goes into a test's assertion and a piped log as often as it goes to a
/// terminal. Whoever is writing to a terminal says so — `bin/prove` asks
/// the terminal itself, and takes `--color` as the answer when a reader
/// says the pipe ends at a pager.
pub fn listing<'g>(graph: &'g Graph, tag: &'g str) -> Listing<'g> {
    Listing {
        graph,
        tag,
        bold: false,
    }
}

impl<'g> Listing<'g> {
    /// Emphasise the shortest unique prefix of every address, for a reader
    /// whose terminal can show it.
    pub fn bold(self, bold: bool) -> Listing<'g> {
        Listing { bold, ..self }
    }
}

/// Where the emphasis on an address's unique prefix begins and ends.
const ON: &str = "\u{1b}[1m";
const OFF: &str = "\u{1b}[0m";

/// How wide a spelled-out address reads: the `#` and the letters. The
/// emphasis is escapes, which take no room on the page, so this is the
/// width whether or not a listing is emphasised.
const SPELLED: usize = 1 + Address::LETTERS;

/// How wide the name column is: a spelled address, and the parentheses a
/// repeated line writes one in.
const NAME: usize = SPELLED + 2;

/// Where a line's own text begins: two spaces, the name column, a space.
/// The gutter a branch indents with is measured from here.
pub(super) const MARGIN: usize = 2 + NAME + 1;

/// How a listing writes the names of boxes: the address of each, and how
/// much of it tells that box from every other on the page.
///
/// Two spellings, and the difference between them is the whole of what
/// the emphasis means. A box's **own line** carries the whole address with
/// its unique prefix marked; every **reference** to it — what a box reads,
/// what reads it, what a branch turns on — carries just that prefix. So
/// what is bold on a line is exactly what the rest of the page calls it,
/// and exactly what a proof writes in `at(#nkz, fold)`.
struct Names {
    short: HashMap<NodeId, String>,
    bold: bool,
}

impl Names {
    fn of(graph: &Graph, bold: bool) -> Names {
        Names {
            short: graph.names(),
            bold,
        }
    }

    /// A box's own line: the whole address, the telling prefix marked.
    fn spell(&self, graph: &Graph, id: NodeId) -> String {
        let letters = graph.address(id).letters();
        let cut = self.short.get(&id).map_or(letters.len(), String::len);
        match self.bold {
            true => format!("#{}{}{}{}", ON, &letters[..cut], OFF, &letters[cut..]),
            false => format!("#{}", letters),
        }
    }

    /// A reference to a box: as much of its address as tells it apart.
    fn refer(&self, graph: &Graph, id: NodeId) -> String {
        match self.short.get(&id) {
            Some(prefix) => format!("#{}", prefix),
            None => graph.address(id).to_string(),
        }
    }

    /// What an input port reads, or a boundary input.
    fn source(&self, graph: &Graph, source: Source) -> String {
        match source {
            Source::Input(i) => format!("in{}", i),
            Source::Port { node, port } => format!("{}.{}", self.refer(graph, node), port),
        }
    }

    /// What reads an output port, or a boundary output.
    fn sink(&self, graph: &Graph, sink: Sink) -> String {
        match sink {
            Sink::Output(i) => format!("out{}", i),
            Sink::Port { node, .. } => self.refer(graph, node),
        }
    }
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
                for sink in graph.sinks(Source::Port { node, port }) {
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

/// Which `select`s a listing draws as **one branch**.
///
/// A branch is a select per answer, so the box a source `branch` used to
/// be is now several, and a reader wants the one bracket back. Peers on
/// one condition are that bracket — but only where they sit at one depth:
/// the regions a listing draws have to be laminar for [`schedule`] to nest
/// them, and a peer inside some other branch that its fellow is outside of
/// would make a bracket that straddles rather than nests.
///
/// So the key is the condition **and** where the select sits, which is
/// what [`nesting`] answers — and that answer is read in the grouping this
/// is computing. The two are found together, coarsest-first: every select
/// alone, then the nesting that follows, then the peers that agree under
/// it, until nothing more merges. Merging only ever makes a nesting
/// coarser, so the rounds are monotone and the fixpoint is reached in at
/// most one round per select.
///
/// A group is named by its least member, which is a name like any other:
/// it keys one listing and is never written down.
fn grouping(graph: &Graph) -> HashMap<NodeId, u32> {
    let selects: Vec<NodeId> = graph
        .live()
        .filter(|(_, kind)| matches!(kind, NodeKind::Select))
        .map(|(id, _)| id)
        .collect();
    // Every select its own branch, which is what the listing drew before
    // an answer was a box of its own.
    let mut named: HashMap<NodeId, u32> =
        selects.iter().map(|&id| (id, id.index() as u32)).collect();
    for _ in 0..selects.len() {
        let inside = nesting(graph, &named);
        let mut peers: BTreeMap<(Source, BTreeSet<u32>), Vec<NodeId>> = BTreeMap::new();
        for &id in &selects {
            let key = (
                graph.sources(id)[0],
                inside.get(&id).cloned().unwrap_or_default(),
            );
            peers.entry(key).or_default().push(id);
        }
        let mut merged: HashMap<NodeId, u32> = HashMap::new();
        for members in peers.values() {
            let name = members
                .iter()
                .map(|id| id.index() as u32)
                .min()
                .expect("a group has a member");
            for &id in members {
                merged.insert(id, name);
            }
        }
        if merged == named {
            return named;
        }
        named = merged;
    }
    named
}

/// The `select`s of each branch a listing draws, by that branch's name.
fn members(named: &HashMap<NodeId, u32>) -> BTreeMap<u32, Vec<NodeId>> {
    let mut out: BTreeMap<u32, Vec<NodeId>> = BTreeMap::new();
    for (&id, &branch) in named {
        out.entry(branch).or_default().push(id);
    }
    for held in out.values_mut() {
        held.sort_unstable();
    }
    out
}

/// Which branches each box lies inside.
///
/// A branch is named by the `select`s that are it — one per answer, which
/// [`grouping`] is what collects — and a box is inside it when [`arms_of`]
/// finds it: upstream of those selects' blocks, not upstream of the
/// condition they share, and read by nothing outside the region. A select
/// is not inside its own branch; a listing draws it as the bracket it is.
///
/// A box that reads nothing belongs to no branch by that test and still
/// *belongs* to the arm that reads it — a `push` is an operand, and the arm
/// is where a reader looks for it. Such a box goes where everything reading
/// it agrees it is: the intersection of its readers' branches, to fixpoint,
/// so a constant feeding a constant follows along.
fn nesting(graph: &Graph, named: &HashMap<NodeId, u32>) -> HashMap<NodeId, BTreeSet<u32>> {
    let held = members(named);
    let mut inside: HashMap<NodeId, BTreeSet<u32>> = HashMap::new();
    for (&branch, selects) in &held {
        for node in arms_of(graph, selects) {
            if !selects.contains(&node) {
                inside.entry(node).or_default().insert(branch);
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
                for sink in graph.sinks(Source::Port { node: id, port }) {
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

    // A branch nested inside another is wholly inside it: its selects are,
    // so its arms are too. Each branch above was asked on its own, which
    // leaves its arms knowing their own branch and no other. This is where
    // they learn the rest, and it is what makes the depth a box is drawn at
    // agree with the depth its brackets open at.
    loop {
        let mut moved = false;
        for (&branch, selects) in &held {
            // Every select of one branch sits in the same branches — that
            // is what [`grouping`] keyed on — so any of them says where.
            let outer = selects
                .first()
                .and_then(|id| inside.get(id))
                .cloned()
                .unwrap_or_default();
            if outer.is_empty() {
                continue;
            }
            let owned: Vec<NodeId> = inside
                .iter()
                .filter(|(_, mine)| mine.contains(&branch))
                .map(|(&id, _)| id)
                .collect();
            for id in owned {
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

/// The arms of a branch: what feeds its selects' block ports and nothing
/// else.
///
/// Nothing marks an arm's boxes as the arm's own, so the question is asked
/// from the selects. Start from everything upstream of their blocks, drop
/// what is also upstream of the condition — that is shared context,
/// computed before the branch was ever reached — and then shrink to a
/// fixpoint by dropping any box something outside the region reads, because
/// a box two regions share belongs to neither.
///
/// Asked of the whole branch at once, which is what keeps a listing's arms
/// what they were when a branch was one box: work an arm does for two of
/// its answers is read from inside the region either way, where asking
/// each select on its own would find it shared between two regions and give
/// it to neither.
fn arms_of(graph: &Graph, selects: &[NodeId]) -> HashSet<NodeId> {
    let upstream = |source: &Source| match *source {
        Source::Port { node, .. } => reach(graph, node, false),
        Source::Input(_) => HashSet::new(),
    };
    let Some(&first) = selects.first() else {
        return HashSet::new();
    };
    let shared = upstream(&graph.sources(first)[0]);
    let mut region: HashSet<NodeId> = selects
        .iter()
        .flat_map(|&select| graph.sources(select)[1..].to_vec())
        .flat_map(|source| upstream(&source))
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
                            Sink::Port { node, .. } => {
                                !selects.contains(node) && !region.contains(node)
                            }
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

/// Which arm of each branch a box belongs to — `true` for the then side —
/// and, as it reads that, which boxes belong to **neither** arm.
///
/// A branch's region wants to split cleanly in two: the sides are backward
/// reaches from disjoint sets of blocks, so a box the then side reads is a
/// then-side box by that very fact. That is what lets the listing draw an
/// `else`, and it is why the split is a **reading** rather than a choice.
///
/// It does not split cleanly on its own, because a box can be read from
/// both sides. [`Law::SelectHoist`](crate::kernel::rules::Law) grows a
/// branch *forwards* over the work after it, and the two copies it leaves
/// read whatever that work read from outside — one wire, a reader in each
/// arm. ([`Law::CondHoist`](crate::kernel::rules::Law) leaves the same
/// shape, its two copies reading the blocks of the branch that moved.) Such a box is upstream of both block lists, and if it reads
/// nothing itself then [`nesting`]'s intersection puts it inside the
/// branch, since every reader agrees on the branch and the intersection
/// cannot see that they disagree on the arm.
///
/// A box two arms share belongs to neither, exactly as a box two regions
/// share does, so this drops it from the branch — leaving it to
/// [`operands_last`], which lands a box of no branch outside the branch
/// its reader is in. Sharing runs backwards: the reach that finds a box
/// from both sides finds everything it reads from both sides too, so one
/// pass settles it and what is left is the clean split the listing draws.
fn arms(
    graph: &Graph,
    named: &HashMap<NodeId, u32>,
    inside: &mut HashMap<NodeId, BTreeSet<u32>>,
) -> HashMap<(NodeId, u32), bool> {
    let mut region: HashMap<u32, HashSet<NodeId>> = HashMap::new();
    for (&id, branches) in inside.iter() {
        for &branch in branches {
            region.entry(branch).or_default().insert(id);
        }
    }
    let mut out: HashMap<(NodeId, u32), bool> = HashMap::new();
    let mut shared: Vec<(NodeId, u32)> = Vec::new();
    for (branch, selects) in members(named) {
        let Some(mine) = region.get(&branch) else {
            continue;
        };
        // Every answer's then block, then every answer's else block: the
        // branch's two sides are the two block ports over all of its
        // selects.
        let block = |which: usize| -> Vec<Source> {
            selects
                .iter()
                .map(|&select| graph.sources(select)[which])
                .collect()
        };
        for (blocks, side) in [(block(1), true), (block(2), false)] {
            let mut todo: Vec<Source> = blocks.clone();
            let mut seen: HashSet<NodeId> = HashSet::new();
            while let Some(source) = todo.pop() {
                let Source::Port { node, .. } = source else {
                    continue;
                };
                if !mine.contains(&node) || !seen.insert(node) {
                    continue;
                }
                if out
                    .insert((node, branch), side)
                    .is_some_and(|was| was != side)
                {
                    shared.push((node, branch));
                }
                todo.extend(graph.sources(node).iter().copied());
            }
        }
    }
    for (node, branch) in shared {
        out.remove(&(node, branch));
        if let Some(mine) = inside.get_mut(&node) {
            mine.remove(&branch);
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
) -> Vec<Printing> {
    let order = nested_order(graph, inside, arms).unwrap_or_else(|| wherever_ready(graph, inside));
    debug_assert_eq!(order.len(), graph.live_count(), "the graph is acyclic");
    operands_at_each_use(graph, inside, arms, order)
}

/// One line of the listing: a box, and where it is drawn.
///
/// Nearly every box has exactly one, drawn in its own place. A box that
/// reads nothing has one per arm that reads it — see
/// [`operands_at_each_use`] — so `id` is not a key here, and `repeat` is
/// what the listing says out loud when it is not.
struct Printing {
    id: NodeId,
    /// The arms this line is drawn inside: which branches hold it, and
    /// which side of each. A box's own place, or — for a box written at
    /// its uses — the place of the readers this line answers for.
    place: BTreeMap<u32, bool>,
    /// The readers this line answers for: all of the box's, unless the box
    /// is written more than once, in which case the lines partition them.
    read_by: Vec<Sink>,
    /// Whether the box is written elsewhere too. A bare id says this line
    /// is the only one for the box; a parenthesised one says it is not.
    repeat: bool,
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
                for sink in graph.sinks(Source::Port { node: id, port }) {
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
            for sink in graph.sinks(Source::Port { node: id, port }) {
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

/// How many boxes may sit between two uses of a value before the listing
/// writes it again rather than making a reader look back for it.
///
/// A legibility number, like [`LABEL`], and the listing is the only thing
/// that reads it: what it trades is a line against a glance.
const REACH: usize = 6;

/// The readers of one box that sit in one arm, and where the line
/// answering for them lands: the index in the schedule of the box it
/// comes before, or `None` for the end of the listing.
struct Group {
    place: BTreeMap<u32, bool>,
    first: Option<usize>,
    read_by: Vec<Sink>,
}

/// Writes each box that reads nothing where it is read — at **every** arm
/// that reads it, not once for all of them. The module docs say why only
/// these boxes may be written twice; this is how the lines are placed.
///
/// A box's readers are grouped by the arm they sit in, and each group
/// gets a line just before the first of them. That spot is always legal:
/// the brackets open there are the reader's own, so a line drawn in the
/// reader's place sits inside the reader's run and breaks nothing.
///
/// Two exceptions shape the rest of it.
///
/// A reader **outside** an arm the box is in cannot take the box along —
/// the box is that arm's content, not the reader's operand. That is
/// `branch { push 1 } { push 2 }`, where the pushes are the arms and the
/// only reader is the `select` that ends the branch. [`nesting`] already
/// put such a box in its arm and the schedule already placed it there, so
/// that group keeps the place the schedule gave it.
///
/// And a value written a line or two up needs no second line, so two
/// groups within [`REACH`] of each other become one — but only when one's
/// place encloses the other's, so a reader finds the line by looking out
/// through brackets that are closing rather than across into an arm it
/// cannot see. The endif ladder a decision tree leaves is what the merge
/// is for; two arms of one branch are what the enclosing test refuses,
/// however close they sit.
fn operands_at_each_use(
    graph: &Graph,
    inside: &HashMap<NodeId, BTreeSet<u32>>,
    arms: &HashMap<(NodeId, u32), bool>,
    order: Vec<NodeId>,
) -> Vec<Printing> {
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

    // Where the schedule itself put each floating box: the box it came
    // before. That is the answer for a literal that is an arm's whole
    // content — `branch { push 1 } { push 2 }` — since the arm is where
    // [`nesting`] put it and no reader of it is in the arm at all.
    let mut scheduled: HashMap<NodeId, Option<usize>> = HashMap::new();
    let mut next = 0;
    let mut waiting: Vec<NodeId> = Vec::new();
    for &id in &order {
        match floating.contains(&id) {
            true => waiting.push(id),
            false => {
                for id in waiting.drain(..) {
                    scheduled.insert(id, Some(next));
                }
                next += 1;
            }
        }
    }
    for id in waiting {
        scheduled.insert(id, None);
    }

    // Placement goes by the links as the graph has them, so that a box is
    // never written before one it reads. What a line *names* looks through
    // the boxes elision drops, which is a different question and is asked
    // of each link on its own.
    let sinks = |id: NodeId| -> Vec<Sink> {
        let mut found = Vec::new();
        let mut seen = HashSet::new();
        for port in 0..graph.kind(id).arity().outputs {
            found.extend(
                graph
                    .sinks(Source::Port { node: id, port })
                    .iter()
                    .copied()
                    .filter(|&sink| seen.insert(sink)),
            );
        }
        found
    };
    let named = |sink: Sink| -> Vec<Sink> { vec![sink] };
    // Which arms a box is drawn inside, and which side of each.
    let place = |id: NodeId| -> BTreeMap<u32, bool> {
        inside
            .get(&id)
            .into_iter()
            .flatten()
            .map(|&branch| (branch, arms.get(&(id, branch)).copied().unwrap_or(true)))
            .collect()
    };

    let mut lands: HashMap<usize, Vec<Printing>> = HashMap::new();
    let mut last: Vec<Printing> = Vec::new();
    for &id in &order {
        if !floating.contains(&id) {
            continue;
        }
        let mine = place(id);
        // A reader at least as deep as the box takes it along: the spot
        // just before that reader has the reader's brackets open, so a
        // line there is legal, and it is beside what reads it. A reader
        // *outside* an arm the box is in cannot — the box is that arm's
        // content, and the schedule already found it a place.
        let mut groups: Vec<Group> = Vec::new();
        for sink in sinks(id) {
            let theirs = match sink {
                Sink::Port { node, .. } => Some(place(node)),
                Sink::Output(_) => None,
            };
            let (where_, first) = match theirs {
                Some(theirs)
                    if mine
                        .iter()
                        .all(|(branch, side)| theirs.get(branch) == Some(side)) =>
                {
                    let Sink::Port { node, .. } = sink else {
                        unreachable!("a boundary read has no place")
                    };
                    (theirs, at.get(&node).copied())
                }
                _ => (mine.clone(), scheduled[&id]),
            };
            match groups.iter_mut().find(|group| group.place == where_) {
                Some(group) => {
                    group.first = match (group.first, first) {
                        (Some(a), Some(b)) => Some(a.min(b)),
                        (a, b) => a.or(b),
                    };
                    group.read_by.push(sink);
                }
                None => groups.push(Group {
                    place: where_,
                    first,
                    read_by: vec![sink],
                }),
            }
        }

        // A value already written a line or two up needs no second line:
        // the reader can see it. So two groups become one when they land
        // within `REACH` of each other **and** one's place encloses the
        // other's — the line keeps the earlier place, and a reader of the
        // later group finds it by looking out through brackets that are
        // closing, never across into an arm it cannot see. The endif
        // ladder a decision tree leaves is what this is for: three
        // `endif`s in six lines all answering `true` want one `push true`
        // above them, not one apiece. Two arms of one branch are the case
        // it must refuse, however close they sit: the `else` between them
        // is exactly the line that says the first is out of view.
        let nested = |a: &BTreeMap<u32, bool>, b: &BTreeMap<u32, bool>| {
            let (inner, outer) = match a.len() <= b.len() {
                true => (a, b),
                false => (b, a),
            };
            inner
                .iter()
                .all(|(branch, side)| outer.get(branch) == Some(side))
        };
        groups.sort_by_key(|group| group.first.unwrap_or(usize::MAX));
        let mut merged: Vec<Group> = Vec::new();
        for group in groups {
            match merged.last_mut() {
                Some(last)
                    if matches!((last.first, group.first), (Some(a), Some(b)) if b - a <= REACH)
                        && nested(&last.place, &group.place) =>
                {
                    last.read_by.extend(group.read_by);
                }
                _ => merged.push(group),
            }
        }

        // A box nothing reads still has to appear: a listing that drops a
        // live box is lying.
        if merged.is_empty() {
            merged.push(Group {
                place: mine,
                first: scheduled[&id],
                read_by: Vec::new(),
            });
        }
        let repeat = merged.len() > 1;
        for group in merged {
            let mut read_by: Vec<Sink> = Vec::new();
            let mut seen = HashSet::new();
            for sink in group.read_by {
                read_by.extend(named(sink).into_iter().filter(|&sink| seen.insert(sink)));
            }
            let printing = Printing {
                id,
                place: group.place,
                read_by,
                repeat,
            };
            match group.first {
                Some(i) => lands.entry(i).or_default().push(printing),
                None => last.push(printing),
            }
        }
    }

    let mut written = Vec::with_capacity(order.len());
    for (i, &id) in solid.iter().enumerate() {
        written.extend(lands.remove(&i).unwrap_or_default());
        let mut read_by: Vec<Sink> = Vec::new();
        let mut seen = HashSet::new();
        for sink in sinks(id) {
            read_by.extend(named(sink).into_iter().filter(|&sink| seen.insert(sink)));
        }
        written.push(Printing {
            id,
            place: place(id),
            read_by,
            repeat: false,
        });
    }
    written.extend(last);

    debug_assert!(lands.is_empty(), "every landing is before a box");
    #[cfg(debug_assertions)]
    {
        // Every live box is written, and what the lines of one say
        // between them is the whole of who reads it.
        let mut said: HashMap<NodeId, HashSet<Sink>> = HashMap::new();
        for printing in &written {
            said.entry(printing.id)
                .or_default()
                .extend(printing.read_by.iter().copied());
        }
        for &id in &order {
            let Some(theirs) = said.get(&id) else {
                panic!("{} is live and went unwritten", id);
            };
            let mut all: HashSet<Sink> = HashSet::new();
            for sink in sinks(id) {
                all.extend(named(sink));
            }
            assert_eq!(
                *theirs, all,
                "{}'s lines do not name all of its readers",
                id
            );
        }
    }
    written
}

/// How the census names a box: the kind without its width or its literal, so
/// that `push 1` and `push true` count together as `push`.
fn census_name(kind: &NodeKind) -> String {
    match kind {
        NodeKind::Call { .. } => "call".to_string(),
        NodeKind::Select => "branch".to_string(),
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
        let names = Names::of(graph, self.bold);
        let named = grouping(graph);
        let mut inside = nesting(graph, &named);
        let arms = arms(graph, &named, &mut inside);
        let written = schedule(graph, &inside, &arms);
        let shown = |_id: NodeId| true;

        // A box's branches, outermost first: the chain it is nested in, and
        // so the depth it and each of its brackets are drawn at.
        let mut held: HashMap<u32, usize> = HashMap::new();
        for branches in inside.values() {
            for &branch in branches {
                *held.entry(branch).or_default() += 1;
            }
        }
        let chain = |place: &BTreeMap<u32, bool>| -> Vec<u32> {
            let mut mine: Vec<u32> = place.keys().copied().collect();
            mine.sort_by_key(|branch| (std::cmp::Reverse(held.get(branch).copied()), *branch));
            mine
        };
        // What each branch decides on, named the way every other wire in
        // the listing is named — so `if #12.0` and the `#12` line above are
        // plainly the same wire.
        let condition: HashMap<u32, String> = graph
            .live()
            .filter_map(|(id, kind)| match kind {
                NodeKind::Select => {
                    let source = *graph.sources(id).first()?;
                    Some((named[&id], names.source(graph, source)))
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
            if shown(id) && !matches!(kind, NodeKind::Select) {
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

        // Counted by the **branch**, not by the select: an answer apiece
        // is what a `branch` builds, and a reader counting brackets on the
        // page should get the same number back.
        let branches = named.values().collect::<HashSet<_>>().len();
        let boxes = graph.live().filter(|&(id, _)| shown(id)).count();
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

        for printing in &written {
            let id = printing.id;
            if !shown(id) {
                continue;
            }
            let kind = graph.kind(id);
            let mine = chain(&printing.place);
            // The lines a reader needs before this one. A branch is one
            // box and that box is its `endif`, so every `if` and every
            // `else` is drawn rather than printed from a box — which is
            // what the empty id column says.
            //
            // Each of them sits at the depth of the branch it belongs to,
            // and that is its place in this box's chain: the box is drawn
            // at `mine.len()`, and a branch `mine[k]` holds it from `k`.
            let ends = match kind {
                NodeKind::Select => Some(named[&id]),
                _ => None,
            };
            let mut ahead: Vec<(&str, u32, usize)> = Vec::new();
            for (depth, &branch) in mine.iter().enumerate() {
                if !opened.contains(&branch) {
                    ahead.push(("if", branch, depth));
                }
                let then = printing.place.get(&branch).copied().unwrap_or(true);
                if !then && parts.contains(&branch) && !parted.contains(&branch) {
                    ahead.push(("else", branch, depth));
                }
            }
            // A `select` closes its branch, so anything that branch still
            // owes — an opening it never got because it owns no box of its
            // own, an `else` its else arm was too empty to trigger — is
            // owed here, at the select's own depth. A select is not inside
            // its own branch, so that is `mine.len()`.
            if let (Some(branch), NodeKind::Select) = (ends, kind)
                && !opened.contains(&branch)
            {
                ahead.push(("if", branch, mine.len()));
            }
            for (word, branch, depth) in ahead {
                // An empty name column: a branch's `endif`s are its
                // selects, so an `if` and an `else` are lines the listing
                // draws rather than boxes it prints.
                writeln!(
                    f,
                    "{:<margin$}{}{} {}",
                    "",
                    gutter(depth),
                    word,
                    condition.get(&branch).map_or("?", String::as_str),
                    margin = MARGIN
                )?;
                match word {
                    "if" => opened.insert(branch),
                    _ => parted.insert(branch),
                };
            }
            let indent = gutter(mine.len());
            let label = match kind {
                // A select is the block it closes: what a reader wants from
                // it is where the arms end, and `endif` is how a reader
                // already knows how to read that.
                NodeKind::Select => format!(
                    "{}endif {}",
                    indent,
                    ends.and_then(|branch| condition.get(&branch))
                        .map_or("?", String::as_str)
                ),
                other => format!("{}{}", indent, other),
            };
            let label = match label.char_indices().nth(LABEL - 1) {
                Some((cut, _)) => format!("{}…", &label[..cut]),
                None => label,
            };

            let sources: Vec<String> = graph
                .sources(id)
                .iter()
                .map(|&source| names.source(graph, source))
                .collect();
            // A select reads its condition at port 0 and the label has
            // already said so, so what is left for this column is what it
            // does with the rest: the two blocks it chooses between.
            let reads = match kind {
                NodeKind::Select if sources.len() > 1 => {
                    format!("then {}  else {}", sources[1], sources[2])
                }
                NodeKind::Select => String::new(),
                _ if sources.is_empty() => String::new(),
                _ => format!("← {}", sources.join(" ")),
            };

            let mut read_by: Vec<String> = printing
                .read_by
                .iter()
                .map(|&sink| names.sink(graph, sink))
                .collect();
            read_by.dedup();
            let read_by = match read_by.is_empty() {
                true => "  ·  nothing reads it".to_string(),
                false => format!("  → {}", read_by.join(" ")),
            };

            // The name column is padded by hand: an emphasised address
            // carries escapes that take no room on the page, and `{:<n}`
            // would count them as if they did.
            let (name, wide) = match printing.repeat {
                true => (format!("({})", names.spell(graph, id)), NAME),
                false => (names.spell(graph, id), SPELLED),
            };
            writeln!(
                f,
                "  {}{} {:<label$}{:<24}{}",
                name,
                " ".repeat(NAME - wide),
                label,
                reads,
                read_by,
                label = LABEL + 1
            )?;
        }

        let outputs: Vec<String> = graph
            .outputs()
            .iter()
            .map(|&source| names.source(graph, source))
            .collect();
        let out = format!("{:<width$}", "out", width = NAME);
        match outputs.is_empty() {
            true => writeln!(f, "\n  {}()", out),
            false => writeln!(f, "\n  {}← {}", out, outputs.join(" ")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::tests::built;

    /// A branch grown **forwards** over the work after it, and the operand
    /// that work read from outside — now read by a copy in each arm.
    ///
    /// The two hoists are the rows that make this shape — `select-hoist`
    /// here — and it is the shape both the arm reading and the
    /// writing-at-each-use rest on.
    fn grown() -> (Graph, NodeId) {
        use crate::kernel::prim::Prim;
        use crate::kernel::rules::{Law, apply, propose};

        let mut graph = built("branch { push 1 } { push 2 } push 10 add");
        let select = graph
            .live()
            .find_map(|(id, kind)| matches!(kind, NodeKind::Select).then_some(id))
            .expect("the body branches");
        let step = propose(&graph, &[Law::SelectHoist], select)
            .pop()
            .expect("the work after the branch is a body to grow over");
        apply(&mut graph, &step).expect("the branch grows forwards");
        graph.check().unwrap_or_else(|e| panic!("{}", e));

        let shared = graph
            .live()
            .filter(|(_, kind)| matches!(kind, NodeKind::Op(Prim::Push(_))))
            .map(|(id, _)| id)
            .find(|&id| graph.sinks(Source::Port { node: id, port: 0 }).len() == 2)
            .unwrap_or_else(|| {
                panic!(
                    "the hoist left no operand read twice:\n{}",
                    listing(&graph, "left")
                )
            });
        (graph, shared)
    }

    /// A box's own line, as the listing spells it: the whole address.
    fn spelled(graph: &Graph, id: NodeId) -> String {
        format!("#{}", graph.address(id).letters())
    }

    /// A reference to a box, as the listing spells one: the prefix that
    /// tells it apart.
    fn referred(graph: &Graph, id: NodeId) -> String {
        format!("#{}", graph.shortest(id))
    }

    #[test]
    fn a_listing_names_every_box_it_shows() {
        let graph = built("push 1 push 2 add");
        let text = listing(&graph, "left").to_string();
        for (id, _) in graph.live() {
            assert!(
                text.contains(&format!("  {} ", spelled(&graph, id))),
                "{} is missing from\n{}",
                graph.address(id),
                text
            );
        }
    }

    /// The listing shows every live box when nothing is elided — a report
    /// that quietly drops one is worse than a long one.
    #[test]
    fn nothing_live_goes_unlisted() {
        let graph = built("push 1 pick 0 swap drop 0");
        let text = listing(&graph, "left").to_string();
        let listed: HashSet<&str> = text
            .lines()
            .filter_map(|line| line.split_whitespace().next())
            .filter(|word| word.starts_with('#') || word.starts_with("(#"))
            .collect();
        assert_eq!(listed.len(), graph.live_count());
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
        // The opening has no box behind it — a branch is its `endif` —
        // and the empty id column is how the listing says so.
        assert!(
            lines[at("if in0")].starts_with(&" ".repeat(MARGIN)),
            "a drawn opening names a box:\n{}",
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
        let named = grouping(&graph);
        let mut inside = nesting(&graph, &named);
        let arms = arms(&graph, &named, &mut inside);
        let written = schedule(&graph, &inside, &arms);
        let mut placed: HashSet<NodeId> = HashSet::new();
        for printing in &written {
            for &source in graph.sources(printing.id) {
                if let Source::Port { node, .. } = source {
                    assert!(
                        placed.contains(&node),
                        "{} is listed before {}",
                        printing.id,
                        node
                    );
                }
            }
            placed.insert(printing.id);
        }
    }

    /// A branch grown **forwards** leaves an operand its two arms share,
    /// and a box two arms share is a box of neither.
    ///
    /// `select-hoist` copies the work after a branch into both of its
    /// arms, so what that work read from outside is now read from both. A
    /// `push` like that has every reader inside the branch and none
    /// outside, which is exactly what [`nesting`]'s intersection reads as
    /// "inside" — it cannot see that the readers disagree on the *arm*.
    /// Drawing it inside one arm would put the other arm's reader before
    /// what it reads, so [`arms`] hands it back to the enclosing level.
    #[test]
    fn an_operand_both_arms_read_is_in_neither() {
        let (graph, shared) = grown();
        let named = grouping(&graph);
        let mut inside = nesting(&graph, &named);
        let arms = arms(&graph, &named, &mut inside);
        assert!(
            inside.get(&shared).is_none_or(|mine| mine.is_empty()),
            "{} is drawn inside a branch its two arms share it:\n{}",
            shared,
            listing(&graph, "left")
        );
        assert!(
            !arms.keys().any(|&(id, _)| id == shared),
            "{} was given an arm to belong to",
            shared
        );

        // Which is what keeps the schedule topological: the other arm's
        // reader would otherwise be listed before the box it reads.
        let written = schedule(&graph, &inside, &arms);
        let mut placed: HashSet<NodeId> = HashSet::new();
        for printing in &written {
            for &source in graph.sources(printing.id) {
                if let Source::Port { node, .. } = source {
                    assert!(
                        placed.contains(&node),
                        "{} is listed before {}:\n{}",
                        printing.id,
                        node,
                        listing(&graph, "left")
                    );
                }
            }
            placed.insert(printing.id);
        }

        // And the shared operand is written in each arm that reads it,
        // rather than once above the branch.
        let written_at: Vec<usize> = written
            .iter()
            .enumerate()
            .filter(|(_, p)| p.id == shared)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(
            written_at.len(),
            2,
            "the operand both arms read is written {} time(s):\n{}",
            written_at.len(),
            listing(&graph, "left")
        );
    }

    /// A value read from two arms is written in both, and each line names
    /// the readers there and no others.
    ///
    /// This is the one box the listing writes twice, and the two things a
    /// reader needs of it are that the operand is beside the `add` that
    /// takes it — in *each* arm, since neither can see into the other —
    /// and that the parenthesised id says the lines are one box. No
    /// reader is dropped for the split: the `→` columns partition them.
    #[test]
    fn a_value_read_from_two_arms_is_written_in_both() {
        let (graph, shared) = grown();
        let text = listing(&graph, "left").to_string();
        let mine: Vec<&str> = text
            .lines()
            .filter(|line| line.contains(&format!("({})", spelled(&graph, shared))))
            .collect();
        assert_eq!(
            mine.len(),
            2,
            "{} is not written in both arms:\n{}",
            graph.address(shared),
            text
        );

        // Each line sits in an arm, and names only what reads it there.
        let readers: Vec<Vec<&str>> = mine
            .iter()
            .map(|line| {
                line.split('→')
                    .nth(1)
                    .expect("a line names its readers")
                    .split_whitespace()
                    .collect()
            })
            .collect();
        assert!(
            readers.iter().all(|named| named.len() == 1),
            "a line names a reader in the other arm:\n{}",
            text
        );
        assert_ne!(
            readers[0], readers[1],
            "both lines name one reader:\n{}",
            text
        );

        // Together they say what one line would have: every reader, once.
        let all: HashSet<String> = graph
            .sinks(Source::Port {
                node: shared,
                port: 0,
            })
            .iter()
            .map(|sink| match sink {
                Sink::Output(i) => format!("out{}", i),
                Sink::Port { node, .. } => referred(&graph, *node),
            })
            .collect();
        let said: HashSet<String> = readers
            .iter()
            .flatten()
            .map(|name| name.to_string())
            .collect();
        assert_eq!(
            said, all,
            "the two lines do not name every reader:\n{}",
            text
        );
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
            // Branches leaving more than one answer, which is more than one
            // `select`: the listing has to draw one bracket over the lot.
            "branch { push 1 push 3 } { push 2 push 4 }",
            "branch { pick 0 not } { pick 0 negate }",
            "branch { branch { push 1 push 2 } { push 3 push 4 } } { drop 0 push 5 push 6 }",
        ];
        let (mut ever_nested, mut ever_grouped) = (false, false);
        for body in bodies {
            let graph = built(body);
            let named = grouping(&graph);
            let mut inside = nesting(&graph, &named);
            let arms = arms(&graph, &named, &mut inside);
            let written = schedule(&graph, &inside, &arms);
            ever_nested |= inside.values().any(|mine| mine.len() > 1);
            ever_grouped |= named.values().collect::<HashSet<_>>().len() < named.len();

            let once: HashSet<NodeId> = written.iter().map(|p| p.id).collect();
            assert_eq!(
                once.len(),
                graph.live_count(),
                "{}: every box at least once",
                body
            );
            let mut placed: HashSet<NodeId> = HashSet::new();
            for printing in &written {
                for &source in graph.sources(printing.id) {
                    if let Source::Port { node, .. } = source {
                        assert!(
                            placed.contains(&node),
                            "{}: {} before {}",
                            body,
                            printing.id,
                            node
                        );
                    }
                }
                placed.insert(printing.id);
            }

            // Contiguous: between a region's first and last line sits
            // nothing that is not the region's, its own ends aside. Asked
            // of the lines rather than the boxes, since a box written at
            // its uses is in whichever region each of its lines is drawn.
            let mut region: HashMap<u32, Vec<usize>> = HashMap::new();
            for (i, printing) in written.iter().enumerate() {
                for &branch in printing.place.keys() {
                    region.entry(branch).or_default().push(i);
                }
            }
            for (branch, held) in &region {
                let lo = *held.first().expect("a line");
                let hi = *held.last().expect("a line");
                for (i, printing) in written.iter().enumerate().take(hi + 1).skip(lo) {
                    // A branch's own selects are its ends, and there is
                    // one per answer.
                    let ends = named.get(&printing.id) == Some(branch);
                    assert!(
                        held.contains(&i) || ends,
                        "{}: {} sits inside branch #{}, which is not its own:\n{}",
                        body,
                        printing.id,
                        branch,
                        listing(&graph, "left")
                    );
                }
            }

            // And the drawing balances: every `if` reaches an `endif` at
            // the depth it opened, innermost first, with any `else` in
            // between at that same depth.
            let text = listing(&graph, "left").to_string();
            let mut stack: Vec<(String, usize)> = Vec::new();
            // The `endif` run in progress, if a line just drew one.
            let mut closing: Option<(String, usize)> = None;
            let mut blocks = 0;
            for line in text.lines() {
                // Past the name column is the gutter, and past that the
                // word.
                let Some(rest) = line.get(MARGIN..) else {
                    continue;
                };
                let depth = rest.matches("| ").count();
                let word = rest.trim_start_matches("| ");
                let condition = |word: &str| {
                    word.split_whitespace()
                        .nth(1)
                        .expect("a block names its condition")
                        .to_string()
                };
                // A branch leaving several answers ends in several
                // selects, so one `if` is closed by a **run** of `endif`s
                // — each its own box, with its own links. The block is
                // done when the run is, which is the first line that is
                // not another `endif` of it.
                let here = word.starts_with("endif ").then(|| (condition(word), depth));
                if closing.is_some() && closing != here {
                    stack.pop();
                    closing = None;
                }
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
                } else if let Some(end) = here {
                    assert_eq!(
                        stack.last(),
                        Some(&end),
                        "{}: an `endif` out of turn:\n{}",
                        body,
                        text
                    );
                    closing = Some(end);
                }
            }
            if closing.take().is_some() {
                stack.pop();
            }
            assert!(
                stack.is_empty(),
                "{}: a block never closes:\n{}",
                body,
                text
            );
            assert_eq!(
                blocks,
                named.values().collect::<HashSet<_>>().len(),
                "{}: a branch got no block, or got two:\n{}",
                body,
                text
            );
        }
        assert!(
            ever_nested,
            "the bodies must actually nest, or this proves nothing"
        );
        assert!(
            ever_grouped,
            "some body must leave a branch of several answers, or the \
             grouping is untested"
        );
    }
}
