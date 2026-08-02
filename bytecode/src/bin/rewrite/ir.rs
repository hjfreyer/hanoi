//! The tree the tool rewrites and prints.

use std::collections::HashSet;

use bytecode::{Instruction, Library, SentenceIndex};

use crate::program::Program;

/// One step of a listing.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(Instruction),
    /// A call that has not been expanded. `depth == 0` is a plain jump.
    ///
    /// This is what `Cut` used to be, generalized: a cut edge was always a call
    /// somebody declined to expand. Making it the same node means a recursive
    /// call has a real arity — from its target's `#[arity]` — where a `Cut` had
    /// none and poisoned the reckoning of everything after it.
    Call { depth: usize, target: SentenceIndex },
    /// An expanded call: a block running below `depth` hidden values.
    Dip {
        depth: usize,
        /// Where this came from; more than one entry after a fusion.
        origins: Vec<String>,
        body: Vec<Node>,
    },
    Branch {
        then_origin: String,
        then_body: Vec<Node>,
        else_origin: String,
        else_body: Vec<Node>,
    },
}

/// The name phase 4 gives a block that was written inline rather than called.
///
/// Both branch arms and `dip N { ... }` bodies get a `SentenceIndex` only
/// because the compiler needs somewhere to put them; nobody jumps to either by
/// name.
const INLINE_BLOCK: &str = "<inline>";

fn is_inline_block(library: &Library, target: SentenceIndex) -> bool {
    library.names[target] == INLINE_BLOCK
}

/// Turns a sentence into a tree, expanding nothing that `inline` could expand.
///
/// Blocks written inline *are* expanded, because a block is not a call. Phase 4
/// gives a branch arm and a `dip N { ... }` body a `SentenceIndex` alike, purely
/// because it needs somewhere to put them, and neither is reachable by name — so
/// there is no call site for `inline` to open and nothing for the un-expanded
/// listing to name on one line. Leaving them closed only meant that a rule
/// wanting to look inside a dip had to ask for an expansion that expands nothing.
///
/// A `dip N` or a `jump` naming a real sentence stays a [`Node::Call`]: there the
/// callee exists independently, `inline` is a real choice, and the label is worth
/// keeping. An inline block that would recurse also stays a `Call`, which is what
/// it becomes at run time anyway.
pub(crate) fn build(
    library: &Library,
    s_idx: SentenceIndex,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Vec<Node> {
    in_progress.insert(s_idx);

    let out = library.sentences[s_idx]
        .iter()
        .map(|inst| match inst {
            Instruction::Dip(depth, target) => build_dip(library, *depth, *target, in_progress),
            Instruction::Branch(then_t, else_t) => Node::Branch {
                then_origin: label(library, *then_t),
                then_body: build_arm(library, *then_t, in_progress),
                else_origin: label(library, *else_t),
                else_body: build_arm(library, *else_t, in_progress),
            },
            other => Node::Op(other.clone()),
        })
        .collect();

    in_progress.remove(&s_idx);
    out
}

fn build_dip(
    library: &Library,
    depth: usize,
    target: SentenceIndex,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Node {
    if is_inline_block(library, target) && !in_progress.contains(&target) {
        Node::Dip {
            depth,
            origins: vec![label(library, target)],
            body: build(library, target, in_progress),
        }
    } else {
        Node::Call { depth, target }
    }
}

fn build_arm(
    library: &Library,
    target: SentenceIndex,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Vec<Node> {
    if in_progress.contains(&target) {
        // A branch arm is entered with the condition already popped, which is
        // what `Dip(0, arm)` means.
        vec![Node::Call { depth: 0, target }]
    } else {
        build(library, target, in_progress)
    }
}

pub(crate) fn label(library: &Library, target: SentenceIndex) -> String {
    format!("#{} {}", usize::from(target), library.names[target])
}

/// The child sequences of a node, for traversal.
///
/// A `Call` has none: its body is a sentence in the library, not part of this
/// tree, and reaching it is what `inline` is for.
pub(crate) fn child_bodies(node: &mut Node) -> Vec<&mut Vec<Node>> {
    match node {
        Node::Dip { body, .. } => vec![body],
        Node::Branch {
            then_body,
            else_body,
            ..
        } => vec![then_body, else_body],
        Node::Op(_) | Node::Call { .. } => Vec::new(),
    }
}

/// Which child sequences a traversal should descend into.
///
/// `children` and its relatives take every child of every node; this names a
/// subset. The distinction is not cosmetic: a tactic that has to open one
/// branch arm and leave the other alone cannot be written without it, and
/// staged inlining stalls the moment the remaining calls sit inside arms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Selector {
    /// The `then` arm of every branch.
    Then,
    /// The `else` arm of every branch.
    Else,
    /// The body of every dip.
    Body,
}

/// The child sequences of a node that `sel` picks out.
///
/// A node with no child of that kind contributes nothing, so `then(t)` applied
/// to a sequence with no branches is a no-op rather than an error — the same
/// stance `each` takes towards a rule that matches nowhere.
pub(crate) fn selected_bodies(node: &mut Node, sel: Selector) -> Vec<&mut Vec<Node>> {
    match (node, sel) {
        (Node::Branch { then_body, .. }, Selector::Then) => vec![then_body],
        (Node::Branch { else_body, .. }, Selector::Else) => vec![else_body],
        (Node::Dip { body, .. }, Selector::Body) => vec![body],
        _ => Vec::new(),
    }
}

/// The nodes a call stands for.
///
/// A plain call — `depth == 0` — hides nothing, so its body is spliced straight
/// into the caller's sequence. Anything deeper keeps its frame, since there the
/// frame is what the instruction means.
pub(crate) fn expand_call(prog: &Program, depth: usize, target: SentenceIndex) -> Vec<Node> {
    let body = build(prog.library(), target, &mut HashSet::new());
    if depth == 0 {
        body
    } else {
        vec![Node::Dip {
            depth,
            origins: vec![prog.label(target)],
            body,
        }]
    }
}

/// Whether two nodes do the same thing.
///
/// Deliberately *not* the derived `PartialEq`. `Dip::origins` and a branch's
/// arm origins record where code came from, which is for the listing and says
/// nothing about what the code does — and phase 4 allocates a fresh
/// `SentenceIndex` for every inline block, so two identical blocks written in
/// different places never share a label. Comparing those would make provenance
/// part of term identity, which is how `factor_branch` used to miss every
/// shared prefix that contained a call.
///
/// A `Call` is compared by target: two calls to the same sentence do the same
/// thing, and two calls to different sentences might, but nothing here can tell
/// without expanding them.
pub(crate) fn same_effect(a: &Node, b: &Node) -> bool {
    match (a, b) {
        (Node::Op(x), Node::Op(y)) => x == y,
        (
            Node::Call {
                depth: da,
                target: ta,
            },
            Node::Call {
                depth: db,
                target: tb,
            },
        ) => da == db && ta == tb,
        (
            Node::Dip {
                depth: da,
                body: ba,
                ..
            },
            Node::Dip {
                depth: db,
                body: bb,
                ..
            },
        ) => da == db && same_effect_seq(ba, bb),
        (
            Node::Branch {
                then_body: ta,
                else_body: ea,
                ..
            },
            Node::Branch {
                then_body: tb,
                else_body: eb,
                ..
            },
        ) => same_effect_seq(ta, tb) && same_effect_seq(ea, eb),
        _ => false,
    }
}

fn same_effect_seq(a: &[Node], b: &[Node]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_effect(x, y))
}
