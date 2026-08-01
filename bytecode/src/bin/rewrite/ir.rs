//! The inlined tree the tool rewrites and prints.

use std::collections::HashSet;

use bytecode::{Instruction, Library, SentenceIndex};


/// One step of an inlined listing.
///
/// Calls have already been resolved into nested bodies, so nothing here refers
/// to a `SentenceIndex` except as a label. That is what lets arities be
/// computed structurally and dips be moved around without consulting the
/// library.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(Instruction),
    Dip {
        depth: usize,
        /// Where this dip came from; more than one entry after a fusion.
        origins: Vec<String>,
        body: Vec<Node>,
    },
    Branch {
        then_origin: String,
        then_body: Vec<Node>,
        else_origin: String,
        else_body: Vec<Node>,
    },
    /// A call that would not terminate if expanded.
    Cut(String),
}

pub(crate) fn build(library: &Library, s_idx: SentenceIndex, in_progress: &mut HashSet<SentenceIndex>) -> Vec<Node> {
    in_progress.insert(s_idx);
    let mut out = Vec::new();

    for inst in &library.sentences[s_idx] {
        let node = match inst {
            Instruction::Dip(k, target) => Node::Dip {
                depth: *k,
                origins: vec![label(library, *target)],
                body: build_target(library, *target, in_progress),
            },
            Instruction::Branch(then_t, else_t) => Node::Branch {
                then_origin: label(library, *then_t),
                then_body: build_target(library, *then_t, in_progress),
                else_origin: label(library, *else_t),
                else_body: build_target(library, *else_t, in_progress),
            },
            other => Node::Op(other.clone()),
        };
        out.push(node);
    }

    in_progress.remove(&s_idx);
    out
}

pub(crate) fn build_target(
    library: &Library,
    target: SentenceIndex,
    in_progress: &mut HashSet<SentenceIndex>,
) -> Vec<Node> {
    if in_progress.contains(&target) {
        vec![Node::Cut(label(library, target))]
    } else {
        build(library, target, in_progress)
    }
}

pub(crate) fn label(library: &Library, target: SentenceIndex) -> String {
    format!("#{} {}", usize::from(target), library.names[target])
}

/// Whether two nodes do the same thing.
///
/// Deliberately *not* the derived `PartialEq`. `Dip::origins` and a branch's
/// arm origins record where code came from, which is for the listing and says
/// nothing about what the code does — and phase 4 allocates a fresh
/// `SentenceIndex` for every inline block, so two identical blocks written in
/// different places never share a label. Comparing those would make provenance
/// part of term identity, which is how `factor_branches` used to miss every
/// shared prefix that contained a call.
///
/// A `Cut` is opaque: it stands for a body that was never expanded, so two of
/// them naming the same sentence still say nothing about the code inside.
pub(crate) fn same_effect(a: &Node, b: &Node) -> bool {
    match (a, b) {
        (Node::Op(x), Node::Op(y)) => x == y,
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

pub(crate) fn same_effect_seq(a: &[Node], b: &[Node]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_effect(x, y))
}

