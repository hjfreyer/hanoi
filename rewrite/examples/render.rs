//! A prototype of what a graph could look like in the proof report.
//!
//! ```bash
//! cargo run -p rewrite --example render
//! cargo run -p rewrite --example render -- two_spellings --all
//! cargo run -p rewrite --example render -- emit_does --diff
//! ```
//!
//! `-p rewrite` is what makes it work from anywhere in the workspace; the
//! corpus is found beside the crate rather than beside the shell.
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::cmp::Reverse;

use rewrite::corpus;
use rewrite::diagram2::{self, Graph, NodeId, NodeKind, Sink, Source};

/// A topological order that **stays inside a branch once it enters one**.
///
/// A plain min-id sort is topological and nothing else, so the constants an
/// arm pushes get hoisted out of it and the arm stops reading as a unit. Of
/// the nodes that are ready, this takes one that shares the most enclosing
/// branches with the node just placed, deepest first, id last — so an arm
/// runs to its `select` before anything outside it is placed.
fn schedule(g: &Graph, inside: &HashMap<NodeId, BTreeSet<u32>>) -> Vec<NodeId> {
    let mut waiting: HashMap<NodeId, usize> = g
        .live()
        .map(|(id, _)| {
            (id, g.sources(id).iter().filter(|s| matches!(s, Source::Port { .. })).count())
        })
        .collect();
    let mut ready: Vec<NodeId> =
        waiting.iter().filter(|&(_, &n)| n == 0).map(|(i, _)| *i).collect();
    let none = BTreeSet::new();
    let mut here: BTreeSet<u32> = BTreeSet::new();
    let mut order = Vec::new();
    while !ready.is_empty() {
        let pick = ready
            .iter()
            .enumerate()
            .max_by_key(|(_, id)| {
                let mine = inside.get(id).unwrap_or(&none);
                (mine.intersection(&here).count(), mine.len(), Reverse(id.index()))
            })
            .map(|(i, _)| i)
            .unwrap();
        let id = ready.swap_remove(pick);
        here = inside.get(&id).unwrap_or(&none).clone();
        order.push(id);
        for port in 0..g.kind(id).arity().outputs {
            for &sink in g.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink {
                    let n = waiting.get_mut(&node).unwrap();
                    *n -= 1;
                    if *n == 0 { ready.push(node); }
                }
            }
        }
    }
    float_down(g, order)
}

/// A box that reads nothing — a `push`, a `tuple 0` — is ready before
/// everything and belongs next to the one thing that wants it. Every
/// topological order is free to put it anywhere before its first reader,
/// so put it there: immediately before. Otherwise the whole constant pool
/// lands in one slab at the top and the operand of an `equal` is forty
/// lines from the `equal`.
fn float_down(g: &Graph, order: Vec<NodeId>) -> Vec<NodeId> {
    let floating: HashSet<NodeId> =
        order.iter().copied().filter(|&id| g.sources(id).is_empty()).collect();
    let mut feeds: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for &id in &floating {
        for port in 0..g.kind(id).arity().outputs {
            for &sink in g.sinks(Source::Port { node: id, port }) {
                if let Sink::Port { node, .. } = sink {
                    feeds.entry(node).or_default().push(id);
                }
            }
        }
    }
    let mut placed: HashSet<NodeId> = HashSet::new();
    let mut out = Vec::with_capacity(order.len());
    for &id in &order {
        if floating.contains(&id) { continue }
        for &c in feeds.get(&id).map(|v| v.as_slice()).unwrap_or(&[]) {
            if placed.insert(c) { out.push(c) }
        }
        out.push(id);
    }
    // Anything nothing reads still has to appear.
    for &id in &order {
        if floating.contains(&id) && !placed.contains(&id) { out.push(id) }
    }
    out
}

/// `id` and `copy` are what the rewriting is there to delete: an `id` box
/// stands between a value and its reader, and a `copy` says a value is read
/// twice, which the links already say. Reading through them shows the graph
/// the way `saturate` will leave it, without spending a step to find out.
fn elided(k: &NodeKind) -> bool {
    matches!(k, NodeKind::Id(_) | NodeKind::Copy(_))
}

/// The first source at or above `src` that a reader should be shown.
fn resolve(g: &Graph, src: Source) -> Source {
    let mut src = src;
    loop {
        let Source::Port { node, port } = src else { return src };
        match g.kind(node) {
            NodeKind::Id(_) => src = g.sources(node)[port],
            // Block-wise: output `i` and output `n + i` both stand for input `i`.
            NodeKind::Copy(n) => src = g.sources(node)[port % n],
            _ => return src,
        }
    }
}

/// Every reader of `src` that survives elision, looking through the boxes
/// that do not.
fn readers(g: &Graph, src: Source, out: &mut Vec<Sink>, seen: &mut HashSet<Sink>) {
    for &sink in g.sinks(src) {
        if !seen.insert(sink) { continue; }
        match sink {
            Sink::Port { node, .. } if elided(g.kind(node)) => {
                for port in 0..g.kind(node).arity().outputs {
                    readers(g, Source::Port { node, port }, out, seen);
                }
            }
            _ => out.push(sink),
        }
    }
}

fn reach(g: &Graph, from: NodeId, forward: bool) -> HashSet<NodeId> {
    let mut seen = HashSet::new();
    let mut q = VecDeque::from([from]);
    while let Some(n) = q.pop_front() {
        if !seen.insert(n) { continue; }
        if forward {
            for port in 0..g.kind(n).arity().outputs {
                for &s in g.sinks(Source::Port { node: n, port }) {
                    if let Sink::Port { node, .. } = s { q.push_back(node); }
                }
            }
        } else {
            for &s in g.sources(n) {
                if let Source::Port { node, .. } = s { q.push_back(node); }
            }
        }
    }
    seen
}

/// Which branches each node lies inside: downstream of the fork and
/// upstream of the select it is paired with. Exact, not a guess.
fn nesting(g: &Graph) -> HashMap<NodeId, BTreeSet<u32>> {
    let mut forks = HashMap::new();
    let mut selects = HashMap::new();
    for (id, kind) in g.live() {
        match kind {
            NodeKind::Fork { branch, .. } => { forks.insert(branch.index() as u32, id); }
            NodeKind::Select { branch, .. } => { selects.insert(branch.index() as u32, id); }
            _ => {}
        }
    }
    let mut inside: HashMap<NodeId, BTreeSet<u32>> = HashMap::new();
    for (&b, &f) in &forks {
        let Some(&s) = selects.get(&b) else { continue };
        let down = reach(g, f, true);
        let up = reach(g, s, false);
        for n in down.intersection(&up) {
            if *n != f && *n != s { inside.entry(*n).or_default().insert(b); }
        }
    }
    // A `push` depends on no fork, so by the test above it is inside no
    // branch — and it still *belongs* to the arm that reads it, which is
    // where a reader looks for it. A node that governs nothing goes where
    // everything that reads it agrees it is: the intersection of their
    // branches, to fixpoint, so a constant feeding a constant follows too.
    let ids: Vec<NodeId> = g.live().map(|(id, _)| id).collect();
    loop {
        let mut moved = false;
        for &id in ids.iter().rev() {
            if inside.contains_key(&id) || !g.sources(id).is_empty() { continue }
            let mut sets: Vec<BTreeSet<u32>> = Vec::new();
            for port in 0..g.kind(id).arity().outputs {
                for &sink in g.sinks(Source::Port { node: id, port }) {
                    match sink {
                        Sink::Output(_) => sets.push(BTreeSet::new()),
                        Sink::Port { node, .. } => {
                            sets.push(inside.get(&node).cloned().unwrap_or_default())
                        }
                    }
                }
            }
            let Some(first) = sets.first().cloned() else { continue };
            let common = sets.iter().fold(first, |a, b| a.intersection(b).copied().collect());
            if !common.is_empty() { inside.insert(id, common); moved = true; }
        }
        if !moved { break }
    }
    inside
}

fn kind_name(k: &NodeKind) -> String {
    match k {
        NodeKind::Op(p) => format!("{}", p).split_whitespace().next().unwrap_or("op").to_string(),
        NodeKind::Fork { .. } | NodeKind::Select { .. } => "branch".into(),
        NodeKind::Id(_) => "id".into(),
        NodeKind::Copy(_) => "copy".into(),
        NodeKind::Drop(_) => "drop".into(),
        NodeKind::Call { .. } => "call".into(),
    }
}

fn render(tag: &str, g: &Graph, elide: bool) -> String {
    let inside = nesting(g);
    let order = schedule(g, &inside);
    let a = g.arity();
    let keep = |id: NodeId| !elide || !elided(g.kind(id));

    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    for (id, k) in g.live() {
        if !keep(id) || matches!(k, NodeKind::Fork { .. } | NodeKind::Select { .. }) { continue; }
        *census.entry(kind_name(k)).or_default() += 1;
    }
    let branches = g.live().filter(|(_, k)| matches!(k, NodeKind::Fork { .. })).count();
    let shown = order.iter().filter(|&&id| keep(id)).count();
    let mut census: Vec<_> = census.into_iter().collect();
    census.sort_by_key(|(k, n)| (Reverse(*n), k.clone()));
    let summary: Vec<String> =
        census.iter().take(8).map(|(k, n)| format!("{}×{}", n, k)).collect();

    let mut out = String::new();
    out += &format!(
        "{}  {} boxes  {} branch{}  {} in → {} out{}\n",
        tag, shown, branches, if branches == 1 { "" } else { "es" },
        a.inputs, a.outputs,
        if elide { format!("   ({} id/copy read through)", g.live_count() - shown) }
        else { String::new() },
    );
    out += &format!("       {}\n\n", summary.join("  "));

    for &id in &order {
        if !keep(id) { continue; }
        let depth = inside.get(&id).map(|s| s.len()).unwrap_or(0);
        let kind = g.kind(id);
        let pad = "│  ".repeat(depth);
        let label = match kind {
            NodeKind::Fork { branch, .. } => format!("{}┌─ branch {}  ?", pad, branch.index()),
            NodeKind::Select { branch, .. } => format!("{}└─ branch {}  ⇒", pad, branch.index()),
            other => format!("{}{}", pad, other),
        };
        let label = if label.chars().count() > 44 {
            let short: String = label.chars().take(43).collect();
            format!("{}…", short)
        } else { label };

        // A fork and a select both read their condition at port 0; showing
        // it apart from the stack is the whole reason it lives there.
        let srcs: Vec<String> = g.sources(id).iter()
            .map(|&s| format!("{}", if elide { resolve(g, s) } else { s }))
            .collect();
        let from = match kind {
            NodeKind::Fork { .. } | NodeKind::Select { .. } if !srcs.is_empty() =>
                format!("if {}  on {}", srcs[0], srcs[1..].join(" ")),
            _ if srcs.is_empty() => String::new(),
            _ => format!("← {}", srcs.join(" ")),
        };
        let mut sinks = Vec::new();
        let mut seen = HashSet::new();
        for port in 0..kind.arity().outputs {
            if elide { readers(g, Source::Port { node: id, port }, &mut sinks, &mut seen); }
            else { sinks.extend(g.sinks(Source::Port { node: id, port }).iter().copied()); }
        }
        let mut to: Vec<String> = sinks.iter().map(|s| match s {
            Sink::Output(i) => format!("out{}", i),
            Sink::Port { node, .. } => format!("{}", node),
        }).collect();
        to.dedup();
        let to = if to.is_empty() { "  ·  nothing reads it".to_string() }
                 else { format!("  → {}", to.join(" ")) };
        out += &format!("  {:<5} {:<45}{:<24}{}\n", format!("{}", id), label, from, to);
    }
    let outs: Vec<String> = g.outputs().iter()
        .map(|&s| format!("{}", if elide { resolve(g, s) } else { s })).collect();
    out += &format!("\n  out   ← {}\n", outs.join(" "));
    out
}

fn main() {
    let mut filter = None;
    let mut elide = true;
    let mut diff = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--all" => elide = false,
            "--diff" => diff = true,
            "-h" | "--help" => {
                eprintln!(
                    "usage: cargo run -p rewrite --example render -- \
                     [<identity substring>] [--all] [--diff]\n\
                     \n  <substring>  which identity to render (default: emit_does)\
                     \n  --all        show every box, `id` and `copy` included\
                     \n  --diff       also drive the left side by `decide` and say what moved"
                );
                return;
            }
            other => filter = Some(other.to_string()),
        }
    }
    let filter = filter.unwrap_or_else(|| "emit_does".to_string());

    // The corpus sits beside the crate, not beside whatever directory this
    // was run from.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits in the workspace")
        .join("tests");
    let mut c = match corpus::load(&root) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: could not load the corpus at {}: {}", root.display(), e);
            std::process::exit(2);
        }
    };
    let Some((idx, _)) = c
        .library
        .identities
        .iter_enumerated()
        .find(|(_, i)| i.name.contains(&filter))
    else {
        eprintln!("error: no identity matching {:?}. The corpus states:", filter);
        for (_, i) in c.library.identities.iter_enumerated() {
            eprintln!("  {}", i.name);
        }
        std::process::exit(2);
    };
    let name = c.library.identities[idx].name.clone();

    let mut goal = rewrite::goal::Goal::of_identity(&mut c.terms, &c.library, idx).unwrap();
    diagram2::inline(&mut goal.lhs, &mut c.terms, &c.library, None).unwrap();
    diagram2::inline(&mut goal.rhs, &mut c.terms, &c.library, None).unwrap();

    println!("identity {}   (calls opened, nothing rewritten)\n", name);
    print!("{}", render("left ", &goal.lhs, elide));
    println!();
    print!("{}", render("right", &goal.rhs, elide));

    if !diff {
        return;
    }
    // What a step looks like when the ids are stable: drive the left side
    // and ask what moved. Nodes are only ever deleted, never renumbered.
    let before: BTreeSet<usize> = goal.lhs.live().map(|(i, _)| i.index()).collect();
    let names: HashMap<usize, String> =
        goal.lhs.live().map(|(i, k)| (i.index(), format!("{}", k))).collect();
    let mut after_graph = goal.lhs.clone();
    let mut deriv = diagram2::rules::Derivation::default();
    rewrite::diagram2::tactic::run(
        &mut after_graph,
        &mut deriv,
        &rewrite::diagram2::tactic::decide(),
    )
    .unwrap();
    let after: BTreeSet<usize> = after_graph.live().map(|(i, _)| i.index()).collect();
    let gone: Vec<usize> = before.difference(&after).copied().collect();
    let new: Vec<usize> = after.difference(&before).copied().collect();
    let mut bykind: BTreeMap<String, usize> = BTreeMap::new();
    for id in &gone {
        *bykind
            .entry(names[id].split(' ').next().unwrap().to_string())
            .or_default() += 1;
    }
    let mut bykind: Vec<_> = bykind.into_iter().collect();
    bykind.sort_by_key(|(k, n)| (Reverse(*n), k.clone()));
    println!(
        "\nafter `decide`: {} boxes → {}   ({} gone, {} new)",
        before.len(),
        after.len(),
        gone.len(),
        new.len()
    );
    println!(
        "  gone: {}",
        bykind
            .iter()
            .take(8)
            .map(|(k, n)| format!("{}×{}", n, k))
            .collect::<Vec<_>>()
            .join("  ")
    );
    println!(
        "  branches still standing: {}",
        after_graph
            .live()
            .filter(|(_, k)| matches!(k, NodeKind::Fork { .. }))
            .count()
    );
}
