//! The depth-gutter listing.

use bytecode::{Library, SentenceIndex};
use std::collections::HashSet;

use crate::arity::{node_arity, seq_arity};
use crate::ir::{build, Node};
use crate::passes::{expand_to_unary_dips, rewrite, Passes};


pub(crate) fn print_sentence(library: &Library, root: SentenceIndex, passes: Passes) {
    println!("#{} {}", usize::from(root), library.names[root]);
    for ann in &library.annotations[root] {
        println!("  {:?}", ann);
    }

    let mut in_progress = HashSet::new();
    let mut body = build(library, root, &mut in_progress);
    rewrite(&mut body, passes);
    if passes.dip_normalize {
        // Presentation only, and deliberately outside the fixpoint: see
        // `collapse_nested_dips`.
        expand_to_unary_dips(&mut body);
    }

    // A sentence whose reckoning breaks immediately — a #[recursive] one, whose
    // body is a cut edge — has no knowable entry depth. Counting from zero
    // still shows every step's effect; the `+` marks the numbers as offsets.
    let (inputs, outputs) = seq_arity(&body);
    let relative = outputs.is_none() && inputs == 0;

    println!();
    if passes.any() {
        println!("  ({})", passes.names().join("; "));
    }
    if relative {
        println!("  offset │ instruction   (entry depth unknown)");
        println!("  ───────┼────────────");
    } else {
        println!("  depth │ instruction");
        println!("  ──────┼────────────");
    }

    print_seq(&body, 0, Some(inputs), relative);
}

pub(crate) fn print_seq(nodes: &[Node], indent: usize, entry: Option<i64>, relative: bool) {
    let mut depth = entry;
    let blank = " ".repeat(7);

    for node in nodes {
        let gutter = match (depth, relative) {
            (Some(d), true) => format!("{:>7}", format!("{:+}", d)),
            (Some(d), false) => format!("{:>7}", d),
            (None, _) => format!("{:>7}", "?"),
        };
        let pad = "  ".repeat(indent);

        match node {
            Node::Op(inst) => println!("{} │ {}{}", gutter, pad, inst),
            Node::Dip {
                depth: k,
                origins,
                body,
            } => {
                let verb = if *k == 0 {
                    "jump".to_string()
                } else {
                    format!("dip {}", k)
                };
                // A wrapper level added by unary expansion has no origin of its
                // own; only the level holding the body names a sentence.
                let head = if origins.is_empty() {
                    verb
                } else {
                    format!("{} → {}", verb, origins.join(" + "))
                };
                println!("{} │ {}{} {{", gutter, pad, head);
                // The callee cannot reach the k dipped values, but they are
                // still on the stack, so the inner frame's entry depth is the
                // same number the dip itself was printed with — which is what
                // makes the hidden region visible.
                print_seq(body, indent + 1, depth, relative);
                println!("{} │ {}}}", blank, pad);
            }
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            } => {
                // Both arms run on the stack with the condition popped.
                let arm_entry = depth.map(|d| d - 1);
                println!("{} │ {}branch then → {} {{", gutter, pad, then_origin);
                print_seq(then_body, indent + 1, arm_entry, relative);
                println!("{} │ {}}} else → {} {{", blank, pad, else_origin);
                print_seq(else_body, indent + 1, arm_entry, relative);
                println!("{} │ {}}}", blank, pad);
            }
            Node::Cut(origin) => {
                println!("{} │ {}⟲ {} recursive, not inlined", gutter, pad, origin)
            }
        }

        depth = match (depth, node_arity(node)) {
            (Some(d), Some((n, m))) => Some(d - n + m),
            _ => None,
        };
    }
}

