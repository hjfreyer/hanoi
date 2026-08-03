//! The depth-gutter listing.

use bytecode::SentenceIndex;
use std::collections::HashSet;

use crate::arity::{node_arity, seq_arity};
use crate::ir::{build, Node};
use crate::program::Program;
use crate::stack::{self, Fresh, Names, Stack};
use crate::tactic::{apply, Env, Tactic, TacticError};

/// How wide the symbolic stack column is allowed to get.
const STACK_WIDTH: usize = 34;

/// Everything the stack view needs, threaded through the listing.
struct View<'a> {
    names: &'a mut Names,
    fresh: &'a mut Fresh,
}

/// Prints the listing. `Ok(true)` means the tactic *failed* — an aimed step
/// missed — and the listing shows the term as the rollback contract left it.
pub(crate) fn print_sentence(
    root: SentenceIndex,
    tactic: &Tactic,
    env: &Env,
    source: &str,
    show_stack: bool,
    positions: bool,
) -> Result<bool, TacticError> {
    let library = env.program().library();
    println!("#{} {}", usize::from(root), library.names[root]);
    for ann in &library.annotations[root] {
        println!("  {:?}", ann);
    }

    let mut in_progress = HashSet::new();
    let body = build(library, root, &mut in_progress);
    let outcome = apply(tactic, env, body)?;
    let failed = matches!(outcome, crate::tactic::Outcome::Failed(_));
    let body = outcome.into_nodes();

    // A sentence whose reckoning breaks immediately — a #[recursive] one, whose
    // body is a cut edge — has no knowable entry depth. Counting from zero
    // still shows every step's effect; the `+` marks the numbers as offsets.
    let (inputs, outputs) = seq_arity(env.program(), &body);
    let relative = outputs.is_none() && inputs == 0;

    println!();
    if source != "default" {
        println!("  tactic: {}", source);
    }

    let mut names = Names::new();
    let mut fresh = Fresh::new();
    let stack = show_stack.then(|| stack::entry(inputs, &mut fresh)).flatten();

    let head = if relative {
        "offset │ instruction   (entry depth unknown)"
    } else if positions {
        "depth │  at │ instruction"
    } else {
        "depth │ instruction"
    };
    if show_stack {
        println!("  {:>w$} │ {}", "stack", head, w = STACK_WIDTH);
        println!("  {}─┼─{}", "─".repeat(STACK_WIDTH), "─".repeat(24));
    } else {
        println!("  {}", head);
        println!("  {}┼────────────", if relative { "───────" } else { "──────" });
    }

    let mut view = show_stack.then_some(View {
        names: &mut names,
        fresh: &mut fresh,
    });
    print_seq(
        env.program(),
        &body,
        0,
        Some(inputs),
        relative,
        stack,
        view.as_mut(),
        positions,
    );

    if show_stack && !names.legend().is_empty() {
        println!();
        println!("  where");
        for (label, desc) in names.legend() {
            println!("    {:>3} = {}", label, desc);
        }
    }
    Ok(failed)
}

#[allow(clippy::too_many_arguments)]
fn print_seq(
    prog: &Program,
    nodes: &[Node],
    indent: usize,
    entry: Option<i64>,
    relative: bool,
    entry_stack: Stack,
    mut view: Option<&mut View>,
    positions: bool,
) {
    let mut depth = entry;
    let mut stack = entry_stack;
    let blank = " ".repeat(7);

    let pos_blank = if positions { " │    " } else { "" };

    for (ix, node) in nodes.iter().enumerate() {
        let gutter = match (depth, relative) {
            (Some(d), true) => format!("{:>7}", format!("{:+}", d)),
            (Some(d), false) => format!("{:>7}", d),
            (None, _) => format!("{:>7}", "?"),
        };
        // The index the aimed combinators speak: this node's position in its
        // own sequence, which is all `at(i, ...)` and `then_at(i, ...)` see.
        let gutter = if positions {
            format!("{} │ {:>3}", gutter, ix)
        } else {
            gutter
        };
        // The stack *before* this instruction, matching what `depth` means.
        let gutter = match view.as_deref_mut() {
            Some(v) => format!(
                "  {:>w$} │{}",
                v.names.render(&stack, STACK_WIDTH),
                gutter,
                w = STACK_WIDTH
            ),
            None => gutter,
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
                let inner = stack.as_ref().and_then(|s| {
                    (*k <= s.len()).then(|| s[..s.len() - k].to_vec())
                });
                print_seq(
                    prog,
                    body,
                    indent + 1,
                    depth,
                    relative,
                    inner,
                    view.as_deref_mut(),
                    positions,
                );
                println!("{}{}{} │ {}}}", stack_blank(&view), blank, pos_blank, pad);
            }
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            } => {
                // Both arms run on the stack with the condition popped.
                let arm_entry = depth.map(|d| d - 1);
                let arm_stack = stack.as_ref().and_then(|s| {
                    (!s.is_empty()).then(|| s[..s.len() - 1].to_vec())
                });
                println!("{} │ {}branch then → {} {{", gutter, pad, then_origin);
                print_seq(
                    prog,
                    then_body,
                    indent + 1,
                    arm_entry,
                    relative,
                    arm_stack.clone(),
                    view.as_deref_mut(),
                    positions,
                );
                println!(
                    "{}{}{} │ {}}} else → {} {{",
                    stack_blank(&view),
                    blank,
                    pos_blank,
                    pad,
                    else_origin
                );
                print_seq(
                    prog,
                    else_body,
                    indent + 1,
                    arm_entry,
                    relative,
                    arm_stack,
                    view.as_deref_mut(),
                    positions,
                );
                println!("{}{}{} │ {}}}", stack_blank(&view), blank, pos_blank, pad);
            }
            Node::Call { depth: k, target } => {
                let verb = if *k == 0 {
                    "jump".to_string()
                } else {
                    format!("dip {}", k)
                };
                println!("{} │ {}{} → {}", gutter, pad, verb, prog.label(*target));
            }
        }

        depth = match (depth, node_arity(prog, node)) {
            (Some(d), Some((n, m))) => Some(d - n + m),
            _ => None,
        };
        if let Some(v) = view.as_deref_mut() {
            stack = stack::step(prog, stack, node, v.fresh);
        }
    }
}

/// Blank filler for the stack column on a closing-brace line.
fn stack_blank(view: &Option<&mut View>) -> String {
    match view {
        Some(_) => format!("  {} │", " ".repeat(STACK_WIDTH)),
        None => String::new(),
    }
}

