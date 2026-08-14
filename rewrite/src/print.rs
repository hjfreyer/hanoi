//! The gutter listing: where each factor is, and how deep the stack is there.
//!
//! Two columns before the instruction. **Depth** is what the stack holds on the
//! way in, and **position** is the node's index in the sequence it belongs to —
//! which is the number `at(n, ...)` takes, and the number `then(n, t)` and its
//! relatives take when read off a `branch` or `par` line. Between them a window
//! a script prints as `[1.then, 2.left] @2` can be read straight off the
//! listing instead of counted out by hand.

use bytecode::SentenceIndex;

use crate::arity::{seq_arity, term_arity};
use crate::ir::{Term, id_word};
use crate::program::Program;
use crate::stack::{self, Fresh, Names, Stack};

/// How wide the symbolic stack column is allowed to get.
const STACK_WIDTH: usize = 34;

/// How wide the position column is. Three digits and a space, which covers a
/// sequence long enough that nobody is aiming into it by eye anyway.
const POS_WIDTH: usize = 4;

/// Everything the stack view needs, threaded through the listing.
struct View<'a> {
    names: &'a mut Names,
    fresh: &'a mut Fresh,
}

/// The position column: a node's index **in the sequence it belongs to**.
///
/// That is exactly the number `at(n, ...)` takes, and — read off a `branch` or
/// a `dip` line — the number `then(n, t)`, `else(n, t)` and `body(n, t)` take.
/// So a window a script prints as `[1.then, 2.left] @2` can be read straight
/// off the listing rather than counted out by hand.
///
/// It restarts at every nesting level, which the indentation is what shows.
/// A closing brace belongs to no node and is left blank.
fn pos_cell(show: bool, index: Option<usize>) -> String {
    if !show {
        return String::new();
    }
    match index {
        Some(i) => format!("{:>w$} │", i, w = POS_WIDTH),
        None => format!("{:>w$} │", "", w = POS_WIDTH),
    }
}

/// The same listing, as lines rather than as output.
///
/// The stepper diffs two of these against each other, which is the whole
/// reason the listing is built before it is printed: what one rule firing did
/// is a handful of lines in a tree that may be thousands long, and the way to
/// show that is to line the two listings up rather than to print both.
///
/// `show_pos` is what that diff turns off. A position is stable only while a
/// sequence keeps its length, and a splice renumbers every sibling after it —
/// so a firing that removed one node would report the whole rest of the
/// sequence as changed. Depth does not have that problem, since every equation
/// preserves the net stack effect of the window it rewrote, which is why the
/// gutter has always been safe to diff.
pub(crate) fn render_body(
    prog: &Program,
    root: SentenceIndex,
    body: &[Term],
    source: &str,
    show_stack: bool,
    show_pos: bool,
) -> Vec<String> {
    let library = prog.library();
    let mut out = Vec::new();
    out.push(format!("#{} {}", usize::from(root), library.names[root]));
    for ann in &library.annotations[root] {
        out.push(format!("  {:?}", ann));
    }
    out.push(String::new());
    if source != "default" {
        out.push(format!("  tactic: {}", source));
    }
    out.extend(render_nodes(prog, body, show_stack, show_pos, true));
    out
}

/// The listing alone, with no header.
///
/// Split out for the one comparison where a header would be noise: `prove`
/// diffs what a tactic reached against what an identity states, and those are
/// two different sentences with two different indices and names. Without the
/// split every failure diff would open with two lines that always differ,
/// burying the one that does not.
///
/// `show_origins` is the same problem one level down. A `<inline>` label says
/// which sentence phase 4 put a block in, and two identical blocks compiled
/// from two different sentences never share one — so a diff that showed them
/// would report every brace as a difference. Provenance is not part of a term's
/// identity, which is why `same_effect` ignores it, and a listing being
/// compared has to agree. A `Call`'s label stays either way: there the target
/// is the term.
pub(crate) fn render_nodes(
    prog: &Program,
    body: &[Term],
    show_stack: bool,
    show_pos: bool,
    show_origins: bool,
) -> Vec<String> {
    let mut out = Vec::new();

    // A sentence whose reckoning breaks immediately — one that opens on a call
    // whose target always panics — has no knowable entry depth. Counting from
    // zero still shows every step's effect; the `+` marks them as offsets.
    let (inputs, outputs) = seq_arity(prog, body);
    let relative = outputs.is_none() && inputs == 0;

    let mut names = Names::new();
    let mut fresh = Fresh::new();
    let stack = show_stack
        .then(|| stack::entry(inputs, &mut fresh))
        .flatten();

    // Padded to the width of a depth gutter, so the header's dividers sit over
    // the ones below it whether or not the stack column pushes them along.
    let head = if relative {
        format!("{:>7} │ instruction   (entry depth unknown)", "offset")
    } else {
        format!("{:>7} │ instruction", "depth")
    };
    let pos_head = if show_pos {
        format!("{:>w$} │", "pos", w = POS_WIDTH)
    } else {
        String::new()
    };
    let pos_rule = if show_pos {
        format!("{}┼", "─".repeat(POS_WIDTH + 1))
    } else {
        String::new()
    };
    // The rule line runs under the position column too, so the two-space lead
    // every other line carries becomes dashes there.
    let lead = if show_pos { "──" } else { "  " };
    if show_stack {
        out.push(format!(
            "{}  {:>w$} │{}",
            pos_head,
            "stack",
            head,
            w = STACK_WIDTH
        ));
        out.push(format!(
            "{}{}{}─┼─{}",
            pos_rule,
            lead,
            "─".repeat(STACK_WIDTH),
            "─".repeat(24)
        ));
    } else {
        out.push(format!("{}{}", pos_head, head));
        out.push(format!(
            "{}{}{}┼────────────",
            pos_rule,
            lead,
            if relative {
                "───────"
            } else {
                "──────"
            }
        ));
    }

    let mut view = show_stack.then_some(View {
        names: &mut names,
        fresh: &mut fresh,
    });
    render_seq(
        prog,
        body,
        0,
        Some(inputs),
        relative,
        stack,
        view.as_mut(),
        show_pos,
        show_origins,
        &mut out,
    );

    if show_stack && !names.legend().is_empty() {
        out.push(String::new());
        out.push("  where".to_string());
        for (label, desc) in names.legend() {
            out.push(format!("    {:>3} = {}", label, desc));
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn render_seq(
    prog: &Program,
    nodes: &[Term],
    indent: usize,
    entry: Option<i64>,
    relative: bool,
    entry_stack: Stack,
    mut view: Option<&mut View>,
    show_pos: bool,
    show_origins: bool,
    out: &mut Vec<String>,
) {
    let mut depth = entry;
    let mut stack = entry_stack;
    let blank = " ".repeat(7);
    // A closing brace belongs to no node, so its position cell is empty.
    let close =
        |view: &Option<&mut View>| format!("{}{}", pos_cell(show_pos, None), stack_blank(view));

    for (index, node) in nodes.iter().enumerate() {
        let gutter = match (depth, relative) {
            (Some(d), true) => format!("{:>7}", format!("{:+}", d)),
            (Some(d), false) => format!("{:>7}", d),
            (None, _) => format!("{:>7}", "?"),
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
        let gutter = format!("{}{}", pos_cell(show_pos, Some(index)), gutter);
        let pad = "  ".repeat(indent);

        match node {
            Term::Op(inst) => out.push(format!("{} │ {}{}", gutter, pad, inst)),
            Term::Id(k) => out.push(format!("{} │ {}{}", gutter, pad, id_word(*k))),
            Term::Call(target) => out.push(format!(
                "{} │ {}jump → {}",
                gutter,
                pad,
                prog.label(*target)
            )),
            // A composite is a spine, and a spine is what this function
            // prints — so it is flattened into the level it sits in rather
            // than indented. Nothing builds one here, since `render_seq` is
            // handed a spine, but a `par`'s sides are terms and may be.
            Term::Compose(..) => {
                let inner: Vec<Term> = node.spine().into_iter().cloned().collect();
                render_seq(
                    prog,
                    &inner,
                    indent,
                    depth,
                    relative,
                    stack.clone(),
                    view.as_deref_mut(),
                    show_pos,
                    show_origins,
                    out,
                );
            }
            Term::Par {
                origins,
                left,
                right,
            } => {
                // The right-hand side runs on the top of the stack and the left
                // on what is under it, so the carve is by the right's own input
                // arity — which for a frame is the width of its identity.
                let hidden = term_arity(prog, right).map(|(n, _)| n).unwrap_or(0);
                let hidden = usize::try_from(hidden).unwrap_or(0);
                // A wrapper level added by unary expansion has no origin of its
                // own; only the level holding the body names a sentence.
                let head = if origins.is_empty() || !show_origins {
                    "par".to_string()
                } else {
                    format!("par → {}", origins.join(" + "))
                };
                out.push(format!("{} │ {}{} {{", gutter, pad, head));
                // The left cannot reach the hidden values, but they are still
                // on the stack, so its entry depth is the same number the `par`
                // itself was printed with — which is what makes the window
                // visible.
                let inner = stack
                    .as_ref()
                    .and_then(|s| (hidden <= s.len()).then(|| s[..s.len() - hidden].to_vec()));
                render_seq(
                    prog,
                    &left.spine().into_iter().cloned().collect::<Vec<_>>(),
                    indent + 1,
                    depth,
                    relative,
                    inner,
                    view.as_deref_mut(),
                    show_pos,
                    show_origins,
                    out,
                );
                // An identity on the right is what a hidden window is, and it
                // is written on the closing line rather than opened up: three
                // lines to say `id 2` would bury every listing.
                match &**right {
                    Term::Id(k) => out.push(format!(
                        "{}{} │ {}}} {{ {} }}",
                        close(&view),
                        blank,
                        pad,
                        id_word(*k)
                    )),
                    other => {
                        out.push(format!("{}{} │ {}}} {{", close(&view), blank, pad));
                        let upper = stack.as_ref().and_then(|s| {
                            (hidden <= s.len()).then(|| s[s.len() - hidden..].to_vec())
                        });
                        render_seq(
                            prog,
                            &other.spine().into_iter().cloned().collect::<Vec<_>>(),
                            indent + 1,
                            Some(hidden as i64),
                            relative,
                            upper,
                            view.as_deref_mut(),
                            show_pos,
                            show_origins,
                            out,
                        );
                        out.push(format!("{}{} │ {}}}", close(&view), blank, pad));
                    }
                }
            }
            Term::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            } => {
                // Both arms run on the stack with the condition popped.
                let arm_entry = depth.map(|d| d - 1);
                let arm_stack = stack
                    .as_ref()
                    .and_then(|s| (!s.is_empty()).then(|| s[..s.len() - 1].to_vec()));
                out.push(if show_origins {
                    format!("{} │ {}branch then → {} {{", gutter, pad, then_origin)
                } else {
                    format!("{} │ {}branch then {{", gutter, pad)
                });
                render_seq(
                    prog,
                    &then_body.spine().into_iter().cloned().collect::<Vec<_>>(),
                    indent + 1,
                    arm_entry,
                    relative,
                    arm_stack.clone(),
                    view.as_deref_mut(),
                    show_pos,
                    show_origins,
                    out,
                );
                out.push(if show_origins {
                    format!(
                        "{}{} │ {}}} else → {} {{",
                        close(&view),
                        blank,
                        pad,
                        else_origin
                    )
                } else {
                    format!("{}{} │ {}}} else {{", close(&view), blank, pad)
                });
                render_seq(
                    prog,
                    &else_body.spine().into_iter().cloned().collect::<Vec<_>>(),
                    indent + 1,
                    arm_entry,
                    relative,
                    arm_stack,
                    view.as_deref_mut(),
                    show_pos,
                    show_origins,
                    out,
                );
                out.push(format!("{}{} │ {}}}", close(&view), blank, pad));
            }
        }

        depth = match (depth, term_arity(prog, node)) {
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
