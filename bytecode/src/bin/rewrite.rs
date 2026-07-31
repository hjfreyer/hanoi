//! Dumps one sentence's compiled bytecode with every call inlined — both `dip`
//! targets (which includes plain jumps, since `jump` is `Dip(0, s)`) and both
//! arms of every `branch`.
//!
//! Optional rewrite passes then run to a fixpoint over the result:
//! `--dip-normalize` pushes dips left, fuses them, and splits them into nests
//! of unary `dip 1`s; `--factor-branches` hoists a run shared by both arms of
//! a branch out in front of it; `--annihilate` cancels a drop against the
//! instruction that produced what it drops. These are the rewrites an
//! optimizer would want to do, and this tool exists to let you eyeball them.
//!
//! This is a debugging aid, not a source generator: the output does not parse,
//! because a dipped block operates below its hidden region and so cannot be
//! spliced into the enclosing instruction stream as-is. What it gives you is
//! the whole call tree in one listing instead of a set of `SentenceIndex`
//! references to chase by hand.

use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::Path;
use std::process;

use bytecode::{Instruction, Library, SentenceIndex};

fn main() {
    let mut passes = Passes::default();
    let mut positional: Vec<String> = Vec::new();
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "--dip-normalize" => passes.dip_normalize = true,
            "--factor-branches" => passes.factor_branches = true,
            "--annihilate" => passes.annihilate = true,
            flag if flag.starts_with("--") => {
                eprintln!("Unknown flag: {}", flag);
                process::exit(1);
            }
            _ => positional.push(arg),
        }
    }

    if positional.len() != 2 {
        eprintln!("Usage: rewrite <directory> <sentence> [passes...]");
        eprintln!();
        eprintln!("  <sentence> is a fully qualified name (queue::queue::accept), a");
        eprintln!("  unique trailing part of one (queue::accept), or an index (#12).");
        eprintln!();
        eprintln!("  --dip-normalize   move dips as far left as they will go, fuse");
        eprintln!("                    adjacent dips that end up at the same depth,");
        eprintln!("                    then split each one into a nest of `dip 1`s.");
        eprintln!("  --factor-branches hoist a run of instructions shared by both");
        eprintln!("                    arms of a branch out in front of it.");
        eprintln!("  --annihilate      cancel a drop against the instruction that");
        eprintln!("                    produced the value it drops.");
        eprintln!();
        eprintln!("  Passes compose: each one's output is fed back to the others.");
        process::exit(1);
    }

    let library = load(&positional[0]);
    let root = match resolve_sentence(&library, &positional[1]) {
        Ok(idx) => idx,
        Err(err) => {
            eprintln!("{}", err);
            process::exit(1);
        }
    };

    print_sentence(&library, root, passes);
}

fn load(dir_arg: &str) -> Library {
    let dir = Path::new(dir_arg);
    if !dir.is_dir() {
        eprintln!("Error: '{}' is not a directory", dir_arg);
        process::exit(1);
    }

    let file_path = dir.join("main.hana");
    if !file_path.exists() {
        eprintln!("Error: Directory '{}' does not contain 'main.hana'", dir_arg);
        process::exit(1);
    }

    let code = match fs::read_to_string(&file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error reading '{}': {}", file_path.display(), err);
            process::exit(1);
        }
    };

    match bytecode::assemble_with_path(&code, file_path.parent()) {
        Ok(lib) => lib,
        Err(err) => {
            eprintln!("Assembly FAILED for '{}':\n{}", file_path.display(), err);
            process::exit(1);
        }
    }
}

/// Accepts an index (`#12` or `12`), an exact name, or an unambiguous suffix.
fn resolve_sentence(library: &Library, ident: &str) -> Result<SentenceIndex, String> {
    let numeric = ident.strip_prefix('#').unwrap_or(ident);
    if let Ok(raw) = numeric.parse::<usize>() {
        if raw >= library.sentences.len() {
            return Err(format!(
                "No sentence #{}: the library has {}",
                raw,
                library.sentences.len()
            ));
        }
        return Ok(SentenceIndex::from(raw));
    }

    let exact: Vec<SentenceIndex> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| *name == ident)
        .map(|(idx, _)| idx)
        .collect();
    if exact.len() == 1 {
        return Ok(exact[0]);
    }
    if exact.len() > 1 {
        return Err(format!("'{}' is ambiguous: {}", ident, render_candidates(library, &exact)));
    }

    // Fall back to a trailing path match, so `queue::accept` finds
    // `queue::queue::accept` without spelling out every segment.
    let suffix = format!("::{}", ident);
    let matches: Vec<SentenceIndex> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| name.ends_with(&suffix))
        .map(|(idx, _)| idx)
        .collect();

    match matches.len() {
        1 => Ok(matches[0]),
        0 => Err(format!(
            "No sentence matching '{}'. Named sentences:\n{}",
            ident,
            named_sentence_list(library)
        )),
        _ => Err(format!(
            "'{}' is ambiguous: {}",
            ident,
            render_candidates(library, &matches)
        )),
    }
}

/// The most a listing prints before it stops being an aid and starts being a
/// wall; `check` alone matches nearly sixty sentences in the test corpus.
const MAX_LISTED: usize = 15;

fn render_candidates(library: &Library, candidates: &[SentenceIndex]) -> String {
    let mut out = String::from("\n");
    for idx in candidates.iter().take(MAX_LISTED) {
        out.push_str(&format!("  #{:<5} {}\n", usize::from(*idx), library.names[*idx]));
    }
    if candidates.len() > MAX_LISTED {
        out.push_str(&format!("  ... and {} more\n", candidates.len() - MAX_LISTED));
    }
    out
}

fn named_sentence_list(library: &Library) -> String {
    let mut named: Vec<(&str, SentenceIndex)> = library
        .names
        .iter_enumerated()
        .filter(|(_, name)| *name != "<inline>")
        .map(|(idx, name)| (name.as_str(), idx))
        .collect();
    named.sort();

    let total = named.len();
    let mut out: Vec<String> = named
        .into_iter()
        .take(MAX_LISTED)
        .map(|(name, idx)| format!("  #{:<5} {}", usize::from(idx), name))
        .collect();
    if total > MAX_LISTED {
        out.push(format!("  ... and {} more", total - MAX_LISTED));
    }
    out.join("\n")
}

// ---------------------------------------------------------------------------
// The inlined tree
// ---------------------------------------------------------------------------

/// One step of an inlined listing.
///
/// Calls have already been resolved into nested bodies, so nothing here refers
/// to a `SentenceIndex` except as a label. That is what lets arities be
/// computed structurally and dips be moved around without consulting the
/// library.
#[derive(Debug, Clone, PartialEq)]
enum Node {
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

fn build(library: &Library, s_idx: SentenceIndex, in_progress: &mut HashSet<SentenceIndex>) -> Vec<Node> {
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

fn build_target(
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

fn label(library: &Library, target: SentenceIndex) -> String {
    format!("#{} {}", usize::from(target), library.names[target])
}

// ---------------------------------------------------------------------------
// Arities
// ---------------------------------------------------------------------------

/// How many values a node takes off the stack and leaves on it, counted from
/// the top. `None` means the node ends or breaks the static reckoning: a panic
/// runs nothing after it, and a cut edge's body was never expanded.
fn node_arity(node: &Node) -> Option<(i64, i64)> {
    match node {
        Node::Op(inst) => op_arity(inst),
        Node::Dip { depth, body, .. } => {
            let (n, m) = full_arity(body)?;
            let d = *depth as i64;
            Some((d + n, d + m))
        }
        Node::Branch {
            then_body,
            else_body,
            ..
        } => {
            // The arity checker requires both arms to agree on net change, so
            // whichever arm is statically known answers for both. The extra
            // input is the condition.
            let (n, m) = full_arity(then_body).or_else(|| full_arity(else_body))?;
            Some((n + 1, m))
        }
        Node::Cut(_) => None,
    }
}

fn op_arity(inst: &Instruction) -> Option<(i64, i64)> {
    Some(match inst {
        Instruction::Push(_) => (0, 1),
        Instruction::Drop => (1, 0),
        // Pick reads at `d` and copies it to the top, so it touches everything
        // down to that depth even though it consumes nothing.
        Instruction::Pick(d) => (*d as i64 + 1, *d as i64 + 2),
        Instruction::Roll(d) => (*d as i64 + 1, *d as i64 + 1),
        Instruction::Equal
        | Instruction::Greater
        | Instruction::Less
        | Instruction::Add
        | Instruction::Subtract
        | Instruction::Multiply
        | Instruction::Divide
        | Instruction::Modulo
        | Instruction::And
        | Instruction::Or
        | Instruction::SymbolCharAt => (2, 1),
        Instruction::Not
        | Instruction::Negate
        | Instruction::Print
        | Instruction::SymbolLen
        | Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
        | Instruction::IsSymbol
        | Instruction::IsTuple
        | Instruction::TupleLength => (1, 1),
        Instruction::Assert => (1, 0),
        Instruction::AssertEqual => (2, 0),
        Instruction::Tuple(n) => (*n as i64, 1),
        Instruction::Untuple(n) => (1, *n as i64),
        Instruction::Panic => return None,
        // Calls are Nodes, never Ops.
        Instruction::Dip(..) | Instruction::Branch(..) => return None,
    })
}

/// `(inputs, outputs)` for a whole sequence, by the same accumulation the arity
/// checker uses: a requirement discovered late grows the input count.
///
/// Inputs are always reported, since the prefix before an unknown node still
/// tells you how deep the sequence reaches. Outputs stop at the first node
/// whose arity is unknown.
/// [`seq_arity`] when the whole sequence is statically known, which is what a
/// node's own arity needs — a body that stops partway has no output count.
fn full_arity(nodes: &[Node]) -> Option<(i64, i64)> {
    let (inputs, outputs) = seq_arity(nodes);
    Some((inputs, outputs?))
}

fn seq_arity(nodes: &[Node]) -> (i64, Option<i64>) {
    let mut inputs = 0i64;
    let mut size = 0i64;
    for node in nodes {
        let Some((n, m)) = node_arity(node) else {
            return (inputs, None);
        };
        if size < n {
            inputs += n - size;
            size = n;
        }
        size = size - n + m;
    }
    (inputs, Some(size))
}

// ---------------------------------------------------------------------------
// Rewriting
// ---------------------------------------------------------------------------

/// Which rewrites to apply. They compose, so each one's output is fed back to
/// the others until nothing more fires.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
struct Passes {
    dip_normalize: bool,
    factor_branches: bool,
    annihilate: bool,
}

impl Passes {
    fn any(&self) -> bool {
        self.dip_normalize || self.factor_branches || self.annihilate
    }

    fn names(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        if self.annihilate {
            out.push("drops annihilated");
        }
        if self.factor_branches {
            out.push("branch prefixes factored out");
        }
        if self.dip_normalize {
            out.push("dips moved left, fused, and split into unary dips");
        }
        out
    }
}

/// Applies the enabled rewrites, and everything they make possible, to a
/// fixpoint over the whole subtree.
///
/// Each pass strictly decreases one of: the nodes held inside branch arms, the
/// node count, or the summed positions of dips. So the loop terminates, and
/// running the passes together rather than in sequence lets one pass expose
/// work for another — factoring a branch produces a dip that then sinks,
/// annihilating a drop can expose a new shared prefix.
fn rewrite(nodes: &mut Vec<Node>, passes: Passes) -> bool {
    let mut ever_changed = false;
    loop {
        let mut changed = false;

        // Innermost first, so an inner rewrite is already settled by the time
        // an outer one asks for its arity.
        for node in nodes.iter_mut() {
            changed |= match node {
                Node::Dip { body, .. } => rewrite(body, passes),
                Node::Branch {
                    then_body,
                    else_body,
                    ..
                } => {
                    let then_changed = rewrite(then_body, passes);
                    let else_changed = rewrite(else_body, passes);
                    then_changed || else_changed
                }
                Node::Op(_) | Node::Cut(_) => false,
            };
        }

        if passes.annihilate {
            changed |= annihilate_drops(nodes);
        }
        if passes.factor_branches {
            changed |= factor_branches(nodes);
        }
        if passes.dip_normalize {
            changed |= collapse_nested_dips(nodes);
            changed |= sink_dips_left(nodes);
            changed |= fuse_adjacent_dips(nodes);
        }

        if !changed {
            return ever_changed;
        }
        ever_changed = true;
    }
}

/// Hoists a run of instructions shared by both arms of a branch out in front
/// of it.
///
/// `branch { X A } { X B }` is `dip 1 { X }; branch { A } { B }`. X runs the
/// same way whichever arm is taken, so it can run before the condition is
/// consumed — but only under a dip, because at that point the condition is
/// still sitting on top of the stack and X must not be handed it.
fn factor_branches(nodes: &mut Vec<Node>) -> bool {
    let mut changed = false;
    let mut i = 0;

    while i < nodes.len() {
        let shared = {
            let Node::Branch {
                then_body,
                else_body,
                ..
            } = &mut nodes[i]
            else {
                i += 1;
                continue;
            };

            let mut shared = Vec::new();
            while let (Some(a), Some(b)) = (then_body.first(), else_body.first()) {
                // A cut edge stands for a body that was never expanded, so two
                // of them comparing equal says nothing about the code inside.
                if a != b || matches!(a, Node::Cut(_)) {
                    break;
                }
                else_body.remove(0);
                shared.push(then_body.remove(0));
            }
            shared
        };

        if shared.is_empty() {
            i += 1;
            continue;
        }

        nodes.insert(
            i,
            Node::Dip {
                depth: 1,
                origins: Vec::new(),
                body: shared,
            },
        );
        changed = true;
        // Step over both the dip just inserted and the branch it came from.
        i += 2;
    }

    changed
}

/// What cancelling a `drop` against the instruction before it leaves behind.
enum Annihilation {
    /// Both instructions go: the predecessor produced exactly what was dropped.
    Both,
    /// Only the predecessor goes: it consumed a value to make the dropped one,
    /// so the drop stays and takes its input instead.
    Predecessor,
}

/// Cancels a drop against the instruction that produced the value it drops.
///
/// Only instructions that cannot panic qualify. `add` also produces one value
/// from the top of the stack, but `add; drop` is not `drop; drop` — the add
/// still rejects non-numeric operands, and dropping the operands unchecked
/// would throw that away.
fn annihilate_drops(nodes: &mut Vec<Node>) -> bool {
    let mut changed = false;
    let mut i = 0;

    while i < nodes.len() {
        if i == 0 || !matches!(nodes[i], Node::Op(Instruction::Drop)) {
            i += 1;
            continue;
        }
        let Node::Op(prev) = &nodes[i - 1] else {
            i += 1;
            continue;
        };

        match annihilation(prev) {
            Some(Annihilation::Both) => {
                nodes.remove(i);
                nodes.remove(i - 1);
                i -= 1;
                changed = true;
            }
            Some(Annihilation::Predecessor) => {
                nodes.remove(i - 1);
                // The drop has slid down into the vacated slot; look at it
                // again, since its new predecessor may cancel too.
                i -= 1;
                changed = true;
            }
            None => i += 1,
        }
    }

    changed
}

fn annihilation(inst: &Instruction) -> Option<Annihilation> {
    match inst {
        // Neither can fail once the arity checker has passed, and each leaves
        // exactly the value the drop removes.
        Instruction::Push(_) | Instruction::Pick(_) => Some(Annihilation::Both),
        // Total, but each consumes a value to produce the dropped one.
        Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
        | Instruction::IsSymbol
        | Instruction::IsTuple => Some(Annihilation::Predecessor),
        _ => None,
    }
}

/// Flattens `dip k { dip j { B } }` into `dip (k + j) { B }`.
///
/// Hiding k and then hiding j more of what is left is hiding k + j, so a dip
/// whose whole body is another dip is a nesting level that says nothing. This
/// is what lets an inner dip keep sinking after its wrapper has moved.
///
/// [`expand_to_unary_dips`] runs this backwards, and the two are not in
/// conflict: the interchange rule tests a dip's *total* hidden depth, so
/// normalization has to work on collapsed dips or it gives up sinking power
/// it is entitled to. Unary form is how the result is presented, not how it
/// is reasoned about, so the expansion happens once at the end and never
/// re-enters the fixpoint.
fn collapse_nested_dips(nodes: &mut [Node]) -> bool {
    let mut changed = false;
    for node in nodes.iter_mut() {
        while collapse_one(node) {
            changed = true;
        }
    }
    changed
}

fn collapse_one(node: &mut Node) -> bool {
    let Node::Dip {
        depth,
        origins,
        body,
    } = node
    else {
        return false;
    };
    if body.len() != 1 || !matches!(body[0], Node::Dip { .. }) {
        return false;
    }

    let Node::Dip {
        depth: inner_depth,
        origins: inner_origins,
        body: inner_body,
    } = body.remove(0)
    else {
        unreachable!("checked above")
    };
    *depth += inner_depth;
    origins.extend(inner_origins);
    *body = inner_body;
    true
}

/// Moves every dip as far left as the interchange rule allows.
fn sink_dips_left(nodes: &mut [Node]) -> bool {
    let mut changed = false;
    for i in 0..nodes.len() {
        if !matches!(nodes[i], Node::Dip { .. }) {
            continue;
        }
        let mut at = i;
        while at > 0 {
            let Some(depth) = dip_depth(&nodes[at]) else {
                break;
            };
            let Some(new_depth) = swapped_depth(&nodes[at - 1], depth) else {
                break;
            };
            if let Node::Dip { depth, .. } = &mut nodes[at] {
                *depth = new_depth;
            }
            nodes.swap(at - 1, at);
            at -= 1;
            changed = true;
        }
    }
    changed
}

/// The depth a dip takes on when moved left past `prev`, if that is legal.
///
/// Writing `prev`'s arity as `(n -> m)`, the dip's window has to sit entirely
/// below everything `prev` leaves behind — that is `k >= m` — and the same
/// window is `k - m + n` deep on the other side of it.
fn swapped_depth(prev: &Node, depth: usize) -> Option<usize> {
    let (n, m) = node_arity(prev)?;
    let k = depth as i64;
    if k < m {
        return None;
    }
    let shifted = k - m + n;
    // A dip cannot hide a negative number of values; the arity table keeps
    // this non-negative, but the tool should not trust it blindly.
    usize::try_from(shifted).ok()
}

fn dip_depth(node: &Node) -> Option<usize> {
    match node {
        Node::Dip { depth, .. } => Some(*depth),
        _ => None,
    }
}

/// Fuses neighbouring dips that hide the same number of values.
///
/// `dip k {A}; dip k {B}` is `dip k {A B}`: the second hides exactly what the
/// first restored, so the region can just stay hidden across both.
fn fuse_adjacent_dips(nodes: &mut Vec<Node>) -> bool {
    let mut i = 0;
    let mut changed = false;
    while i + 1 < nodes.len() {
        let fusable = match (&nodes[i], &nodes[i + 1]) {
            (Node::Dip { depth: a, .. }, Node::Dip { depth: b, .. }) => a == b,
            _ => false,
        };
        if !fusable {
            i += 1;
            continue;
        }

        let Node::Dip {
            origins: next_origins,
            body: next_body,
            ..
        } = nodes.remove(i + 1)
        else {
            unreachable!("checked above")
        };
        if let Node::Dip { origins, body, .. } = &mut nodes[i] {
            origins.extend(next_origins);
            body.extend(next_body);
            // The concatenation can expose fusions and moves of its own; the
            // fixpoint in `rewrite` picks those up on its next turn.
        }
        changed = true;
    }
    changed
}

/// Rewrites every `dip k` with `k >= 2` into `k` nested `dip 1`s.
///
/// The inverse of [`collapse_nested_dips`], run once after normalization has
/// settled. A nest of unary dips is the same hidden region written in unary:
/// each level holds exactly one value out of reach, which is the classic `dip`
/// combinator and the form worth reading a normalized listing in.
///
/// `dip 0` is left alone — it hides nothing and is a plain call.
fn expand_to_unary_dips(nodes: &mut [Node]) {
    for node in nodes.iter_mut() {
        expand_node(node);
    }
}

fn expand_node(node: &mut Node) {
    match node {
        Node::Dip {
            depth,
            origins,
            body,
        } => {
            expand_to_unary_dips(body);
            if *depth < 2 {
                return;
            }
            let levels = *depth;

            // The innermost level keeps the origin, so the arrow points at the
            // block whose body is actually shown; the wrappers it gains are
            // bookkeeping and say nothing about where the code came from.
            let mut nest = Node::Dip {
                depth: 1,
                origins: std::mem::take(origins),
                body: std::mem::take(body),
            };
            for _ in 1..levels {
                nest = Node::Dip {
                    depth: 1,
                    origins: Vec::new(),
                    body: vec![nest],
                };
            }
            *node = nest;
        }
        Node::Branch {
            then_body,
            else_body,
            ..
        } => {
            expand_to_unary_dips(then_body);
            expand_to_unary_dips(else_body);
        }
        Node::Op(_) | Node::Cut(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

fn print_sentence(library: &Library, root: SentenceIndex, passes: Passes) {
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

fn print_seq(nodes: &[Node], indent: usize, entry: Option<i64>, relative: bool) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::assemble;

    const DIPS: Passes = Passes {
        dip_normalize: true,
        factor_branches: false,
        annihilate: false,
    };

    const FACTOR: Passes = Passes {
        dip_normalize: false,
        factor_branches: true,
        annihilate: false,
    };

    const ANNIHILATE: Passes = Passes {
        dip_normalize: false,
        factor_branches: false,
        annihilate: true,
    };

    const ALL: Passes = Passes {
        dip_normalize: true,
        factor_branches: true,
        annihilate: true,
    };

    /// Net stack change, which every pass must preserve exactly.
    fn net(nodes: &[Node]) -> Option<i64> {
        let (inputs, outputs) = seq_arity(nodes);
        outputs.map(|o| o - inputs)
    }

    fn tree(code: &str, passes: Passes) -> Vec<Node> {
        let library = assemble(code).unwrap();
        let mut body = build(&library, SentenceIndex::from(0), &mut HashSet::new());
        rewrite(&mut body, passes);
        body
    }

    /// The depth before each instruction of a sequence, entered at its inputs.
    fn depths(nodes: &[Node]) -> Vec<Option<i64>> {
        let mut depth = Some(seq_arity(nodes).0);
        let mut out = Vec::new();
        for node in nodes {
            out.push(depth);
            depth = match (depth, node_arity(node)) {
                (Some(d), Some((n, m))) => Some(d - n + m),
                _ => None,
            };
        }
        out
    }

    fn shape(nodes: &[Node]) -> Vec<String> {
        nodes
            .iter()
            .map(|node| match node {
                Node::Op(inst) => format!("{}", inst),
                Node::Dip { depth, body, .. } => {
                    format!("dip {} {{ {} }}", depth, shape(body).join(" "))
                }
                Node::Branch { .. } => "branch".to_string(),
                Node::Cut(_) => "cut".to_string(),
            })
            .collect()
    }

    #[test]
    fn depth_counts_inputs_once() {
        // Regression: an earlier version read the arity checker's recorded
        // per-instruction size, which already includes the inputs found so far,
        // and added the total back on — reporting `is_tuple` one deeper than it
        // runs.
        let body = tree(
            r#"
            #[arity(1, 1)]
            sentence probe {
                pick 0
                is_tuple
                and
            }
        "#,
            Passes::default(),
        );
        assert_eq!(depths(&body), vec![Some(1), Some(2), Some(2)]);
    }

    #[test]
    fn dip_contributes_only_its_targets_net_change() {
        let body = tree(
            r#"
            #[arity(3, 1)]
            sentence probe {
                dip 1 { add }
                drop 0
            }
        "#,
            Passes::default(),
        );
        assert_eq!(depths(&body), vec![Some(3), Some(2)]);
        // The dip itself takes three and leaves two: two consumed by the add,
        // plus the one it holds out of the way.
        assert_eq!(node_arity(&body[0]), Some((3, 2)));
    }

    #[test]
    fn depth_stops_being_known_after_a_panic() {
        let body = tree(
            r#"
            #[arity(0, 0)]
            sentence probe {
                push 1
                panic
                push 2
            }
        "#,
            Passes::default(),
        );
        assert_eq!(depths(&body), vec![Some(0), Some(1), None]);
    }

    #[test]
    fn a_cycle_has_no_static_arity() {
        let body = tree(
            r#"
            #[recursive]
            sentence loops {
                push 1
                jump loops
            }
        "#,
            Passes::default(),
        );
        assert_eq!(seq_arity(&body).1, None);
    }

    #[test]
    fn dips_sink_past_pushes_and_arithmetic() {
        // The dip starts at the end hiding one value. Moving it past `add`
        // widens it to two operands, and past each push narrows it again, so it
        // arrives at the front hiding nothing at all.
        let body = tree(
            r#"
            #[arity(2, 2)]
            sentence probe {
                push 1
                push 2
                add
                dip 1 { add }
            }
        "#,
            DIPS,
        );
        assert_eq!(
            shape(&body),
            vec!["dip 0 { add }", "push 1", "push 2", "add"]
        );
    }

    #[test]
    fn dips_fuse_when_they_meet_at_the_same_depth() {
        let body = tree(
            r#"
            #[arity(3, 3)]
            sentence probe {
                dip 1 { pick 0 drop 0 }
                dip 1 { pick 0 drop 0 }
            }
        "#,
            DIPS,
        );
        assert_eq!(
            shape(&body),
            vec!["dip 1 { pick 0 drop pick 0 drop }"]
        );
    }

    fn tree_unary(code: &str) -> Vec<Node> {
        let mut body = tree(code, DIPS);
        expand_to_unary_dips(&mut body);
        body
    }

    #[test]
    fn a_deep_dip_becomes_a_nest_of_unary_dips() {
        // `untuple 3` leaves three values, so a dip hiding two cannot clear it
        // and stays put — which is what makes this a case where the expansion
        // has something to do.
        let body = tree_unary(
            r#"
            sentence probe {
                untuple 3
                dip 2 { add }
            }
        "#,
        );
        assert_eq!(
            shape(&body),
            vec!["untuple 3", "dip 1 { dip 1 { add } }"]
        );
    }

    #[test]
    fn expansion_leaves_plain_calls_alone() {
        // `dip 0` hides nothing, so there is no unary nest to write it as.
        let body = tree_unary(
            r#"
            sentence probe {
                push 1
                push 2
                dip 0 { add }
            }
        "#,
        );
        assert_eq!(shape(&body), vec!["push 1", "push 2", "dip 0 { add }"]);
    }

    #[test]
    fn expansion_preserves_arity() {
        let code = r#"
            sentence probe {
                untuple 3
                dip 2 { add }
            }
        "#;
        let normalized = tree(code, DIPS);
        let unary = tree_unary(code);
        assert_ne!(shape(&normalized), shape(&unary), "expected an expansion");
        assert_eq!(seq_arity(&normalized), seq_arity(&unary));
    }

    #[test]
    fn nested_dips_collapse_and_then_keep_sinking() {
        // Hiding one and then one more is hiding two, and once that is a single
        // dip it sinks past both of the pushes it was reaching over.
        //
        // It stops at `push 2`: by then it has narrowed to `dip 0`, which is a
        // plain call taking its argument off the top — exactly the value that
        // push put there. That is the rule's `k >= m` biting, and it is the
        // point at which the dip has reached the values it actually operates on.
        let body = tree(
            r#"
            sentence probe {
                push 1
                push 2
                push 8
                push 9
                dip 1 { dip 1 { add } }
            }
        "#,
            DIPS,
        );
        assert_eq!(
            shape(&body),
            vec!["push 1", "push 2", "dip 0 { add }", "push 8", "push 9"]
        );
    }

    #[test]
    fn fusing_records_every_origin() {
        let library = assemble(
            r#"
            sentence probe {
                push 1
                push 2
                push 8
                push 9
                dip 1 { dip 1 { add } }
            }
        "#,
        )
        .unwrap();
        let mut body = build(&library, SentenceIndex::from(0), &mut HashSet::new());
        rewrite(&mut body, DIPS);

        let origins = body
            .iter()
            .find_map(|node| match node {
                Node::Dip { origins, .. } => Some(origins),
                _ => None,
            })
            .expect("a dip should survive normalization");
        // Both of the sentences that were collapsed together are named, so the
        // listing still says where the merged block came from.
        assert_eq!(origins.len(), 2);
    }

    #[test]
    fn a_dip_stops_at_a_pick_that_reaches_into_it() {
        // `pick 2` reads three deep, so a dip hiding only one value would be
        // rewriting the very slot the pick copies from. It has to stay put.
        let body = tree(
            r#"
            sentence probe {
                pick 2
                dip 1 { pick 0 }
            }
        "#,
            DIPS,
        );
        assert_eq!(shape(&body), vec!["pick 2", "dip 1 { pick 0 }"]);
    }

    #[test]
    fn a_dip_sinks_past_a_pick_it_clears() {
        // Same shape, but hiding four values puts the whole pick above the
        // window, so the move is sound.
        let body = tree(
            r#"
            sentence probe {
                pick 2
                dip 4 { pick 0 }
            }
        "#,
            DIPS,
        );
        assert_eq!(shape(&body), vec!["dip 3 { pick 0 }", "pick 2"]);
    }

    #[test]
    fn a_shared_branch_prefix_is_hoisted_under_a_dip() {
        // The `push 7` runs either way, so it can run before the condition is
        // consumed — under a dip, since the condition is still on top.
        let body = tree(
            r#"
            sentence probe {
                branch { push 7 push 1 } { push 7 push 2 }
            }
        "#,
            FACTOR,
        );
        assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
    }

    #[test]
    fn factoring_takes_the_whole_shared_run() {
        let body = tree(
            r#"
            sentence probe {
                branch { push 7 is_int push 1 } { push 7 is_int push 2 }
            }
        "#,
            FACTOR,
        );
        assert_eq!(shape(&body), vec!["dip 1 { push 7 is_int }", "branch"]);
    }

    #[test]
    fn factoring_stops_where_the_arms_diverge() {
        // Both arms also end with `push 5`, but only the prefix is hoistable:
        // what runs before the branch has to run before *both* arms, and the
        // trailing pushes are separated by instructions that differ.
        let body = tree(
            r#"
            sentence probe {
                branch { push 7 push 1 push 5 } { push 7 push 2 push 5 }
            }
        "#,
            FACTOR,
        );
        assert_eq!(shape(&body), vec!["dip 1 { push 7 }", "branch"]);
        let Node::Branch {
            then_body,
            else_body,
            ..
        } = &body[1]
        else {
            panic!("expected a branch")
        };
        assert_eq!(shape(then_body), vec!["push 1", "push 5"]);
        assert_eq!(shape(else_body), vec!["push 2", "push 5"]);
    }

    #[test]
    fn a_push_and_a_drop_cancel() {
        let body = tree(
            r#"
            sentence probe {
                push 1
                push 2
                drop 0
                drop 0
            }
        "#,
            ANNIHILATE,
        );
        // Cancelling the inner pair exposes the outer one.
        assert!(body.is_empty(), "expected nothing left, got {:?}", shape(&body));
    }

    #[test]
    fn a_pick_and_a_drop_cancel() {
        let body = tree(
            r#"
            sentence probe {
                pick 1
                drop 0
                add
            }
        "#,
            ANNIHILATE,
        );
        assert_eq!(shape(&body), vec!["add"]);
    }

    #[test]
    fn a_type_test_leaves_the_drop_behind() {
        // `is_int` consumes a value to make the one being dropped, so the drop
        // still has to happen — it just takes the input instead.
        let body = tree(
            r#"
            sentence probe {
                is_int
                drop 0
            }
        "#,
            ANNIHILATE,
        );
        assert_eq!(shape(&body), vec!["drop"]);
    }

    #[test]
    fn a_partial_instruction_is_not_annihilated() {
        // `add; drop` is not `drop; drop`: the add still rejects non-numeric
        // operands, and cancelling it would discard that check.
        let body = tree(
            r#"
            sentence probe {
                add
                drop 0
            }
        "#,
            ANNIHILATE,
        );
        assert_eq!(shape(&body), vec!["add", "drop"]);
    }

    #[test]
    fn passes_compose() {
        // Annihilating the push/drop pair leaves `push 7` shared by both arms,
        // which factoring then hoists — neither pass alone gets there.
        let code = r#"
            sentence probe {
                branch { push 7 push 9 drop 0 push 1 } { push 7 push 2 }
            }
        "#;
        assert_eq!(shape(&tree(code, FACTOR)), vec!["dip 1 { push 7 }", "branch"]);

        let both = tree(
            code,
            Passes {
                factor_branches: true,
                annihilate: true,
                dip_normalize: false,
            },
        );
        let Node::Branch { then_body, .. } = &both[1] else {
            panic!("expected a branch")
        };
        assert_eq!(shape(&both), vec!["dip 1 { push 7 }", "branch"]);
        assert_eq!(shape(then_body), vec!["push 1"]);
    }

    /// The rewrites must not change what a sentence does. Arity is the part of
    /// that this tool can check for itself, and running it over every sentence
    /// in the real corpus exercises far more instruction sequences than the
    /// hand-written cases above.
    ///
    /// Two different invariants are at play:
    ///
    /// - Net change is preserved by every pass, exactly.
    /// - The *input requirement* is preserved by the dip passes and by
    ///   factoring, but `--annihilate` may lower it: dropping `pick 2; drop`
    ///   also drops the demand for three values that only the `pick` made. The
    ///   rewritten code is defined on strictly more stacks than the original,
    ///   which is sound — so the bound is one-directional, not an equality.
    #[test]
    fn rewrites_preserve_arity_across_the_corpus() {
        // Tests run with the package root as the working directory.
        let main = Path::new("../tests/main.hana");
        let code = match fs::read_to_string(main) {
            Ok(code) => code,
            // Not a failure: the crate should still be testable on its own.
            Err(_) => return,
        };
        let library = bytecode::assemble_with_path(&code, main.parent()).unwrap();

        let mut checked = 0;
        for (s_idx, _) in library.names.iter_enumerated() {
            let plain = build(&library, s_idx, &mut HashSet::new());
            let name = || format!("#{} {}", usize::from(s_idx), library.names[s_idx]);

            // The dip passes and factoring preserve arity outright.
            for passes in [DIPS, FACTOR] {
                let mut rewritten = plain.clone();
                rewrite(&mut rewritten, passes);
                assert_eq!(
                    seq_arity(&plain),
                    seq_arity(&rewritten),
                    "{:?} changed the arity of {}",
                    passes,
                    name()
                );
            }

            // Everything together preserves net change, and never asks for
            // more inputs than the original did.
            let mut all = plain.clone();
            rewrite(&mut all, ALL);
            assert_eq!(net(&plain), net(&all), "net change changed for {}", name());
            assert!(
                seq_arity(&all).0 <= seq_arity(&plain).0,
                "rewriting raised the input requirement of {}",
                name()
            );

            let mut unary = all.clone();
            expand_to_unary_dips(&mut unary);
            assert_eq!(
                seq_arity(&all),
                seq_arity(&unary),
                "unary expansion changed the arity of {}",
                name()
            );
            assert!(
                unary_only(&unary),
                "{} kept a dip deeper than 1 after expansion",
                name()
            );
            checked += 1;
        }

        assert!(checked > 500, "expected the full corpus, saw {}", checked);
    }

    /// Whether every dip in the tree hides at most one value.
    fn unary_only(nodes: &[Node]) -> bool {
        nodes.iter().all(|node| match node {
            Node::Dip { depth, body, .. } => *depth <= 1 && unary_only(body),
            Node::Branch {
                then_body,
                else_body,
                ..
            } => unary_only(then_body) && unary_only(else_body),
            Node::Op(_) | Node::Cut(_) => true,
        })
    }

    #[test]
    fn normalization_preserves_arity() {
        // The rewrite is supposed to be meaning-preserving; arity is the part
        // of the meaning this tool can check for itself.
        let code = r#"
            sentence probe {
                push 1
                dip 2 { add }
                roll 1
                dip 1 { drop 0 }
                add
            }
        "#;
        let plain = tree(code, Passes::default());
        let normalized = tree(code, DIPS);
        assert_ne!(shape(&plain), shape(&normalized), "expected some rewriting");
        assert_eq!(seq_arity(&plain), seq_arity(&normalized));
    }
}

