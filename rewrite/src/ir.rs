//! The term the tool rewrites and prints.
//!
//! ## The algebra
//!
//! A program is a **term**, and a term is built from three atoms and two binary
//! operators:
//!
//! ```text
//! A, B  ::=  id n  |  op  |  jump S           the atoms
//!         |  A ; B                            composition
//!         |  par { A } { B }                  parallel composition
//!         |  branch { A } { B }
//! ```
//!
//! `A ; B` runs `A` and then `B`. `par { A } { B }` runs both, on disjoint
//! parts of one stack: the arities say how it is carved, with `B` taking the
//! values on top and `A` the ones underneath. `id n` is the identity on `n`
//! values, and `id 0` — the program that does nothing at all — is the unit of
//! both operators.
//!
//! ## What became of `dip`
//!
//! The ISA has a `dip`, an instruction that runs a block with the top value
//! hidden from it. That is `par { A } { id }`: a computation beside an identity,
//! carved so that the identity gets the top value and passes it through
//! untouched. A region `k` values wide is `par { A } { id k }`, which is what
//! [`Term::frame`] builds and [`Term::as_frame`] reads back — the tree keeps a
//! width because [`Rule::Collapse`][crate::rule::Rule::Collapse] can merge a
//! nest of frames into one, so the number here is one a rewrite arrived at
//! rather than one the bytecode stated.
//!
//! A `par` whose right-hand side is *not* an identity is a term nothing
//! compiles to today. The operator is binary because that is what it means for
//! two computations to run side by side; the frames are the special case that
//! the instruction set happens to be written in. The laws are stated about the
//! general shape all the same — [`Rule::Interchange`][crate::rule::Rule::Interchange]
//! joins any two `par`s whose upper regions meet — so a term that holds one is
//! a term the rules can read, whether a rewrite or a script put it there.
//!
//! ## Composition is associative, and the code reads it that way
//!
//! `(A ; B) ; C` and `A ; (B ; C)` are the same program, so nothing here is
//! allowed to distinguish them. Every term is built through [`Term::seq`] and
//! [`Term::then`], which nest to the right and drop `id 0`, and every traversal
//! that wants to look *inside* a composite reads its [`spine`][Term::spine] —
//! the factors in order, with the associativity forgotten. A window is a run of
//! adjacent factors of one spine, which is what makes an equation's left-hand
//! side something a search can look for.

use bytecode::{Instruction, Library, SentenceIndex};

use crate::program::Program;

/// A program.
///
/// **Canonical by construction.** `Compose` is only ever built by [`Term::then`]
/// and [`Term::seq`], which right-nest and drop the unit, so structural equality
/// is equality modulo associativity — which is what lets [`same_effect`] be a
/// recursive walk rather than a spine comparison at every level.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Term {
    /// `id n`: the identity on `n` values.
    ///
    /// `id 0` is the empty program and the unit of both `;` and `par`. Wider
    /// identities exist for one reason: `par` carves the stack by the arities of
    /// its two sides, so the thing that passes `k` values through has to be able
    /// to say how many.
    Id(usize),
    Op(Instruction),
    /// A call that has not been expanded.
    ///
    /// Its arity is its target's, which is what an unexpanded call needs in
    /// order not to poison the reckoning of everything after it.
    Call(SentenceIndex),
    /// `A ; B`.
    Compose(Box<Term>, Box<Term>),
    /// `par { A } { B }`: `B` on the values at the top, `A` on the ones below.
    Par {
        /// Where the left-hand side came from; more than one entry after a
        /// fusion, and empty for a `par` a rewrite built.
        origins: Vec<String>,
        left: Box<Term>,
        right: Box<Term>,
    },
    Branch {
        then_origin: String,
        then_body: Box<Term>,
        else_origin: String,
        else_body: Box<Term>,
    },
}

impl Term {
    /// The empty program: `id 0`.
    pub(crate) fn nil() -> Term {
        Term::Id(0)
    }

    pub(crate) fn is_nil(&self) -> bool {
        matches!(self, Term::Id(0))
    }

    /// `self ; other`, right-nested, with the unit dropped and adjacent
    /// identities merged.
    pub(crate) fn then(self, other: Term) -> Term {
        if self.is_nil() {
            return other;
        }
        if other.is_nil() {
            return self;
        }
        match self {
            Term::Compose(a, b) => Term::Compose(a, Box::new(b.then(other))),
            // `id j ; id k` = `id max(j, k)`. Neither does anything, and what a
            // composite requires is the deepest thing either half reached for —
            // so two identities in a row are one. Without this the interchange
            // law's frame case would answer with `par { A ; B } { id k ; id k }`,
            // which is the same program written so that nothing recognizes the
            // frame in it.
            Term::Id(j) => match other {
                Term::Id(k) => Term::Id(j.max(k)),
                Term::Compose(head, tail) => match *head {
                    Term::Id(k) => Term::Id(j.max(k)).then(*tail),
                    head => Term::Compose(
                        Box::new(Term::Id(j)),
                        Box::new(Term::Compose(Box::new(head), tail)),
                    ),
                },
                other => Term::Compose(Box::new(Term::Id(j)), Box::new(other)),
            },
            head => Term::Compose(Box::new(head), Box::new(other)),
        }
    }

    /// The composite of a run of terms, in order.
    ///
    /// **This is where the canonical form comes from.** Every composite is
    /// nested to the right and holds no `id 0`, so two terms that differ only in
    /// how their composition was bracketed are the same value — which is what
    /// lets `==` and [`same_effect`] be structural walks rather than spine
    /// comparisons at every level. An empty run is `id 0`.
    pub(crate) fn seq(items: impl IntoIterator<Item = Term>) -> Term {
        let mut factors: Vec<Term> = Vec::new();
        for item in items {
            item.take_spine(&mut factors);
        }
        let Some(mut out) = factors.pop() else {
            return Term::nil();
        };
        while let Some(t) = factors.pop() {
            out = t.then(out);
        }
        out
    }

    /// `par { left } { right }`, with no provenance.
    pub(crate) fn par(left: Term, right: Term) -> Term {
        Term::Par {
            origins: Vec::new(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// The same, remembering where the left-hand side came from.
    pub(crate) fn par_from(origins: Vec<String>, left: Term, right: Term) -> Term {
        Term::Par {
            origins,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// `par { body } { id k }`: `body` run with the top `k` values passed
    /// through beside it. What a `dip k` used to be.
    pub(crate) fn frame(origins: Vec<String>, k: usize, body: Term) -> Term {
        Term::par_from(origins, body, Term::Id(k))
    }

    /// The width, provenance and body of a frame, if that is what this is.
    ///
    /// A `par` whose right-hand side is a general computation has no width to
    /// report: the laws that reason about a hidden window are stated about the
    /// identity case, and this is what holds them to it.
    pub(crate) fn as_frame(&self) -> Option<(usize, &[String], &Term)> {
        match self {
            Term::Par {
                origins,
                left,
                right,
            } => match **right {
                Term::Id(k) => Some((k, origins, left)),
                _ => None,
            },
            _ => None,
        }
    }

    /// `branch { then } { else }`, with provenance for the two arms.
    pub(crate) fn branch(
        then_origin: impl Into<String>,
        then_body: Term,
        else_origin: impl Into<String>,
        else_body: Term,
    ) -> Term {
        Term::Branch {
            then_origin: then_origin.into(),
            then_body: Box::new(then_body),
            else_origin: else_origin.into(),
            else_body: Box::new(else_body),
        }
    }

    /// The two arms and their provenance, if this is a branch.
    pub(crate) fn as_branch(&self) -> Option<(&str, &Term, &str, &Term)> {
        match self {
            Term::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            } => Some((then_origin, then_body, else_origin, else_body)),
            _ => None,
        }
    }

    /// The factors of a composite, in order, with the nesting forgotten.
    ///
    /// A term that is not a composite is one factor, and `id 0` is none.
    pub(crate) fn spine(&self) -> Vec<&Term> {
        let mut out = Vec::new();
        self.walk_spine(&mut out);
        out
    }

    /// Iterative down the right, which is the way a canonical composite nests:
    /// a sentence's spine is as long as the sentence, and recursing once per
    /// factor would put the whole of it on the stack.
    fn walk_spine<'t>(&'t self, out: &mut Vec<&'t Term>) {
        let mut cur = self;
        loop {
            match cur {
                Term::Compose(a, b) => {
                    a.walk_spine(out);
                    cur = b;
                }
                Term::Id(0) => return,
                other => {
                    out.push(other);
                    return;
                }
            }
        }
    }

    /// The same, taking the term apart rather than borrowing it.
    pub(crate) fn into_spine(self) -> Vec<Term> {
        let mut out = Vec::new();
        self.take_spine(&mut out);
        out
    }

    fn take_spine(self, out: &mut Vec<Term>) {
        let mut cur = self;
        loop {
            match cur {
                Term::Compose(a, b) => {
                    a.take_spine(out);
                    cur = *b;
                }
                Term::Id(0) => return,
                other => {
                    out.push(other);
                    return;
                }
            }
        }
    }

    /// How many factors the spine holds.
    pub(crate) fn width(&self) -> usize {
        let mut cur = self;
        let mut out = 0;
        loop {
            match cur {
                Term::Compose(a, b) => {
                    out += a.width();
                    cur = b;
                }
                Term::Id(0) => return out,
                _ => return out + 1,
            }
        }
    }
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

/// Turns a sentence into a term, expanding nothing that `unfold` could expand.
///
/// Blocks written inline *are* expanded, because a block is not a call. Phase 4
/// gives a branch arm and a `dip N { ... }` body a `SentenceIndex` alike, purely
/// because it needs somewhere to put them, and neither is reachable by name — so
/// there is no call site for `unfold` to open and nothing for the un-expanded
/// listing to name on one line.
///
/// A `dip N` or a `jump` naming a real sentence keeps its [`Term::Call`]: there
/// the callee exists independently, `unfold` is a real choice, and the label is
/// worth keeping.
///
/// The walk terminates because recursion is forbidden: `check_arities` refuses a
/// sentence that reaches itself, so a library that compiled has an acyclic call
/// graph and there is no cycle for this to guard against.
pub(crate) fn build(library: &Library, s_idx: SentenceIndex) -> Term {
    Term::seq(library.sentences[s_idx].iter().map(|inst| match inst {
        // The ISA has no width to read: a call hides nothing or one value, and
        // a deeper region is that many of them nested.
        Instruction::Jump(target) => build_call(library, 0, *target),
        Instruction::Dip(target) => build_call(library, 1, *target),
        Instruction::Branch(then_t, else_t) => Term::Branch {
            then_origin: label(library, *then_t),
            then_body: Box::new(build(library, *then_t)),
            else_origin: label(library, *else_t),
            else_body: Box::new(build(library, *else_t)),
        },
        other => Term::Op(other.clone()),
    }))
}

/// A `jump` or a `dip` naming a sentence, as the term it stands for.
///
/// A plain jump to a real sentence is a bare [`Term::Call`] — no `par`, because
/// nothing is running beside it. Everything else is a frame: an inline block
/// gets one even at width 0, since `par { A } { id 0 }` is what a jump into a
/// block written on the spot is, and the frame is where its label lives.
fn build_call(library: &Library, k: usize, target: SentenceIndex) -> Term {
    if is_inline_block(library, target) {
        Term::frame(vec![label(library, target)], k, build(library, target))
    } else if k == 0 {
        Term::Call(target)
    } else {
        Term::frame(Vec::new(), k, Term::Call(target))
    }
}

pub(crate) fn label(library: &Library, target: SentenceIndex) -> String {
    format!("#{} {}", usize::from(target), library.names[target])
}

/// The sub-terms of a factor, each labelled with the selector that names it.
///
/// A `Call` has none: its body is a sentence in the library, not part of this
/// term, and reaching it is what `unfold` is for.
///
/// The label is what lets a traversal record *where* it went, which is what a
/// [`Location`][crate::location::Location] is built from; recovering it after
/// the fact is impossible, so every traversal carries it whether or not it
/// looks.
pub(crate) fn child_seqs(node: &mut Term) -> Vec<(Selector, &mut Term)> {
    match node {
        Term::Par { left, right, .. } => {
            vec![
                (Selector::Left, &mut **left),
                (Selector::Right, &mut **right),
            ]
        }
        Term::Branch {
            then_body,
            else_body,
            ..
        } => vec![
            (Selector::Then, &mut **then_body),
            (Selector::Else, &mut **else_body),
        ],
        // A `Compose` is not a factor of anybody's spine, so a traversal never
        // meets one here.
        Term::Op(_) | Term::Call(_) | Term::Id(_) | Term::Compose(..) => Vec::new(),
    }
}

/// The one sub-term `sel` names, if the factor has one of that kind.
pub(crate) fn child_seq(node: &mut Term, sel: Selector) -> Option<&mut Term> {
    child_seqs(node)
        .into_iter()
        .find(|(s, _)| *s == sel)
        .map(|(_, body)| body)
}

/// How wide a factor's hidden window is, if it has one.
///
/// A frame — `par { A } { id k }` — hides `k` values from `A`, whether `A` is
/// spelled out or is an unexpanded call. Every equation that reasons about the
/// *window* rather than the body accepts both, or it would silently demand that
/// you unfold a callee just to move it.
///
/// A bare `jump` is not a `par` at all and reports `None`. A frame at `k = 0`
/// does report `Some(0)`: a window that hides nothing is a different thing from
/// having no window at all.
pub(crate) fn frame_depth(node: &Term) -> Option<usize> {
    node.as_frame().map(|(k, _, _)| k)
}

/// The same factor with its hidden window set to `k`.
pub(crate) fn with_frame_depth(node: &Term, k: usize) -> Option<Term> {
    let (_, origins, body) = node.as_frame()?;
    Some(Term::frame(origins.to_vec(), k, body.clone()))
}

/// Which sub-terms a traversal should descend into.
///
/// `children` and its relatives take every child of every factor; this names a
/// subset. The distinction is not cosmetic: a tactic that has to open one
/// branch arm and leave the other alone cannot be written without it, and
/// staged inlining stalls the moment the remaining calls sit inside arms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Selector {
    /// The `then` arm of every branch.
    Then,
    /// The `else` arm of every branch.
    Else,
    /// The left-hand side of every `par` — the computation a frame hides values
    /// from.
    Left,
    /// The right-hand side of every `par`, which for a frame is the identity
    /// that passes them through.
    Right,
}

/// The term a call stands for.
pub(crate) fn expand_call(prog: &Program, target: SentenceIndex) -> Term {
    build(prog.library(), target)
}

/// A one-line sketch of a run of factors: what a rule saw, or what it left.
///
/// Bounded in both directions — three factors wide at each level, two levels
/// deep — because the stepper prints one of these next to a prompt, and the
/// window a rule matched may hold a `par` with fifty thousand factors in it. The
/// listing above the prompt is where the term is shown in full; this only has
/// to be enough to recognize the rewrite by.
///
/// A call is named by index alone. The label wants the library, which a rule's
/// window does not carry, and the index is what the listing prints first.
pub(crate) fn sketch(nodes: &[Term]) -> String {
    let full = sketch_seq(nodes, 2);
    match full.char_indices().nth(SKETCH_LINE) {
        Some((cut, _)) => format!("{}…", &full[..cut]),
        None => full,
    }
}

/// One factor, named but not opened: `add`, `par { … } { id }`,
/// `branch { … } { … }`.
///
/// What [`sketch`] is for is recognizing a rewrite, so it shows two levels. What
/// this is for is saying what happened to be somewhere — a miss report naming
/// the factor an aimed rule declined — where the shape is the whole answer and a
/// branch's contents are a wall.
pub(crate) fn sketch_head(node: &Term) -> String {
    sketch_node(node, 0)
}

/// The same, for a whole term rather than a factor of one.
pub(crate) fn sketch_term(term: &Term) -> String {
    let spine: Vec<&Term> = term.spine();
    let owned: Vec<Term> = spine.into_iter().cloned().collect();
    sketch(&owned)
}

/// Factors shown per level before the rest becomes an ellipsis.
const SKETCH_WIDTH: usize = 3;

/// Characters a sketch may take up. Two branches with three factors each fit
/// inside the structural bounds and still run off the side of a terminal.
const SKETCH_LINE: usize = 88;

fn sketch_seq(nodes: &[Term], depth: usize) -> String {
    if nodes.is_empty() {
        return "(nothing)".to_string();
    }
    let mut parts: Vec<String> = nodes
        .iter()
        .take(SKETCH_WIDTH)
        .map(|node| sketch_node(node, depth))
        .collect();
    if nodes.len() > SKETCH_WIDTH {
        parts.push("…".to_string());
    }
    parts.join(" ; ")
}

fn sketch_inner(term: &Term, depth: usize) -> String {
    let spine: Vec<Term> = term.spine().into_iter().cloned().collect();
    sketch_seq(&spine, depth)
}

/// One side of a `par`. An identity is written as itself rather than as the
/// spine it does not have: `par { drop } { id 0 }` says which law is about to
/// fire where `par { drop } { (nothing) }` reads as a hole.
fn sketch_side(term: &Term, depth: usize) -> String {
    match term {
        Term::Id(k) => id_word(*k),
        other => sketch_inner(other, depth),
    }
}

fn sketch_node(node: &Term, depth: usize) -> String {
    match node {
        Term::Op(inst) => format!("{}", inst),
        Term::Id(k) => id_word(*k),
        Term::Call(target) => format!("jump → #{}", usize::from(*target)),
        Term::Compose(..) => sketch_inner(node, depth),
        Term::Par { left, right, .. } => match depth {
            0 => "par { … } { … }".to_string(),
            _ => format!(
                "par {{ {} }} {{ {} }}",
                sketch_side(left, depth - 1),
                sketch_side(right, depth - 1)
            ),
        },
        Term::Branch {
            then_body,
            else_body,
            ..
        } => match depth {
            0 => "branch { … } { … }".to_string(),
            _ => format!(
                "branch {{ {} }} {{ {} }}",
                sketch_inner(then_body, depth - 1),
                sketch_inner(else_body, depth - 1)
            ),
        },
    }
}

/// How an identity is written: `id` for the one-value case, `id k` otherwise.
pub(crate) fn id_word(k: usize) -> String {
    if k == 1 {
        "id".to_string()
    } else {
        format!("id {}", k)
    }
}

/// Whether two terms do the same thing.
///
/// Deliberately *not* the derived `PartialEq`. `Par::origins` and a branch's arm
/// origins record where code came from, which is for the listing and says
/// nothing about what the code does — and phase 4 allocates a fresh
/// `SentenceIndex` for every inline block, so two identical blocks written in
/// different places never share a label. Comparing those would make provenance
/// part of term identity, which is how `factor` used to miss every shared prefix
/// that contained a call.
///
/// A `Call` is compared by target: two calls to the same sentence do the same
/// thing, and two calls to different sentences might, but nothing here can tell
/// without expanding them.
pub(crate) fn same_effect(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Op(x), Term::Op(y)) => x == y,
        (Term::Id(x), Term::Id(y)) => x == y,
        (Term::Call(x), Term::Call(y)) => x == y,
        (Term::Compose(..), _) | (_, Term::Compose(..)) => {
            let (x, y) = (a.spine(), b.spine());
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| same_effect(p, q))
        }
        (
            Term::Par {
                left: la,
                right: ra,
                ..
            },
            Term::Par {
                left: lb,
                right: rb,
                ..
            },
        ) => same_effect(la, lb) && same_effect(ra, rb),
        (
            Term::Branch {
                then_body: ta,
                else_body: ea,
                ..
            },
            Term::Branch {
                then_body: tb,
                else_body: eb,
                ..
            },
        ) => same_effect(ta, tb) && same_effect(ea, eb),
        _ => false,
    }
}

pub(crate) fn same_effect_seq(a: &[Term], b: &[Term]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_effect(x, y))
}

/// The same, against a window borrowed out of a spine.
pub(crate) fn same_effect_refs(a: &[&Term], b: &[Term]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_effect(x, y))
}

/// A borrowed window, copied — for an error message, which is the only place
/// that needs one.
pub(crate) fn cloned(nodes: &[&Term]) -> Vec<Term> {
    nodes.iter().map(|t| (*t).clone()).collect()
}
