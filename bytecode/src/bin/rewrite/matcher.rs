//! Finding where an equation applies.
//!
//! A matcher reads a window and proposes steps. It does not rewrite anything —
//! [`crate::applier`] does that, and does it from the proposal alone — so a
//! matcher that is wrong produces a step that is refused rather than a tree
//! that is quietly broken.
//!
//! This is the upper layer at its simplest: one matcher per *search direction*
//! over the equations. `sink` and `float` are two matchers over one
//! [`Rule::Interchange`]; `collapse` and `expand` two over one
//! [`Rule::Collapse`]. What used to be a doubled rule is now a doubled way of
//! looking, which is the part that genuinely differs — the arithmetic is
//! written once.
//!
//! ## Window-relative locations
//!
//! **A matcher does not know where in the tree it is.** That was the old
//! system's governing invariant and it survives here unchanged, with one
//! addition: a matcher must say *where within its own window* each step lands,
//! and the driver turns that into a real [`Location`] with
//! [`Location::under`]. A matcher that needs to reach into a branch arm says
//! so with a descent from the window, never with a path from the root.
//!
//! ## Firings that take more than one step
//!
//! [`Factor`] is the first of these and the reason the two layers are worth
//! separating. Hoisting a shared prefix out of both arms of a branch used to be
//! one rule that knew a whole procedure; it is now three steps, each an
//! instance of a law — wrap the prefix in a frame in each arm, then read the
//! hoist law backwards. The steps are applied in order, so each one's location
//! addresses the tree as the previous one left it.
//!
//! ## What a matcher owes
//!
//! Termination. An equation is true in both directions and says nothing about
//! progress; every measure that used to live on a rule lives here instead, in
//! the choice of which direction to look for and when to decline. `expand`
//! and `float` and `unfactor` have no measure at all and must not share a
//! fixpoint with their opposites — the fuel budget is what diagnoses it when
//! they do.

use bytecode::Instruction;

use crate::arity::{full_arity, node_arity};
use crate::ir::{Node, Selector, frame_depth, same_effect, same_effect_seq, with_frame_depth};
use crate::location::Location;
use crate::program::Program;
use crate::rule::{Direction, Rule, StepKind};

/// A step a matcher wants taken, positioned relative to the window it saw.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PlannedStep {
    pub(crate) kind: StepKind,
    pub(crate) dir: Direction,
    /// Where this lands *within the window*. `Location::root(0)` is the window
    /// itself; a descent reaches into a node inside it.
    pub(crate) rel: Location,
}

/// A way of looking for work.
pub(crate) trait Matcher: Sync + std::fmt::Debug {
    fn name(&self) -> &'static str;

    /// How many adjacent nodes this reads. The driver only ever hands `plan` a
    /// window of exactly this length.
    fn width(&self) -> usize;

    /// The steps that rewrite this window, or nothing.
    ///
    /// Every step returned must be one the applier will accept: a matcher
    /// checks its own side conditions rather than proposing something that
    /// fails. An empty vector is not a match — return `None`.
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>>;

    /// The same equation, read the other way: what `inv(...)` resolves to.
    ///
    /// An equation is true in both directions, but *looking* for it is not the
    /// same job twice — `sink` reads `X ; D` where `float` reads `D ; X`, and
    /// the arithmetic between them runs backwards. So an inverse is a real
    /// matcher and has to be written, and this is where each one says which.
    ///
    /// It is **required rather than defaulted**, so that adding a matcher means
    /// deciding what its backward reading is instead of silently having none.
    /// Where that reading is worth a name of its own it gets one and this
    /// simply returns it: `Sink::inverse` is [`Float`]. Where it is not, the
    /// matcher is unnameable — reachable only through `inv` — and reports
    /// itself as `inv(x)`, which keeps the rule namespace to the readings
    /// people actually talk about.
    ///
    /// `Err` for a reading that cannot be searched for at all, carrying why.
    /// Three things put a reading out of reach, and the message says which:
    /// the backward side would have to be **invented** rather than recognized
    /// (`eval`, `fold_branch`), an argument it needs is **not recoverable**
    /// from the window (`cancel_tuple`'s `n`), or the backward side is
    /// **empty**, so there is no window to match at all (`counit`).
    fn inverse(&self) -> Result<Box<dyn Matcher>, String>;
}

/// A step at the window itself, refused if its arguments do not hold up.
fn at_window(prog: &Program, rule: Rule, dir: Direction) -> Option<Vec<PlannedStep>> {
    rule.check(prog).ok()?;
    Some(vec![PlannedStep {
        kind: StepKind::Rule(rule),
        dir,
        rel: Location::root(0),
    }])
}

/// Every matcher that takes no arguments, by name.
///
/// A tactic expression can order and place these but cannot define one: they
/// are a fixed vocabulary in their own namespace. [`Introduce`] is not here
/// because it is not complete without a term — see [`matcher_with_term`].
pub(crate) fn matcher_by_name(name: &str) -> Option<Box<dyn Matcher>> {
    Some(match name {
        "annihilate" => Box::new(Annihilate),
        "annihilate_flagged" => Box::new(AnnihilateFlagged),
        "cancel_tuple" => Box::new(CancelTuple),
        "collapse" => Box::new(Collapse),
        "comm" => Box::new(Comm),
        "copy_assoc" => Box::new(CopyAssoc),
        "copy_const" => Box::new(CopyConst),
        "counit" => Box::new(Counit),
        "distribute" => Box::new(Distribute),
        "eval1" => Box::new(EvalUnary),
        "eval2" => Box::new(EvalBinary),
        "expand" => Box::new(Expand),
        "factor" => Box::new(Factor),
        "flatten" => Box::new(Flatten),
        "float" => Box::new(Float),
        "fold_branch" => Box::new(FoldBranch),
        "fuse" => Box::new(Fuse),
        "sink" => Box::new(Sink),
        "split_bool" => Box::new(SplitBool),
        "swap" => Box::new(Swap),
        "unsplit_bool" => Box::new(UnsplitBool),
        "unfactor" => Box::new(Unfactor),
        "unfold" => Box::new(Unfold),
        _ => return None,
    })
}

/// The matchers that take no arguments, in the order `--list-rules` prints.
pub(crate) fn matcher_names() -> Vec<&'static str> {
    let mut names = vec![
        "annihilate",
        "annihilate_flagged",
        "cancel_tuple",
        "collapse",
        "comm",
        "copy_assoc",
        "copy_const",
        "counit",
        "distribute",
        "eval1",
        "eval2",
        "expand",
        "factor",
        "flatten",
        "float",
        "fold_branch",
        "fuse",
        "sink",
        "split_bool",
        "swap",
        "unfactor",
        "unsplit_bool",
        "unfold",
    ];
    names.sort();
    names
}

/// The matchers that need a term, by name.
pub(crate) fn term_matcher_names() -> Vec<&'static str> {
    vec!["introduce", "share"]
}

/// A matcher completed by a term written in the tactic expression.
///
/// `None` for a name that is not one of these; `Err` for one that is but whose
/// term it cannot use.
pub(crate) fn matcher_with_term(
    name: &str,
    term: Vec<Node>,
    prog: Option<&Program>,
) -> Option<Result<Box<dyn Matcher>, String>> {
    match name {
        "introduce" => Some(Introduce::new(prog, term).map(|m| Box::new(m) as Box<dyn Matcher>)),
        "share" => Some(Share::new(prog, term).map(|m| Box::new(m) as Box<dyn Matcher>)),
        _ => None,
    }
}

/// A term's arity, using the library when there is one.
///
/// [`term_arity`] answers from the term alone, which is what lets a tactic be
/// compiled before a program is chosen — but it has no answer for a term that
/// names a sentence. With a program in hand, `full_arity` does.
fn arity_of(prog: Option<&Program>, x: &[Node]) -> Option<(i64, i64)> {
    match prog {
        Some(prog) => full_arity(prog, x),
        None => term_arity(x),
    }
}

/// What a term has to be before a law can close over it.
///
/// Shared by the two rules that take one, because they want the same three
/// things: something to work with, an arity to state the law at, and that
/// arity in the range the law's arguments are counted in.
fn term_arity_or_why(prog: Option<&Program>, x: &[Node]) -> Result<(usize, usize), String> {
    if x.is_empty() {
        return Err("there is nothing there".to_string());
    }
    let Some((n, m)) = arity_of(prog, x) else {
        return Err(
            "the arity of that is not known, so there is no saying how many \
             values it reads or leaves"
                .to_string(),
        );
    };
    match (usize::try_from(n), usize::try_from(m)) {
        (Ok(n), Ok(m)) => Ok((n, m)),
        _ => Err(format!("an arity of {:?} cannot be used here", (n, m))),
    }
}

// ---------------------------------------------------------------------------
// Calls and frames
// ---------------------------------------------------------------------------

/// Opens a call, replacing it with the block it names.
///
/// Nothing is expanded until you ask. The cost is provenance — a spliced body
/// no longer says which sentence it came from — which is why this is not in any
/// default pass.
#[derive(Debug)]
pub(crate) struct Unfold;

impl Matcher for Unfold {
    fn name(&self) -> &'static str {
        "unfold"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "reading `unfold` backwards *folds*: it contracts a body back \
             into a call. That has to name the sentence to fold into, and \
             nothing in a window says which one — the step kind can express \
             it, but no matcher looks for it yet"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Call { depth, target } = &window[0] else {
            return None;
        };
        if prog.is_recursive(*target) {
            return None;
        }
        Some(vec![PlannedStep {
            kind: StepKind::Unfold {
                depth: *depth,
                target: *target,
            },
            dir: Direction::Forward,
            rel: Location::root(0),
        }])
    }
}

/// `dip k { dip j { A } }` becomes `dip (k+j) { A }`.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct Collapse;

impl Matcher for Collapse {
    fn name(&self) -> &'static str {
        "collapse"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Expand))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Dip {
            depth: k,
            origins: outer,
            body,
        } = &window[0]
        else {
            return None;
        };
        let [
            Node::Dip {
                depth: j,
                origins: inner,
                body: a,
            },
        ] = &body[..]
        else {
            return None;
        };
        at_window(
            prog,
            Rule::Collapse {
                k: *k,
                j: *j,
                a: a.clone(),
                outer: outer.clone(),
                inner: inner.clone(),
            },
            Direction::Forward,
        )
    }
}

/// `dip k { A }` becomes `dip 1 { dip (k-1) { A } }`, for `k >= 2`.
///
/// The same law as [`Collapse`] read backwards, peeling one level at a time;
/// driven to a fixpoint it writes a hidden region in unary, which is the
/// classic `dip` combinator. The origins ride inward to the level that holds
/// the body.
///
/// Measure: none. This *increases* the node count and must never share a
/// fixpoint with [`Collapse`].
#[derive(Debug)]
pub(crate) struct Expand;

impl Matcher for Expand {
    fn name(&self) -> &'static str {
        "expand"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Collapse))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Dip {
            depth,
            origins,
            body,
        } = &window[0]
        else {
            return None;
        };
        // `dip 0` hides nothing and `dip 1` is already unary.
        if *depth < 2 {
            return None;
        }
        at_window(
            prog,
            Rule::Collapse {
                k: 1,
                j: depth - 1,
                a: body.clone(),
                outer: Vec::new(),
                inner: origins.clone(),
            },
            Direction::Reverse,
        )
    }
}

/// `dip 0 { P }` becomes `P`, spliced into the enclosing sequence.
///
/// This is the matcher that lets the others reach across a call. Rules only see
/// the sequence they are handed, so a branch one frame down and an instruction
/// outside it are not in the same window until this has fired.
///
/// It discards the frame's origins, so the listing stops saying which sentence
/// the code came from.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct Flatten;

impl Matcher for Flatten {
    fn name(&self) -> &'static str {
        "flatten"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvFlatten))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Dip {
            depth: 0,
            origins,
            body,
        } = &window[0]
        else {
            return None;
        };
        at_window(
            prog,
            Rule::ElimDip0 {
                a: body.clone(),
                origins: origins.clone(),
            },
            Direction::Forward,
        )
    }
}

/// `A` becomes `dip 0 { A }`: the frame [`Flatten`] takes away.
///
/// [`Rule::ElimDip0`] read backwards, wrapping one node in a frame that hides
/// nothing. That looks like a pointless thing to do until you want to move the
/// node, because [`Rule::Interchange`] and [`Rule::Hoist`] both carry *frames*
/// — so putting one round a bare instruction is how it becomes something the
/// movement laws can pick up. `factor` uses exactly this step, twice.
///
/// No name of its own: it is `inv(flatten)`.
///
/// Measure: none, and it grows the term — its own output is a node it would
/// wrap again, so `each` never settles. Aim it.
#[derive(Debug)]
pub(crate) struct InvFlatten;

impl Matcher for InvFlatten {
    fn name(&self) -> &'static str {
        "inv(flatten)"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Flatten))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        at_window(
            prog,
            Rule::ElimDip0 {
                a: window.to_vec(),
                origins: Vec::new(),
            },
            Direction::Reverse,
        )
    }
}

/// `dip k { A } ; dip k { B }` becomes `dip k { A B }`.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct Fuse;

impl Matcher for Fuse {
    fn name(&self) -> &'static str {
        "fuse"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvFuse))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Dip {
                depth: ka,
                origins: oa,
                body: ba,
            },
            Node::Dip {
                depth: kb,
                origins: ob,
                body: bb,
            },
        ] = window
        else {
            return None;
        };
        if ka != kb {
            return None;
        }
        at_window(
            prog,
            Rule::Fuse {
                k: *ka,
                a: ba.clone(),
                b: bb.clone(),
                a_origins: oa.clone(),
                b_origins: ob.clone(),
            },
            Direction::Forward,
        )
    }
}

/// `dip k { A B }` becomes `dip k { A } ; dip k { B }`, splitting off one node.
///
/// [`Rule::Fuse`] read backwards. The equation lets the body be cut anywhere,
/// and this takes the canonical cut: one node off the front, the way [`Expand`]
/// takes the canonical split of [`Rule::Collapse`]. Driven by `each` it would
/// peel the whole body apart, one frame per node — which is also why it must
/// not share a fixpoint with [`Fuse`].
///
/// No name of its own: it is `inv(fuse)`.
///
/// Measure: none. It grows the term.
#[derive(Debug)]
pub(crate) struct InvFuse;

impl Matcher for InvFuse {
    fn name(&self) -> &'static str {
        "inv(fuse)"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Fuse))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Dip {
            depth,
            origins,
            body,
        } = &window[0]
        else {
            return None;
        };
        // One node either side, or the split says nothing: an empty frame beside
        // the original is a change the listing shows and nothing can use.
        if body.len() < 2 {
            return None;
        }
        at_window(
            prog,
            Rule::Fuse {
                k: *depth,
                a: body[..1].to_vec(),
                b: body[1..].to_vec(),
                a_origins: origins.clone(),
                b_origins: Vec::new(),
            },
            Direction::Reverse,
        )
    }
}

// ---------------------------------------------------------------------------
// Interchange
// ---------------------------------------------------------------------------

/// `X ; dip k { S }` becomes `dip (k-m+n) { S } ; X`, where `X : n -> m` and
/// `k >= m`.
///
/// The normalizing direction of the interchange law: it walks framed
/// computations left, past everything whose results their window clears.
///
/// Measure: the summed positions of dips.
#[derive(Debug)]
pub(crate) struct Sink;

impl Matcher for Sink {
    fn name(&self) -> &'static str {
        "sink"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Float))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [x, framed] = window else { return None };
        // The equation's own arithmetic checks `k >= m`; all this has to do is
        // supply the arity it claims.
        let (n, m) = node_arity(prog, x)?;
        at_window(
            prog,
            Rule::Interchange {
                x: x.clone(),
                framed: framed.clone(),
                n,
                m,
            },
            Direction::Forward,
        )
    }
}

/// `dip j { S } ; X` becomes `X ; dip (j-n+m) { S }`, where `X : n -> m` and
/// `j >= n`.
///
/// The same law read from the other side. `sink` needs the window to clear
/// what `X` leaves behind; this needs it to clear what `X` *consumes*, so that
/// `X`'s operands are entirely inside the hidden region and `S` cannot disturb
/// them. The two conditions are the same one seen from either end.
///
/// It exists for the case where a computation has to be delivered *to*
/// somewhere rather than gathered up.
///
/// Measure: none. Termination is the caller's problem, which is what `once` and
/// `repeat_n` are for.
#[derive(Debug)]
pub(crate) struct Float;

impl Matcher for Float {
    fn name(&self) -> &'static str {
        "float"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Sink))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [framed, x] = window else { return None };
        let j = frame_depth(framed)? as i64;
        let (n, m) = node_arity(prog, x)?;
        if j < n {
            return None;
        }
        // The equation is stated with the left-hand side's depth, so recover it:
        // `j = k - m + n`, hence `k = j - n + m`.
        let k = usize::try_from(j - n + m).ok()?;
        at_window(
            prog,
            Rule::Interchange {
                x: x.clone(),
                framed: with_frame_depth(framed, k)?,
                n,
                m,
            },
            Direction::Reverse,
        )
    }
}

// ---------------------------------------------------------------------------
// Branches
// ---------------------------------------------------------------------------

/// `branch { X A } { X B }` becomes `dip 1 { X }; branch { A } { B }`.
///
/// `X` runs the same way whichever arm is taken, so it can run before the
/// condition is consumed — but only under a dip, because at that point the
/// condition is still on top and `X` must not be handed it.
///
/// **This is a firing of three steps.** The law it ends on
/// ([`Rule::Hoist`], backwards) lifts one framed block out of both arms, so
/// the shared run has to be wrapped in a frame first — which is
/// [`Rule::ElimDip0`] backwards, once per arm. Where the old rule spliced a
/// prefix of any length in one motion, this spells out why that was allowed.
///
/// Takes the whole shared run at once. Arms are compared by effect, not by
/// label, so two identical blocks compiled to different sentences still count
/// as shared — and the else arm's provenance is lost, as it always was.
///
/// Measure: nodes held inside branch arms.
#[derive(Debug)]
pub(crate) struct Factor;

impl Matcher for Factor {
    fn name(&self) -> &'static str {
        "factor"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "`factor` is three steps of two different equations, so there is \
             no single one to read backwards. `inv(unfactor)` is the last of \
             the three, lifting a framed prefix out of both arms"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = &window[0]
        else {
            return None;
        };

        let shared = then_body
            .iter()
            .zip(else_body)
            .take_while(|(a, b)| same_effect(a, b))
            .count();
        if shared == 0 {
            return None;
        }
        let prefix = then_body[..shared].to_vec();

        // Wrap the shared run in a frame inside each arm. The `else` arm is
        // wrapped using the `then` arm's copy, which is sound because the two
        // are the same by effect and is what loses the else arm's origins.
        let wrap = |sel: Selector| PlannedStep {
            kind: StepKind::Rule(Rule::ElimDip0 {
                a: prefix.clone(),
                origins: Vec::new(),
            }),
            dir: Direction::Reverse,
            rel: Location {
                descent: vec![(0, sel)],
                at: 0,
            },
        };
        let steps = [wrap(Selector::Then), wrap(Selector::Else)];

        // Then lift the two frames into one, in front of the branch.
        let hoist = Rule::Hoist {
            k: 0,
            x: prefix,
            origins: Vec::new(),
            then_arm: then_body[shared..].to_vec(),
            else_arm: else_body[shared..].to_vec(),
            then_origin: then_origin.clone(),
            else_origin: else_origin.clone(),
        };
        hoist.check(prog).ok()?;

        let [wrap_then, wrap_else] = steps;
        Some(vec![
            wrap_then,
            wrap_else,
            PlannedStep {
                kind: StepKind::Rule(hoist),
                dir: Direction::Reverse,
                rel: Location::root(0),
            },
        ])
    }
}

/// `dip k { X } ; branch { A } { B }` becomes
/// `branch { dip (k-1) { X }; A } { dip (k-1) { X }; B }`, for `k >= 1`.
///
/// The window has to contain the condition, or the branch would be popping
/// something the block could have produced. Deeper windows are the case that
/// matters in practice: restricting this to `k = 1` would mean a computation
/// could only be pushed into a branch it happened to sit immediately beneath,
/// which is almost never where `float` leaves one.
///
/// It duplicates on purpose — a law that only holds inside an arm cannot see
/// anything outside one.
///
/// Measure: none. Never put this and [`Factor`] in one `repeat`.
#[derive(Debug)]
pub(crate) struct Unfactor;

impl Matcher for Unfactor {
    fn name(&self) -> &'static str {
        "unfactor"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvHoist))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Dip {
                depth,
                origins,
                body,
            },
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
        ] = window
        else {
            return None;
        };
        if *depth < 1 {
            return None;
        }
        if body.is_empty() {
            // Pushing nothing into both arms reports a change without making
            // one worth making.
            return None;
        }
        at_window(
            prog,
            Rule::Hoist {
                k: depth - 1,
                x: body.clone(),
                origins: origins.clone(),
                then_arm: then_body.clone(),
                else_arm: else_body.clone(),
                then_origin: then_origin.clone(),
                else_origin: else_origin.clone(),
            },
            Direction::Forward,
        )
    }
}

/// `branch { dip k { X } ; A } { dip k { X } ; B }` becomes
/// `dip (k+1) { X } ; branch { A } { B }`.
///
/// [`Rule::Hoist`] read backwards: the frame both arms open with runs whichever
/// way the branch goes, so it can run before the condition is consumed — one
/// deeper, because out there the condition is still on the stack.
///
/// This is [`Factor`]'s third step, on its own and generalized. `factor` starts
/// from an *unframed* shared prefix and wraps it first, so it always hoists at
/// `k = 0`; this takes a frame that is already there, at any depth, which is
/// what `float` tends to leave behind.
///
/// The two frames are compared by effect, so provenance does not have to agree.
///
/// No name of its own: it is `inv(unfactor)`.
///
/// Measure: nodes held inside branch arms, like [`Factor`]'s — but it must
/// still not share a fixpoint with [`Unfactor`], which puts them back.
#[derive(Debug)]
pub(crate) struct InvHoist;

impl Matcher for InvHoist {
    fn name(&self) -> &'static str {
        "inv(unfactor)"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Unfactor))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = &window[0]
        else {
            return None;
        };
        let (Some(head), Some(other)) = (then_body.first(), else_body.first()) else {
            return None;
        };
        if !same_effect(head, other) {
            return None;
        }
        // A `Call` hides something too, but the equation spells the frame out as
        // a dip and there is nowhere to put a callee's name.
        let Node::Dip {
            depth: k,
            origins,
            body: x,
        } = head
        else {
            return None;
        };
        at_window(
            prog,
            Rule::Hoist {
                k: *k,
                x: x.clone(),
                origins: origins.clone(),
                then_arm: then_body[1..].to_vec(),
                else_arm: else_body[1..].to_vec(),
                then_origin: then_origin.clone(),
                else_origin: else_origin.clone(),
            },
            Direction::Reverse,
        )
    }
}

/// `branch { A } { B } ; X` becomes `branch { A X } { B X }`.
///
/// `X` runs after whichever arm was taken, so moving it inside both is no
/// change at all. The point is to put it where a law can see it in context: a
/// simplification that only holds on one side cannot fire while `X` sits
/// outside.
///
/// Measure: nodes following a branch in the same sequence. Node count *grows*.
#[derive(Debug)]
pub(crate) struct Distribute;

impl Matcher for Distribute {
    fn name(&self) -> &'static str {
        "distribute"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvDistribute))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
            next,
        ] = window
        else {
            return None;
        };
        at_window(
            prog,
            Rule::Distribute {
                then_arm: then_body.clone(),
                else_arm: else_body.clone(),
                suffix: vec![next.clone()],
                then_origin: then_origin.clone(),
                else_origin: else_origin.clone(),
            },
            Direction::Forward,
        )
    }
}

/// `branch { A C } { B C }` becomes `branch { A } { B } ; C`.
///
/// [`Rule::Distribute`] read backwards, which factors a shared **suffix** out
/// of both arms — the move the old rule set could not express at all, since
/// `factor_branch` only ever worked on prefixes. It takes the longest shared
/// run, compared by effect.
///
/// No name of its own: it is `inv(distribute)`.
///
/// Measure: nodes held inside branch arms. It shrinks the term, but must not
/// share a fixpoint with [`Distribute`], which puts the suffix back.
#[derive(Debug)]
pub(crate) struct InvDistribute;

impl Matcher for InvDistribute {
    fn name(&self) -> &'static str {
        "inv(distribute)"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Distribute))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Branch {
            then_origin,
            then_body,
            else_origin,
            else_body,
        } = &window[0]
        else {
            return None;
        };
        let shared = then_body
            .iter()
            .rev()
            .zip(else_body.iter().rev())
            .take_while(|(a, b)| same_effect(a, b))
            .count();
        if shared == 0 {
            return None;
        }
        at_window(
            prog,
            Rule::Distribute {
                then_arm: then_body[..then_body.len() - shared].to_vec(),
                else_arm: else_body[..else_body.len() - shared].to_vec(),
                suffix: then_body[then_body.len() - shared..].to_vec(),
                then_origin: then_origin.clone(),
                else_origin: else_origin.clone(),
            },
            Direction::Reverse,
        )
    }
}

/// `push c ; branch { A } { B }` becomes the arm `c` selects.
///
/// Any literal folds, not only a `Bool`: a branch takes the then arm on
/// `Bool(true)` and the else arm on everything else, so `push 1; branch` is
/// decided just as firmly. A *computed* condition still declines, which is the
/// real content — it folds what is already decided.
///
/// Measure: branch count.
#[derive(Debug)]
pub(crate) struct FoldBranch;

impl Matcher for FoldBranch {
    fn name(&self) -> &'static str {
        "fold_branch"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "reading `fold_branch` backwards would have to invent the arm \
             that was not taken, and a condition that chooses between them. \
             The window is the arm that ran and says neither"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Push(c)),
            Node::Branch {
                then_origin,
                then_body,
                else_origin,
                else_body,
            },
        ] = window
        else {
            return None;
        };
        at_window(
            prog,
            Rule::FoldBranch {
                c: c.clone(),
                then_arm: then_body.clone(),
                else_arm: else_body.clone(),
                then_origin: then_origin.clone(),
                else_origin: else_origin.clone(),
            },
            Direction::Forward,
        )
    }
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/// Evaluates a two-operand operator whose operands are already literals.
///
/// Folding is evaluation: every operator is total, so running it on known
/// values and pushing the answer is the same program. The equation declines
/// anything it has no answer for, so this proposes and lets it judge.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct EvalBinary;

impl Matcher for EvalBinary {
    fn name(&self) -> &'static str {
        "eval2"
    }
    fn width(&self) -> usize {
        3
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "reading `eval` backwards would have to invent the operator \
             that produced the literal, and the operands it was applied to"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Push(a)),
            Node::Op(Instruction::Push(b)),
            Node::Op(inst),
        ] = window
        else {
            return None;
        };
        at_window(
            prog,
            Rule::Eval {
                op: inst.clone(),
                inputs: vec![a.clone(), b.clone()],
            },
            Direction::Forward,
        )
    }
}

/// Evaluates a one-operand operator applied to a literal.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct EvalUnary;

impl Matcher for EvalUnary {
    fn name(&self) -> &'static str {
        "eval1"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "reading `eval` backwards would have to invent the operator \
             that produced the literal, and the operand it was applied to"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [Node::Op(Instruction::Push(a)), Node::Op(inst)] = window else {
            return None;
        };
        at_window(
            prog,
            Rule::Eval {
                op: inst.clone(),
                inputs: vec![a.clone()],
            },
            Direction::Forward,
        )
    }
}

/// `X ; drop` becomes `drop^n`, where `X : n -> 1`.
///
/// Computing a value and throwing it away is throwing away the operands
/// instead. `pick d` is not of this shape — it is `(d+1 -> d+2)` — so it falls
/// to [`Counit`] rather than here, without either matcher having to say so.
///
/// Measure: non-drop node count.
#[derive(Debug)]
pub(crate) struct Annihilate;

impl Matcher for Annihilate {
    fn name(&self) -> &'static str {
        "annihilate"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "the backward reading of `annihilate` is the introduction rule, \
             which has to say what computation to conjure in front of the \
             drops: write `introduce { ... }`"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        annihilate_with(prog, window, 1)
    }
}

/// `X ; drop ; drop` becomes `drop^n`, where `X : n -> 2`.
///
/// The two-output case, which exists because a fallible instruction leaves its
/// flag alongside its value: `add` is `(2 -> 2)`, so what cancels it is two
/// drops rather than one. `pick 0` is `(1 -> 2)` and belongs here too, copying
/// a value only for both copies to go.
///
/// Measure: non-drop node count.
#[derive(Debug)]
pub(crate) struct AnnihilateFlagged;

impl Matcher for AnnihilateFlagged {
    fn name(&self) -> &'static str {
        "annihilate_flagged"
    }
    fn width(&self) -> usize {
        3
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "the backward reading of `annihilate` is the introduction rule, \
             which has to say what computation to conjure in front of the \
             drops: write `introduce { ... }`"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        annihilate_with(prog, window, 2)
    }
}

/// The shared body of the annihilation matchers, which differ only in how many
/// outputs they read.
fn annihilate_with(prog: &Program, window: &[Node], m: usize) -> Option<Vec<PlannedStep>> {
    let (x, drops) = window.split_first()?;
    if drops.len() != m || !drops.iter().all(is_drop) {
        return None;
    }
    let (n, actual) = node_arity(prog, x)?;
    if actual != m as i64 {
        return None;
    }
    // Dropping what a drop produced is not an annihilation, and hoisting it
    // would let the matcher chase its own tail.
    if is_drop(x) {
        return None;
    }
    at_window(
        prog,
        Rule::Annihilate {
            x: vec![x.clone()],
            n: usize::try_from(n).ok()?,
            m,
        },
        Direction::Forward,
    )
}

fn is_drop(node: &Node) -> bool {
    matches!(node, Node::Op(Instruction::Drop))
}

/// Puts a computation into the term, at a place a `drop` was already standing.
///
/// The annihilation law read backwards: `drop^n` becomes `X ; drop^m`, for the
/// `X : n -> m` the tactic named. Both sides discard exactly the same `n`
/// values, so the term means what it meant — but it now contains `X`, which is
/// something no rule reading the window could have supplied.
///
/// **This is the first matcher that takes an argument, and it has to.** Every
/// other one reads a shape and rewrites it, so what it produces is a function
/// of what it found. An introduction has nothing to read: `drop` says nothing
/// about what computation ought to appear in front of it. The term comes from
/// the tactic expression:
///
/// ```text
/// then(once(introduce { pick 0 }))
/// ```
///
/// It is what makes factoring reachable when only one arm has the code you want
/// to hoist. Give the other arm a `pick 0` it immediately discards, and the two
/// arms now share a prefix that `factor` can lift out — the copy having been
/// paid for in a place where it provably costs nothing.
///
/// Measure: none, and it *grows* the term. Aiming it is entirely the caller's
/// job, which is what `once`, `then`, `else` and `repeat_n` are for. Putting it
/// in a `repeat` will exhaust the budget.
#[derive(Debug)]
pub(crate) struct Introduce {
    x: Vec<Node>,
    /// `x`'s arity, worked out when the tactic was compiled. It is a property
    /// of the term alone — terms hold no calls — so it needs no library.
    n: usize,
    m: usize,
}

impl Introduce {
    pub(crate) fn new(prog: Option<&Program>, x: Vec<Node>) -> Result<Self, String> {
        let (n, m) = term_arity_or_why(prog, &x)?;
        if n == 0 {
            // Two reasons, and either would do. A term that consumes nothing
            // would match a window of no nodes, which is every position, so
            // `each` would never move past the first one. And it would gain
            // nothing: this law discards whatever the term produces, so
            // `push 7` could only ever become `push 7 ; drop`, which no
            // later step can use.
            return Err(
                "that consumes nothing, so there is no drop for it to stand in \
                 front of — and its result would be discarded on the spot"
                    .to_string(),
            );
        }
        Ok(Introduce { x, n, m })
    }
}

impl Matcher for Introduce {
    fn name(&self) -> &'static str {
        "introduce"
    }
    /// The `n` drops the term will stand in front of. A width that depends on
    /// the argument is the whole reason matchers are values rather than
    /// statics.
    fn width(&self) -> usize {
        self.n
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvIntroduce {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        }))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        if !window.iter().all(is_drop) {
            return None;
        }
        at_window(
            prog,
            Rule::Annihilate {
                x: self.x.clone(),
                n: self.n,
                m: self.m,
            },
            Direction::Reverse,
        )
    }
}

/// `X ; drop^m` becomes `drop^n`, for the `X : n -> m` the tactic named.
///
/// [`Introduce`] read backwards, which is [`Rule::Annihilate`] read forwards —
/// so it is [`Annihilate`]'s law, but reading a whole *term* rather than a
/// single node. That is the difference worth having: `annihilate` matches
/// `X ; drop` for one node `X`, where this matches the run of nodes the term
/// spells out, and so can take back out exactly what an `introduce` put in.
///
/// No name of its own: it is `inv(introduce { ... })`.
///
/// Measure: node count, as [`Annihilate`]'s is.
#[derive(Debug)]
pub(crate) struct InvIntroduce {
    x: Vec<Node>,
    n: usize,
    m: usize,
}

impl Matcher for InvIntroduce {
    fn name(&self) -> &'static str {
        "inv(introduce)"
    }
    /// The term, and the drops that follow it.
    fn width(&self) -> usize {
        self.x.len() + self.m
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Introduce {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        }))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let (term, drops) = window.split_at(self.x.len());
        if !same_effect_seq(term, &self.x) || !drops.iter().all(is_drop) {
            return None;
        }
        at_window(
            prog,
            Rule::Annihilate {
                x: self.x.clone(),
                n: self.n,
                m: self.m,
            },
            Direction::Forward,
        )
    }
}

/// `pick(n-1)^n ; X ; dip m { X }` becomes `X ; pick(m-1)^m`.
///
/// [`Rule::CopyNat`] read forward: common-subexpression elimination. Copying
/// the inputs and running `X` on both the copy and the original is running it
/// once and copying the outputs, because `X` answers the same twice.
///
/// **It takes a term, and has to.** The window cannot say what `X` is: for a
/// run of nodes there is nothing to mark where it begins, and the number of
/// `pick`s in front of it is `X`'s own input arity, which the matcher has to
/// know before it can ask for a window at all. So the tactic names it, the way
/// it names what to [`Introduce`] — and here it may name a *sentence*, since
/// running one function twice is the whole case this is for:
///
/// ```text
/// each(share { jump State::check })
/// ```
///
/// Measure: applications of `X`, which it strictly reduces. Safe in a fixpoint,
/// but not beside its own backward reading.
#[derive(Debug)]
pub(crate) struct Share {
    x: Vec<Node>,
    n: usize,
    m: usize,
}

impl Share {
    pub(crate) fn new(prog: Option<&Program>, x: Vec<Node>) -> Result<Self, String> {
        let (n, m) = term_arity_or_why(prog, &x)?;
        Ok(Share { x, n, m })
    }

    fn rule(&self) -> Rule {
        Rule::CopyNat {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        }
    }
}

impl Matcher for Share {
    fn name(&self) -> &'static str {
        "share"
    }
    /// The copies, the term, and the frame holding the second application.
    fn width(&self) -> usize {
        self.n + self.x.len() + 1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvShare {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        }))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        // The equation is closed over the term, so there is one shape to look
        // for and the applier will compare against it anyway. All this decides
        // is whether to propose.
        let rule = self.rule();
        if !same_effect_seq(window, &rule.lhs()) {
            return None;
        }
        at_window(prog, rule, Direction::Forward)
    }
}

/// `X ; pick(m-1)^m` becomes `pick(n-1)^n ; X ; dip m { X }`.
///
/// [`Rule::CopyNat`] read backwards: it un-shares, running `X` a second time
/// rather than copying what it left. That is how a computation gets delivered
/// to a place that needs its own copy — the same job `inv(annihilate)` does for
/// code that was never there at all, except that here the second copy is
/// provably the same value as the first.
///
/// No name of its own: it is `inv(share { ... })`.
///
/// Measure: none, and it grows the term.
#[derive(Debug)]
pub(crate) struct InvShare {
    x: Vec<Node>,
    n: usize,
    m: usize,
}

impl Matcher for InvShare {
    fn name(&self) -> &'static str {
        "inv(share)"
    }
    /// The term, and the copies of what it left.
    fn width(&self) -> usize {
        self.x.len() + self.m
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Share {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        }))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let rule = Rule::CopyNat {
            x: self.x.clone(),
            n: self.n,
            m: self.m,
        };
        if !same_effect_seq(window, &rule.rhs()) {
            return None;
        }
        at_window(prog, rule, Direction::Reverse)
    }
}

/// The arity of a term written in a tactic expression.
///
/// Terms are built from instructions and frames and never name a sentence, so
/// this answers without a library — which is what lets a tactic be compiled
/// before a program is loaded. `None` for anything whose reckoning stops, which
/// for a term means a `panic`.
pub(crate) fn term_arity(nodes: &[Node]) -> Option<(i64, i64)> {
    let mut inputs = 0i64;
    let mut size = 0i64;
    for node in nodes {
        let (n, m) = match node {
            Node::Op(inst) => bytecode::arity::op_arity(inst)?,
            Node::Dip { depth, body, .. } => {
                let (n, m) = term_arity(body)?;
                let d = *depth as i64;
                (d + n, d + m)
            }
            // A term cannot hold one, and if one appears the caller built it
            // rather than parsed it.
            Node::Call { .. } | Node::Branch { .. } => return None,
        };
        if size < n {
            inputs += n - size;
            size = n;
        }
        size = size - n + m;
    }
    Some((inputs, size))
}

/// `pick d ; drop` becomes nothing.
///
/// Copying a value and discarding the copy: neither happened. The counit law of
/// the comonoid whose comultiplication is `pick`.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct Counit;

impl Matcher for Counit {
    fn name(&self) -> &'static str {
        "counit"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "`pick d ; drop` = nothing, so the backward side is empty: there \
             is no window to recognize, and nothing to say which `d` to put \
             back. It is the generator's to emit, not a matcher's to find"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [Node::Op(Instruction::Pick(d)), drop] = window else {
            return None;
        };
        if !is_drop(drop) {
            return None;
        }
        at_window(prog, Rule::Counit { d: *d }, Direction::Forward)
    }
}

/// `roll 1 ; op` becomes `op`, for a commutative `op`.
///
/// `roll 1` swaps the top two values, and an operator that answers the same
/// either way round cannot tell. The commutative set — `add`, `multiply`,
/// `and`, `or`, `equal` — is a property of the instruction rather than of this
/// matcher, and `vm` measures it against the interpreter rather than trusting
/// the list.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct Comm;

impl Matcher for Comm {
    fn name(&self) -> &'static str {
        "comm"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Swap))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [Node::Op(Instruction::Roll(1)), Node::Op(op)] = window else {
            return None;
        };
        at_window(prog, Rule::Commute { op: op.clone() }, Direction::Forward)
    }
}

/// `op` becomes `roll 1 ; op`, for a commutative `op`.
///
/// The same law read backwards: it swaps the operands of a commutative
/// operator, which is how what sits *underneath* them gets rearranged to line
/// up with something else. `comm` then takes the shuffle away again once it has
/// done its work, or `interchange` carries it off.
///
/// Measure: none, and it grows the term — its own output contains the operator
/// it just matched, so `each` would put a second `roll 1` in front of it and
/// keep going. Aim it with `once`, `at` or a descent, as with `introduce`.
#[derive(Debug)]
pub(crate) struct Swap;

impl Matcher for Swap {
    fn name(&self) -> &'static str {
        "swap"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(Comm))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let Node::Op(op) = &window[0] else {
            return None;
        };
        at_window(prog, Rule::Commute { op: op.clone() }, Direction::Reverse)
    }
}

/// Splits an opaque value into the two cases where it is a boolean.
///
/// Puts `pick 0 ; is_bool ; branch { branch { push true } { push false } } { }`
/// in front of the node it is aimed at. The whole block is the identity, so the
/// term still means what it meant — but inside the inner arms the value has
/// been replaced by a **literal**, which every law that folds constants can act
/// on and none of them could reach before.
///
/// This is the only way to get a branch on an unknown condition into a term,
/// and so the only way to learn anything about a value that did not arrive as a
/// literal. Everything else needs the fact already on the stack.
///
/// It inserts *before* the window, so aiming is the whole job: `at(2,
/// split_bool)` puts the split in front of node 2. It reads one node only to
/// have somewhere to stand, and so cannot insert past the last one.
///
/// Measure: none, and it grows the term — its own output is a node it would
/// happily insert in front of again. Aim it with `once`, `at` or a descent, as
/// with `introduce` and `swap`.
#[derive(Debug)]
pub(crate) struct SplitBool;

impl Matcher for SplitBool {
    fn name(&self) -> &'static str {
        "split_bool"
    }
    fn width(&self) -> usize {
        1
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(UnsplitBool))
    }
    fn plan(&self, prog: &Program, _window: &[Node]) -> Option<Vec<PlannedStep>> {
        at_window(prog, Rule::SplitBool, Direction::Reverse)
    }
}

/// Removes a case split that has served its purpose.
///
/// [`SplitBool`] read forward: the whole guarded block is the identity, so once
/// the arms have been folded down to nothing interesting it can go.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct UnsplitBool;

impl Matcher for UnsplitBool {
    fn name(&self) -> &'static str {
        "unsplit_bool"
    }
    fn width(&self) -> usize {
        3
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(SplitBool))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        // The equation is closed, so the applier compares the window against
        // the one shape it has. All this decides is whether to bother.
        if !same_effect_seq(window, &Rule::SplitBool.lhs()) {
            return None;
        }
        at_window(prog, Rule::SplitBool, Direction::Forward)
    }
}

/// `push c ; pick 0` becomes `push c ; push c`.
///
/// Copying a constant is pushing it again. It is what makes a refinement pay:
/// downstream code reads a slot with `pick`, and a `pick` is opaque to every
/// law that folds literals.
///
/// Measure: the number of `push c; pick 0` adjacencies, which this strictly
/// decreases — its own output contains none.
#[derive(Debug)]
pub(crate) struct CopyConst;

impl Matcher for CopyConst {
    fn name(&self) -> &'static str {
        "copy_const"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvCopyConst))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Push(c)),
            Node::Op(Instruction::Pick(0)),
        ] = window
        else {
            return None;
        };
        at_window(prog, Rule::CopyConst { c: c.clone() }, Direction::Forward)
    }
}

/// `push c ; push c` becomes `push c ; pick 0`.
///
/// [`Rule::CopyConst`] read backwards. Pushing a literal twice is pushing it
/// and copying it, and the copy is what a law about *slots* can act on where a
/// second literal is just another literal.
///
/// No name of its own: it is `inv(copy_const)`.
///
/// Measure: none worth the name — it does not grow the term, but its output
/// contains no `push c ; push c`, so it settles where [`CopyConst`] does not
/// undo it. Never put the two in one `repeat`.
#[derive(Debug)]
pub(crate) struct InvCopyConst;

impl Matcher for InvCopyConst {
    fn name(&self) -> &'static str {
        "inv(copy_const)"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(CopyConst))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Push(a)),
            Node::Op(Instruction::Push(b)),
        ] = window
        else {
            return None;
        };
        if a != b {
            return None;
        }
        at_window(prog, Rule::CopyConst { c: a.clone() }, Direction::Reverse)
    }
}

/// `pick d ; pick 0` becomes `pick d ; dip 1 { pick d }`.
///
/// Duplication is coassociative. Neither side is smaller, and that is not the
/// point: the right-hand side puts one copy **in a frame**, and a framed
/// computation is one [`Float`] can carry. A bare `pick` cannot travel at all.
///
/// Measure: the number of `pick d; pick 0` adjacencies, which this strictly
/// decreases — its own output contains none.
#[derive(Debug)]
pub(crate) struct CopyAssoc;

impl Matcher for CopyAssoc {
    fn name(&self) -> &'static str {
        "copy_assoc"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(InvCopyAssoc))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Pick(d)),
            Node::Op(Instruction::Pick(0)),
        ] = window
        else {
            return None;
        };
        at_window(prog, Rule::CopyAssoc { d: *d }, Direction::Forward)
    }
}

/// `pick d ; dip 1 { pick d }` becomes `pick d ; pick 0`.
///
/// [`Rule::CopyAssoc`] read backwards, taking the second copy back out of its
/// frame once it has been carried to where it was wanted.
///
/// No name of its own: it is `inv(copy_assoc)`.
///
/// Measure: its output contains no `pick d ; dip 1 { pick d }`, so it settles
/// on its own — but not beside [`CopyAssoc`], which puts the frame back.
#[derive(Debug)]
pub(crate) struct InvCopyAssoc;

impl Matcher for InvCopyAssoc {
    fn name(&self) -> &'static str {
        "inv(copy_assoc)"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Ok(Box::new(CopyAssoc))
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Pick(d)),
            Node::Dip { depth: 1, body, .. },
        ] = window
        else {
            return None;
        };
        let [Node::Op(Instruction::Pick(inner))] = &body[..] else {
            return None;
        };
        if d != inner {
            return None;
        }
        at_window(prog, Rule::CopyAssoc { d: *d }, Direction::Reverse)
    }
}

/// `tuple n ; untuple n` becomes `push true`.
///
/// `untuple n` cannot fail on something `tuple n` just built, so the flag it
/// leaves is a literal `true`, and that literal is the whole residue of the
/// pair. The converse order is not a no-op and has no matcher.
///
/// Measure: node count.
#[derive(Debug)]
pub(crate) struct CancelTuple;

impl Matcher for CancelTuple {
    fn name(&self) -> &'static str {
        "cancel_tuple"
    }
    fn width(&self) -> usize {
        2
    }
    fn inverse(&self) -> Result<Box<dyn Matcher>, String> {
        Err(
            "the backward side of `cancel_tuple` is `push true`, which does \
             not say what `n` was — a tuple of any width leaves the same flag"
                .to_string(),
        )
    }
    fn plan(&self, prog: &Program, window: &[Node]) -> Option<Vec<PlannedStep>> {
        let [
            Node::Op(Instruction::Tuple(n)),
            Node::Op(Instruction::Untuple(m)),
        ] = window
        else {
            return None;
        };
        if n != m {
            return None;
        }
        at_window(prog, Rule::CancelTuple { n: *n }, Direction::Forward)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::applier::apply_script;
    use crate::rule::Step;
    use bytecode::{Library, SentenceIndex, Value, assemble};

    fn prog() -> Program<'static> {
        Program::new(Box::leak(Box::new(Library::new())))
    }

    fn op(i: Instruction) -> Node {
        Node::Op(i)
    }

    fn dip(depth: usize, body: Vec<Node>) -> Node {
        Node::Dip {
            depth,
            origins: Vec::new(),
            body,
        }
    }

    fn branch(then_body: Vec<Node>, else_body: Vec<Node>) -> Node {
        Node::Branch {
            then_origin: "then".to_string(),
            then_body,
            else_origin: "else".to_string(),
            else_body,
        }
    }

    /// Runs a matcher over a window and returns the rewritten sequence.
    ///
    /// This is the whole contract in one function: a matcher proposes, the
    /// applier disposes, and what comes back is what the old rule's `rewrite`
    /// would have returned directly.
    fn fire(m: &dyn Matcher, prog: &Program, window: &[Node]) -> Option<Vec<Node>> {
        let planned = m.plan(prog, window)?;
        assert!(!planned.is_empty(), "{} planned nothing", m.name());
        let script: Vec<Step> = planned
            .into_iter()
            .map(|p| Step {
                kind: p.kind,
                dir: p.dir,
                loc: p.rel.under(&[], 0),
            })
            .collect();
        let mut tree = window.to_vec();
        apply_script(prog, &mut tree, &script, true)
            .unwrap_or_else(|e| panic!("{} proposed a step that was refused: {}", m.name(), e));
        Some(tree)
    }

    // -- reading an equation backwards ---------------------------------------

    /// Fires `m`, then fires `inv(m)` on the result, and expects the window
    /// back.
    ///
    /// This is what `inv` promises, so it is asserted rather than described:
    /// two readings of one equation undo each other. Where the backward reading
    /// has a name of its own the pair is already tested by name; this covers
    /// every pair at once, including the ones reachable only through `inv`.
    fn round_trip(m: &dyn Matcher, window: &[Node]) {
        let there = fire(m, &prog(), window)
            .unwrap_or_else(|| panic!("{} declined {:?}", m.name(), window));
        let back = m
            .inverse()
            .unwrap_or_else(|why| panic!("{} has no inverse: {}", m.name(), why));
        assert_ne!(there, window, "{} changed nothing", m.name());
        assert_eq!(
            fire(&*back, &prog(), &there).as_deref(),
            Some(window),
            "{} did not undo {}",
            back.name(),
            m.name()
        );
    }

    #[test]
    fn every_matcher_says_which_way_it_reads_back() {
        // A matcher with no answer here would be a silent hole: `inv` of it
        // would report "unknown", which is a different claim from "that
        // reading cannot be searched for, and here is why".
        for name in matcher_names() {
            let m = matcher_by_name(name).unwrap();
            match m.inverse() {
                Ok(back) => {
                    // Reading back twice is reading forwards: `inv` is an
                    // involution, so `inv(inv(r))` is `r` rather than a third
                    // thing that happens to behave like it.
                    let again = back
                        .inverse()
                        .unwrap_or_else(|why| panic!("{} has no inverse: {}", back.name(), why));
                    assert_eq!(again.name(), m.name(), "inv(inv({})) drifted", name);
                }
                Err(why) => assert!(
                    why.len() > 20,
                    "{} declines an inverse without saying why",
                    name
                ),
            }
        }
    }

    #[test]
    fn the_unnamed_readings_undo_the_named_ones() {
        let d = |depth, body| dip(depth, body);
        // `inv(flatten)`: a frame that hides nothing, put back.
        round_trip(&Flatten, &[d(0, vec![op(Instruction::Add)])]);
        // `inv(fuse)`: one node split off the front of a body.
        round_trip(
            &InvFuse,
            &[d(2, vec![op(Instruction::Add), op(Instruction::Not)])],
        );
        // `inv(unfactor)`: a frame both arms open with, lifted out.
        round_trip(
            &Unfactor,
            &[
                d(1, vec![op(Instruction::Add)]),
                branch(vec![op(Instruction::Drop)], vec![op(Instruction::Not)]),
            ],
        );
        // `inv(distribute)`: a suffix both arms end with, taken out.
        round_trip(
            &Distribute,
            &[
                branch(vec![op(Instruction::Add)], vec![op(Instruction::Drop)]),
                op(Instruction::Not),
            ],
        );
        round_trip(
            &CopyConst,
            &[
                op(Instruction::Push(Value::Int(7))),
                op(Instruction::Pick(0)),
            ],
        );
        round_trip(
            &CopyAssoc,
            &[op(Instruction::Pick(3)), op(Instruction::Pick(0))],
        );
    }

    #[test]
    fn inv_flatten_wraps_one_node_in_a_frame_that_hides_nothing() {
        // Worth having on its own: a bare instruction cannot travel, and this
        // is what makes it into something the movement laws carry.
        assert_eq!(
            fire(&InvFlatten, &prog(), &[op(Instruction::Add)]),
            Some(vec![dip(0, vec![op(Instruction::Add)])])
        );
    }

    #[test]
    fn inv_fuse_splits_one_node_off_the_front() {
        let w = [dip(
            1,
            vec![
                op(Instruction::Add),
                op(Instruction::Not),
                op(Instruction::Drop),
            ],
        )];
        assert_eq!(
            fire(&InvFuse, &prog(), &w),
            Some(vec![
                dip(1, vec![op(Instruction::Add)]),
                dip(1, vec![op(Instruction::Not), op(Instruction::Drop)]),
            ])
        );
        // A body with nothing to split leaves an empty frame beside itself,
        // which is a change nothing can use.
        assert!(
            InvFuse
                .plan(&prog(), &[dip(1, vec![op(Instruction::Add)])])
                .is_none()
        );
    }

    #[test]
    fn inv_unfactor_lifts_a_frame_the_arms_share() {
        // Deeper than `factor` can reach on its own: the prefix is already
        // framed, at depth 2, and comes out at 3.
        let w = [branch(
            vec![dip(2, vec![op(Instruction::Add)]), op(Instruction::Drop)],
            vec![dip(2, vec![op(Instruction::Add)]), op(Instruction::Not)],
        )];
        assert_eq!(
            fire(&InvHoist, &prog(), &w),
            Some(vec![
                dip(3, vec![op(Instruction::Add)]),
                branch(vec![op(Instruction::Drop)], vec![op(Instruction::Not)]),
            ])
        );
        // Arms that open differently, and an unframed shared prefix — which is
        // `factor`'s business, since it has to wrap it first.
        assert!(
            InvHoist
                .plan(
                    &prog(),
                    &[branch(
                        vec![dip(1, vec![op(Instruction::Add)])],
                        vec![dip(2, vec![op(Instruction::Add)])],
                    )]
                )
                .is_none()
        );
        assert!(
            InvHoist
                .plan(
                    &prog(),
                    &[branch(
                        vec![op(Instruction::Add)],
                        vec![op(Instruction::Add)]
                    )]
                )
                .is_none()
        );
    }

    #[test]
    fn inv_distribute_factors_the_longest_shared_suffix() {
        // The move the old rule set could not express at all: `factor_branch`
        // only ever worked on prefixes.
        let w = [branch(
            vec![
                op(Instruction::Add),
                op(Instruction::Not),
                op(Instruction::Drop),
            ],
            vec![
                op(Instruction::Pick(0)),
                op(Instruction::Not),
                op(Instruction::Drop),
            ],
        )];
        assert_eq!(
            fire(&InvDistribute, &prog(), &w),
            Some(vec![
                branch(vec![op(Instruction::Add)], vec![op(Instruction::Pick(0))]),
                op(Instruction::Not),
                op(Instruction::Drop),
            ])
        );
        assert!(
            InvDistribute
                .plan(
                    &prog(),
                    &[branch(
                        vec![op(Instruction::Add)],
                        vec![op(Instruction::Not)]
                    )]
                )
                .is_none()
        );
    }

    #[test]
    fn share_runs_a_computation_once_and_copies_what_it_left() {
        // `equal` is (2 -> 1), so two picks in front and one after.
        let m = Share::new(None, vec![op(Instruction::Equal)]).unwrap();
        assert_eq!(m.width(), 4);
        let w = [
            op(Instruction::Pick(1)),
            op(Instruction::Pick(1)),
            op(Instruction::Equal),
            dip(1, vec![op(Instruction::Equal)]),
        ];
        assert_eq!(
            fire(&m, &prog(), &w),
            Some(vec![op(Instruction::Equal), op(Instruction::Pick(0))])
        );
        round_trip(&m, &w);

        // The copies have to be the ones the law names: `pick 0` twice copies
        // the top value twice over, which is a different program.
        let wrong = [
            op(Instruction::Pick(0)),
            op(Instruction::Pick(0)),
            op(Instruction::Equal),
            dip(1, vec![op(Instruction::Equal)]),
        ];
        assert!(m.plan(&prog(), &wrong).is_none());
    }

    #[test]
    fn share_reads_a_term_of_any_shape() {
        // Nothing to copy, which is the case `copy_const` is: the term needs
        // no inputs, so the law says only that the second application can be
        // replaced by a copy of the first.
        let m = Share::new(None, vec![op(Instruction::Push(Value::Int(7)))]).unwrap();
        assert_eq!(m.width(), 2, "no picks in front of it");
        round_trip(
            &m,
            &[
                op(Instruction::Push(Value::Int(7))),
                dip(1, vec![op(Instruction::Push(Value::Int(7)))]),
            ],
        );

        // And a term of more than one node, where nothing in the window could
        // have said where the computation began.
        let term = vec![op(Instruction::Pick(0)), op(Instruction::IsBool)];
        let m = Share::new(None, term.clone()).unwrap();
        assert_eq!(m.width(), 1 + 2 + 1, "one pick, the term, the frame");
        let mut w = vec![op(Instruction::Pick(0))];
        w.extend(term.clone());
        w.push(dip(2, term));
        round_trip(&m, &w);
    }

    #[test]
    fn share_needs_a_term_it_can_state_the_law_at() {
        assert!(Share::new(None, Vec::new()).is_err());
        // `panic` has no arity, so there is no saying what it reads or leaves.
        let err = Share::new(None, vec![op(Instruction::Panic)]).unwrap_err();
        assert!(err.contains("arity"), "{}", err);
    }

    #[test]
    fn inv_introduce_reads_the_whole_term_where_annihilate_reads_one_node() {
        // `pick 0` is (1 -> 2), so the introduction stands in front of one drop
        // and leaves two; reading it back takes all three nodes.
        let m = Introduce::new(None, vec![op(Instruction::Pick(0))]).unwrap();
        round_trip(&m, &[op(Instruction::Drop)]);

        // A term of more than one node, which `annihilate` cannot match: it
        // reads `X ; drop` for a single node `X`.
        let term = vec![op(Instruction::Pick(0)), op(Instruction::IsBool)];
        let m = Introduce::new(None, term.clone()).unwrap();
        round_trip(&m, &[op(Instruction::Drop)]);
        let back = m.inverse().unwrap();
        assert_eq!(back.width(), 4, "the term, then the drops it leaves");
        assert!(
            Annihilate
                .plan(&prog(), &[term[0].clone(), term[1].clone()])
                .is_none(),
            "annihilate should not reach a two-node term"
        );
    }

    // -- frames -------------------------------------------------------------

    #[test]
    fn collapse_merges_a_dip_whose_body_is_one_dip() {
        let w = [dip(2, vec![dip(3, vec![op(Instruction::Add)])])];
        assert_eq!(
            fire(&Collapse, &prog(), &w),
            Some(vec![dip(5, vec![op(Instruction::Add)])])
        );
    }

    #[test]
    fn collapse_declines_a_body_that_is_more_than_one_dip() {
        let w = [dip(2, vec![dip(1, vec![]), op(Instruction::Add)])];
        assert!(Collapse.plan(&prog(), &w).is_none());
    }

    #[test]
    fn expand_peels_exactly_one_level() {
        let w = [dip(3, vec![op(Instruction::Add)])];
        assert_eq!(
            fire(&Expand, &prog(), &w),
            Some(vec![dip(1, vec![dip(2, vec![op(Instruction::Add)])])])
        );
    }

    #[test]
    fn expand_leaves_a_plain_call_and_a_unary_dip_alone() {
        assert!(Expand.plan(&prog(), &[dip(0, vec![])]).is_none());
        assert!(Expand.plan(&prog(), &[dip(1, vec![])]).is_none());
    }

    #[test]
    fn expand_and_collapse_are_inverse() {
        let w = [dip(4, vec![op(Instruction::Add)])];
        let expanded = fire(&Expand, &prog(), &w).unwrap();
        assert_eq!(fire(&Collapse, &prog(), &expanded), Some(w.to_vec()));
    }

    #[test]
    fn flatten_splices_a_frame_that_hides_nothing() {
        let w = [dip(0, vec![op(Instruction::Add), op(Instruction::Not)])];
        assert_eq!(
            fire(&Flatten, &prog(), &w),
            Some(vec![op(Instruction::Add), op(Instruction::Not)])
        );
    }

    #[test]
    fn flatten_removes_an_empty_frame_outright() {
        assert_eq!(fire(&Flatten, &prog(), &[dip(0, vec![])]), Some(Vec::new()));
    }

    #[test]
    fn flatten_declines_a_frame_that_hides_something() {
        assert!(Flatten.plan(&prog(), &[dip(1, vec![])]).is_none());
    }

    #[test]
    fn fuse_joins_two_frames_at_the_same_depth() {
        let w = [
            dip(2, vec![op(Instruction::Add)]),
            dip(2, vec![op(Instruction::Not)]),
        ];
        assert_eq!(
            fire(&Fuse, &prog(), &w),
            Some(vec![dip(
                2,
                vec![op(Instruction::Add), op(Instruction::Not)]
            )])
        );
    }

    #[test]
    fn fuse_declines_different_depths() {
        let w = [dip(1, vec![]), dip(2, vec![])];
        assert!(Fuse.plan(&prog(), &w).is_none());
    }

    // -- interchange --------------------------------------------------------

    #[test]
    fn sink_widens_past_an_operator_that_consumes_two() {
        // `add` is (2 -> 2), the second output being its success flag: 2 >= 2
        // clears the window, and the same window is 2 - 2 + 2 = 2 deep beyond.
        let w = [op(Instruction::Add), dip(2, vec![])];
        assert_eq!(
            fire(&Sink, &prog(), &w),
            Some(vec![dip(2, vec![]), op(Instruction::Add)])
        );
        // One shallower and the dip would be rewriting the flag.
        assert!(
            Sink.plan(&prog(), &[op(Instruction::Add), dip(1, vec![])])
                .is_none()
        );
    }

    #[test]
    fn sink_narrows_past_a_push() {
        let w = [op(Instruction::Push(Value::Int(1))), dip(1, vec![])];
        assert_eq!(
            fire(&Sink, &prog(), &w),
            Some(vec![dip(0, vec![]), op(Instruction::Push(Value::Int(1)))])
        );
    }

    #[test]
    fn sink_moves_an_unexpanded_call_by_its_frame_alone() {
        // The side condition is about the frame; the callee's body has no say.
        let call = Node::Call {
            depth: 2,
            target: SentenceIndex::from(0),
        };
        let w = [op(Instruction::Add), call];
        let got = fire(&Sink, &prog(), &w).unwrap();
        assert!(matches!(got[0], Node::Call { depth: 2, .. }));
        assert_eq!(got[1], op(Instruction::Add));
    }

    #[test]
    fn sink_declines_past_a_panic() {
        // `panic` has no arity, so nothing can be said about moving past it.
        let w = [op(Instruction::Panic), dip(3, vec![])];
        assert!(Sink.plan(&prog(), &w).is_none());
    }

    #[test]
    fn float_and_sink_are_inverse_on_everything_that_moves() {
        // One law, two ways of looking for it.
        for (x, depth) in [
            (op(Instruction::Add), 2usize),
            (op(Instruction::Push(Value::Int(1))), 1),
            (op(Instruction::Drop), 0),
            (op(Instruction::Pick(2)), 4),
            (op(Instruction::Roll(1)), 2),
        ] {
            let w = [x.clone(), dip(depth, vec![op(Instruction::Not)])];
            let Some(sunk) = fire(&Sink, &prog(), &w) else {
                panic!("sink declined {:?} at depth {}", x, depth)
            };
            assert_eq!(
                fire(&Float, &prog(), &sunk),
                Some(w.to_vec()),
                "float did not undo sink for {:?}",
                x
            );
        }
    }

    #[test]
    fn float_declines_a_window_that_holds_what_x_consumes() {
        // `add` consumes two; a window one deep does not contain both.
        let w = [dip(1, vec![]), op(Instruction::Add)];
        assert!(Float.plan(&prog(), &w).is_none());
    }

    // -- branches -----------------------------------------------------------

    #[test]
    fn factor_hoists_a_shared_prefix_out_of_both_arms() {
        let w = [branch(
            vec![op(Instruction::Add), op(Instruction::Drop)],
            vec![op(Instruction::Add), op(Instruction::Not)],
        )];
        assert_eq!(
            fire(&Factor, &prog(), &w),
            Some(vec![
                dip(1, vec![op(Instruction::Add)]),
                branch(vec![op(Instruction::Drop)], vec![op(Instruction::Not)]),
            ])
        );
    }

    #[test]
    fn factor_takes_the_whole_shared_run_at_once() {
        let shared = vec![op(Instruction::Add), op(Instruction::Not)];
        let mut then_arm = shared.clone();
        then_arm.push(op(Instruction::Drop));
        let mut else_arm = shared.clone();
        else_arm.push(op(Instruction::Pick(0)));
        let w = [branch(then_arm, else_arm)];
        assert_eq!(
            fire(&Factor, &prog(), &w),
            Some(vec![
                dip(1, shared),
                branch(vec![op(Instruction::Drop)], vec![op(Instruction::Pick(0))]),
            ])
        );
    }

    #[test]
    fn factor_is_three_steps() {
        // The shape of the firing, not just its result: two frames introduced,
        // one lifted. Each is an instance of a law.
        let w = [branch(
            vec![op(Instruction::Add)],
            vec![op(Instruction::Add)],
        )];
        let planned = Factor.plan(&prog(), &w).unwrap();
        assert_eq!(planned.len(), 3);
        assert_eq!(planned[0].kind.name(), "elim_dip0");
        assert_eq!(planned[1].kind.name(), "elim_dip0");
        assert_eq!(planned[2].kind.name(), "hoist");
        assert!(planned.iter().all(|p| p.dir == Direction::Reverse));
    }

    #[test]
    fn factor_declines_arms_that_share_no_prefix() {
        let w = [branch(
            vec![op(Instruction::Add)],
            vec![op(Instruction::Not)],
        )];
        assert!(Factor.plan(&prog(), &w).is_none());
    }

    #[test]
    fn factor_compares_arms_by_effect_not_by_label() {
        // Two identical blocks compiled to different sentences never share a
        // label, and used to make factoring miss every shared prefix that
        // contained one.
        let block = |origin: &str| Node::Dip {
            depth: 1,
            origins: vec![origin.to_string()],
            body: vec![op(Instruction::Add)],
        };
        let w = [branch(
            vec![block("#3 a"), op(Instruction::Drop)],
            vec![block("#9 b"), op(Instruction::Not)],
        )];
        let got = fire(&Factor, &prog(), &w).unwrap();
        assert_eq!(got.len(), 2);
        assert!(matches!(got[0], Node::Dip { depth: 1, .. }));
    }

    #[test]
    fn unfactor_pushes_a_block_into_both_arms_one_shallower() {
        let w = [
            dip(1, vec![op(Instruction::Add)]),
            branch(vec![op(Instruction::Drop)], vec![]),
        ];
        assert_eq!(
            fire(&Unfactor, &prog(), &w),
            Some(vec![branch(
                vec![dip(0, vec![op(Instruction::Add)]), op(Instruction::Drop)],
                vec![dip(0, vec![op(Instruction::Add)])],
            )])
        );
    }

    #[test]
    fn unfactor_declines_a_window_that_does_not_hold_the_condition() {
        let w = [dip(0, vec![op(Instruction::Add)]), branch(vec![], vec![])];
        assert!(Unfactor.plan(&prog(), &w).is_none());
    }

    #[test]
    fn distribute_moves_a_following_node_into_both_arms() {
        let w = [
            branch(vec![op(Instruction::Add)], vec![]),
            op(Instruction::Not),
        ];
        assert_eq!(
            fire(&Distribute, &prog(), &w),
            Some(vec![branch(
                vec![op(Instruction::Add), op(Instruction::Not)],
                vec![op(Instruction::Not)],
            )])
        );
    }

    #[test]
    fn fold_branch_takes_the_arm_the_literal_selects() {
        let w = |c: Value| {
            [
                op(Instruction::Push(c)),
                branch(vec![op(Instruction::Add)], vec![op(Instruction::Not)]),
            ]
        };
        assert_eq!(
            fire(&FoldBranch, &prog(), &w(Value::Bool(true))),
            Some(vec![op(Instruction::Add)])
        );
        assert_eq!(
            fire(&FoldBranch, &prog(), &w(Value::Bool(false))),
            Some(vec![op(Instruction::Not)])
        );
        // Not a bool at all: `false` is the only falsy value, so the branch
        // takes the then arm, and so does this.
        assert_eq!(
            fire(&FoldBranch, &prog(), &w(Value::Int(1))),
            Some(vec![op(Instruction::Add)])
        );
    }

    #[test]
    fn fold_branch_declines_a_computed_condition() {
        let w = [op(Instruction::Pick(0)), branch(vec![], vec![])];
        assert!(FoldBranch.plan(&prog(), &w).is_none());
    }

    // -- values -------------------------------------------------------------

    #[test]
    fn eval_folds_a_binary_operator_on_two_literals() {
        let w = [
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Equal),
        ];
        assert_eq!(
            fire(&EvalBinary, &prog(), &w),
            Some(vec![op(Instruction::Push(Value::Bool(true)))])
        );
    }

    #[test]
    fn eval_produces_the_flag_of_a_fallible_comparison() {
        let w = [
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Push(Value::Int(2))),
            op(Instruction::Less),
        ];
        assert_eq!(
            fire(&EvalBinary, &prog(), &w),
            Some(vec![
                op(Instruction::Push(Value::Bool(true))),
                op(Instruction::Push(Value::Bool(true))),
            ])
        );
    }

    #[test]
    fn eval_declines_an_operator_it_has_no_answer_for() {
        let w = [
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Push(Value::Int(2))),
            op(Instruction::Add),
        ];
        assert!(EvalBinary.plan(&prog(), &w).is_none());
        // And a third push is not an operator.
        let w = [
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Push(Value::Int(2))),
            op(Instruction::Push(Value::Int(3))),
        ];
        assert!(EvalBinary.plan(&prog(), &w).is_none());
    }

    #[test]
    fn eval_folds_a_unary_operator() {
        // `not` goes through `truthy`, so a non-boolean is *true* and negates
        // to `false` rather than being rejected.
        let w = [op(Instruction::Push(Value::Int(7))), op(Instruction::Not)];
        assert_eq!(
            fire(&EvalUnary, &prog(), &w),
            Some(vec![op(Instruction::Push(Value::Bool(false)))])
        );
        // And a type test answers on every literal.
        let w = [op(Instruction::Push(Value::Int(7))), op(Instruction::IsInt)];
        assert_eq!(
            fire(&EvalUnary, &prog(), &w),
            Some(vec![op(Instruction::Push(Value::Bool(true)))])
        );
    }

    #[test]
    fn annihilate_trades_a_result_for_its_operands() {
        // `equal` is (2 -> 1): dropping the answer is dropping both operands.
        let w = [op(Instruction::Equal), op(Instruction::Drop)];
        assert_eq!(
            fire(&Annihilate, &prog(), &w),
            Some(vec![op(Instruction::Drop), op(Instruction::Drop)])
        );
    }

    #[test]
    fn annihilate_cancels_a_push_against_a_drop() {
        // `push` is (0 -> 1), so there is nothing left at all.
        let w = [op(Instruction::Push(Value::Int(1))), op(Instruction::Drop)];
        assert_eq!(fire(&Annihilate, &prog(), &w), Some(Vec::new()));
    }

    #[test]
    fn annihilate_flagged_reads_a_value_and_its_flag() {
        // `add` is (2 -> 2) now that the flag is explicit, so what cancels it
        // is two drops.
        let w = [
            op(Instruction::Add),
            op(Instruction::Drop),
            op(Instruction::Drop),
        ];
        assert_eq!(
            fire(&AnnihilateFlagged, &prog(), &w),
            Some(vec![op(Instruction::Drop), op(Instruction::Drop)])
        );
    }

    #[test]
    fn annihilate_flagged_takes_a_pick_whose_copies_both_go() {
        // `pick 0` is (1 -> 2).
        let w = [
            op(Instruction::Pick(0)),
            op(Instruction::Drop),
            op(Instruction::Drop),
        ];
        assert_eq!(
            fire(&AnnihilateFlagged, &prog(), &w),
            Some(vec![op(Instruction::Drop)])
        );
    }

    #[test]
    fn annihilate_reaches_a_frame_the_old_whitelist_refused() {
        // Under the global precondition there is no hidden `assert`, so a
        // framed computation annihilates like any other. `dip 1 { equal }` is
        // (3 -> 2).
        let w = [
            dip(1, vec![op(Instruction::Equal)]),
            op(Instruction::Drop),
            op(Instruction::Drop),
        ];
        assert_eq!(
            fire(&AnnihilateFlagged, &prog(), &w),
            Some(vec![
                op(Instruction::Drop),
                op(Instruction::Drop),
                op(Instruction::Drop)
            ])
        );
    }

    #[test]
    fn annihilate_leaves_a_pick_to_the_counit_law() {
        // `pick d` is (d+1 -> d+2), so it is not of annihilate's shape at all
        // and neither matcher has to know about the other.
        let w = [op(Instruction::Pick(2)), op(Instruction::Drop)];
        assert!(Annihilate.plan(&prog(), &w).is_none());
        assert_eq!(fire(&Counit, &prog(), &w), Some(Vec::new()));
    }

    #[test]
    fn comm_removes_a_swap_before_a_commutative_operator() {
        for inst in [
            Instruction::Add,
            Instruction::Multiply,
            Instruction::And,
            Instruction::Or,
            Instruction::Equal,
        ] {
            let w = [op(Instruction::Roll(1)), op(inst.clone())];
            assert_eq!(
                fire(&Comm, &prog(), &w),
                Some(vec![op(inst.clone())]),
                "{:?}",
                inst
            );
        }
    }

    #[test]
    fn comm_declines_an_operator_that_reads_its_operands_in_order() {
        for inst in [
            Instruction::Subtract,
            Instruction::Less,
            Instruction::Tuple(2),
        ] {
            let w = [op(Instruction::Roll(1)), op(inst.clone())];
            assert!(Comm.plan(&prog(), &w).is_none(), "{:?}", inst);
        }
        // And a deeper roll is not a swap of the top two.
        let w = [op(Instruction::Roll(2)), op(Instruction::Add)];
        assert!(Comm.plan(&prog(), &w).is_none());
    }

    #[test]
    fn swap_introduces_the_shuffle_comm_removes() {
        let w = [op(Instruction::Add)];
        assert_eq!(
            fire(&Swap, &prog(), &w),
            Some(vec![op(Instruction::Roll(1)), op(Instruction::Add)])
        );
        // And straight back out again: two readings of one law.
        let there = fire(&Swap, &prog(), &w).unwrap();
        assert_eq!(fire(&Comm, &prog(), &there), Some(w.to_vec()));
    }

    #[test]
    fn swap_declines_what_comm_declines() {
        assert!(Swap.plan(&prog(), &[op(Instruction::Subtract)]).is_none());
        assert!(Swap.plan(&prog(), &[op(Instruction::Not)]).is_none());
        assert!(Swap.plan(&prog(), &[dip(1, Vec::new())]).is_none());
    }

    #[test]
    fn split_bool_puts_the_two_cases_in_front_of_what_it_is_aimed_at() {
        let w = [op(Instruction::Not)];
        let got = fire(&SplitBool, &prog(), &w).unwrap();
        assert_eq!(got.len(), 4, "{:?}", got);
        assert_eq!(got[0], op(Instruction::Pick(0)));
        assert_eq!(got[1], op(Instruction::IsBool));
        assert_eq!(got[3], op(Instruction::Not), "it did not insert in front");
    }

    #[test]
    fn unsplit_bool_takes_the_split_back_out() {
        let split = fire(&SplitBool, &prog(), &[op(Instruction::Not)]).unwrap();
        // The guard block is the first three nodes; `not` is what it stood in
        // front of.
        assert_eq!(
            fire(&UnsplitBool, &prog(), &split[..3]),
            Some(Vec::new()),
            "{:?}",
            split
        );
    }

    #[test]
    fn unsplit_bool_declines_a_block_that_is_not_the_split() {
        // A guard over different arms is a different program.
        let wrong = [
            op(Instruction::Pick(0)),
            op(Instruction::IsBool),
            branch(vec![op(Instruction::Drop)], Vec::new()),
        ];
        assert!(UnsplitBool.plan(&prog(), &wrong).is_none());
        // And so is the same shape guarded on something else.
        let wrong = [
            op(Instruction::Pick(0)),
            op(Instruction::IsInt),
            Rule::SplitBool.lhs()[2].clone(),
        ];
        assert!(UnsplitBool.plan(&prog(), &wrong).is_none());
    }

    #[test]
    fn copy_const_turns_a_copy_back_into_a_push() {
        let w = [
            op(Instruction::Push(Value::Int(7))),
            op(Instruction::Pick(0)),
        ];
        assert_eq!(
            fire(&CopyConst, &prog(), &w),
            Some(vec![
                op(Instruction::Push(Value::Int(7))),
                op(Instruction::Push(Value::Int(7))),
            ])
        );
    }

    #[test]
    fn copy_assoc_puts_the_second_copy_in_a_frame() {
        let w = [op(Instruction::Pick(2)), op(Instruction::Pick(0))];
        assert_eq!(
            fire(&CopyAssoc, &prog(), &w),
            Some(vec![
                op(Instruction::Pick(2)),
                dip(1, vec![op(Instruction::Pick(2))]),
            ])
        );
    }

    #[test]
    fn cancel_tuple_leaves_the_flag_behind() {
        let w = [op(Instruction::Tuple(3)), op(Instruction::Untuple(3))];
        assert_eq!(
            fire(&CancelTuple, &prog(), &w),
            Some(vec![op(Instruction::Push(Value::Bool(true)))])
        );
        // Different widths are not a cancelling pair.
        let w = [op(Instruction::Tuple(3)), op(Instruction::Untuple(2))];
        assert!(CancelTuple.plan(&prog(), &w).is_none());
    }

    // -- unfold -------------------------------------------------------------

    #[test]
    fn unfold_opens_a_call_and_refuses_a_recursive_one() {
        let library: &'static Library = Box::leak(Box::new(
            assemble(
                r#"
                sentence pushy { push 7 }
                #[recursive] sentence loops { jump loops }
                "#,
            )
            .unwrap(),
        ));
        let prog = Program::new(library);
        let idx = |name: &str| {
            library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(i, _)| i)
                .unwrap()
        };

        let w = [Node::Call {
            depth: 0,
            target: idx("pushy"),
        }];
        assert_eq!(
            fire(&Unfold, &prog, &w),
            Some(vec![op(Instruction::Push(Value::Int(7)))])
        );

        let w = [Node::Call {
            depth: 0,
            target: idx("loops"),
        }];
        assert!(Unfold.plan(&prog, &w).is_none());
    }

    // -- introduce ----------------------------------------------------------

    fn introduce(term: Vec<Node>) -> Introduce {
        Introduce::new(None, term).unwrap_or_else(|e| panic!("{}", e))
    }

    #[test]
    fn introduce_puts_the_named_code_in_front_of_the_drops_it_pays_for() {
        // `pick 0` is (1 -> 2), so it stands in front of one drop and brings
        // two of its own. Both sides discard exactly one value.
        let m = introduce(vec![op(Instruction::Pick(0))]);
        assert_eq!(m.width(), 1);
        assert_eq!(
            fire(&m, &prog(), &[op(Instruction::Drop)]),
            Some(vec![
                op(Instruction::Pick(0)),
                op(Instruction::Drop),
                op(Instruction::Drop),
            ])
        );
    }

    #[test]
    fn introduce_reads_as_many_drops_as_the_term_consumes() {
        // `add` is (2 -> 2): it stands in front of *two* drops. A matcher whose
        // width depends on its argument is why matchers are values.
        let m = introduce(vec![op(Instruction::Add)]);
        assert_eq!(m.width(), 2);
        let w = [op(Instruction::Drop), op(Instruction::Drop)];
        assert_eq!(
            fire(&m, &prog(), &w),
            Some(vec![
                op(Instruction::Add),
                op(Instruction::Drop),
                op(Instruction::Drop),
            ])
        );
    }

    #[test]
    fn introduce_declines_a_window_that_is_not_all_drops() {
        let m = introduce(vec![op(Instruction::Add)]);
        assert!(
            m.plan(&prog(), &[op(Instruction::Drop), op(Instruction::Not)])
                .is_none()
        );
    }

    #[test]
    fn a_term_that_consumes_nothing_is_refused() {
        // `push 7` is (0 -> 1). A width-0 matcher matches at every position,
        // so `each` would never move past the first — and the law discards
        // what the term makes anyway, so there would be nothing to gain.
        let err = Introduce::new(None, vec![op(Instruction::Push(Value::Int(7)))]).unwrap_err();
        assert!(err.contains("consumes nothing"), "{}", err);
    }

    #[test]
    fn introduce_takes_a_whole_sequence() {
        let m = introduce(vec![op(Instruction::Pick(0)), op(Instruction::IsBool)]);
        // pick 0 is (1 -> 2), is_bool is (1 -> 1): together (1 -> 2).
        assert_eq!(m.width(), 1);
        let got = fire(&m, &prog(), &[op(Instruction::Drop)]).unwrap();
        assert_eq!(got.len(), 4, "{:?}", got);
    }

    #[test]
    fn introduce_refuses_a_term_with_no_arity() {
        assert!(Introduce::new(None, Vec::new()).is_err());
        assert!(Introduce::new(None, vec![op(Instruction::Panic)]).is_err());
    }

    #[test]
    fn the_introduced_code_is_undone_by_annihilate() {
        // Forward and backward readings of one law, so what `introduce` puts in
        // `annihilate` takes straight back out.
        let m = introduce(vec![op(Instruction::Pick(0))]);
        let with = fire(&m, &prog(), &[op(Instruction::Drop)]).unwrap();
        // `pick 0 ; drop` is the counit; the remaining `drop` is the original.
        assert_eq!(
            fire(&Counit, &prog(), &with[..2]),
            Some(Vec::new()),
            "{:?}",
            with
        );
    }

    #[test]
    fn term_arity_reckons_frames_without_a_library() {
        assert_eq!(term_arity(&[op(Instruction::Pick(0))]), Some((1, 2)));
        assert_eq!(
            term_arity(&[dip(2, vec![op(Instruction::Drop)])]),
            Some((3, 2))
        );
        assert_eq!(term_arity(&[]), Some((0, 0)));
        assert_eq!(term_arity(&[op(Instruction::Panic)]), None);
    }

    // -- the registry -------------------------------------------------------

    #[test]
    fn every_matcher_is_named_once_and_findable() {
        let names = matcher_names();
        let mut unique = names.clone();
        unique.dedup();
        assert_eq!(names.len(), unique.len(), "two matchers share a name");
        // The constructor and the name list are separate, so they can drift.
        // This is where that would show up.
        for name in &names {
            assert_eq!(
                matcher_by_name(name).map(|m| m.name()),
                Some(*name),
                "`{}` is listed but does not construct as itself",
                name
            );
        }
        assert!(matcher_by_name("no_such_matcher").is_none());
        for name in term_matcher_names() {
            assert!(
                matcher_by_name(name).is_none(),
                "`{}` needs a term and must not construct without one",
                name
            );
            let built = matcher_with_term(name, vec![op(Instruction::Pick(0))], None)
                .unwrap_or_else(|| panic!("`{}` is listed but takes no term", name))
                .unwrap_or_else(|e| panic!("`{}` rejected a plain term: {}", name, e));
            assert_eq!(built.name(), name);
        }
        assert!(matcher_with_term("sink", Vec::new(), None).is_none());
    }

    #[test]
    fn no_matcher_proposes_a_step_the_applier_would_refuse() {
        // A matcher checks its own side conditions, so anything it plans must
        // apply. Sweep every matcher over a corpus of windows and hold it to
        // that — `fire` panics if the applier refuses.
        let prog = prog();
        let corpus: Vec<Node> = vec![
            op(Instruction::Add),
            op(Instruction::Drop),
            op(Instruction::Not),
            op(Instruction::Equal),
            op(Instruction::Pick(0)),
            op(Instruction::Pick(2)),
            op(Instruction::Roll(1)),
            op(Instruction::Push(Value::Int(1))),
            op(Instruction::Push(Value::Bool(true))),
            op(Instruction::Tuple(2)),
            op(Instruction::Untuple(2)),
            op(Instruction::Panic),
            dip(0, vec![op(Instruction::Add)]),
            dip(1, vec![op(Instruction::Not)]),
            dip(2, vec![dip(1, vec![op(Instruction::Add)])]),
            branch(vec![op(Instruction::Add)], vec![op(Instruction::Add)]),
            branch(vec![op(Instruction::Not)], vec![]),
        ];

        let mut fired = 0;
        let mut all: Vec<Box<dyn Matcher>> = matcher_names()
            .into_iter()
            .filter_map(matcher_by_name)
            .collect();
        all.push(
            matcher_with_term("introduce", vec![op(Instruction::Pick(0))], None)
                .unwrap()
                .unwrap(),
        );
        for m in &all {
            let width = m.width();
            // Every window of this width over the corpus, in both orders, so
            // that pairs like `push ; pick 0` and `pick 0 ; push` both occur.
            for i in 0..corpus.len() {
                for j in 0..corpus.len() {
                    let mut window: Vec<Node> = Vec::new();
                    for k in 0..width {
                        window.push(corpus[(i + j * k) % corpus.len()].clone());
                    }
                    if fire(m.as_ref(), &prog, &window).is_some() {
                        fired += 1;
                    }
                }
            }
        }
        // A lower bound rather than an exact count: the point is that the sweep
        // is doing real work, so that "nothing was refused" is not vacuous.
        assert!(fired > 100, "the sweep only fired {} times", fired);
    }
}
