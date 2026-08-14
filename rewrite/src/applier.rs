//! Applying a rewrite script, mechanically.
//!
//! This is the only code in the tool that changes a term. A live run and a
//! replay go through it alike, which is what makes a script a faithful record
//! of a derivation rather than a log written alongside one.
//!
//! Applying a step is deliberately not a search. The equation regenerates the
//! side it expects to find, the window is compared against it, and anything
//! short of an exact match — by effect; provenance is not part of a term's
//! identity — is a failure rather than an invitation to look elsewhere. A
//! script that no longer fits its program says so at the step that stopped
//! fitting.
//!
//! ## Windows, and why composition being associative is what makes them work
//!
//! A step names a run of adjacent factors of one spine. `A ; (B ; C)` and
//! `(A ; B) ; C` are the same program, so the applier reads the term it lands
//! in as its spine, splices there, and rebuilds — which means an equation whose
//! left-hand side is `swap ; swap` matches wherever those two sit next to each
//! other, without the parenthesization having to agree. See [`crate::ir`].
//!
//! Nothing here trusts the script. Side conditions are re-checked against the
//! library on every application (see [`Rule::check`]), so a step whose
//! arguments claim an arity the library does not give is refused no matter how
//! it came to be written.

use crate::arity::{seq_arity, term_arity};
use crate::ir::{
    Selector, Term, aligned, child_seq, cloned, expand_call, pad, same_effect_refs, sketch,
    sketch_head, unpad,
};
use crate::location::{Location, selector_name};
use crate::program::Program;
use crate::rule::{Direction, SideCondition, Step, StepKind};

/// What a step did to the spine it landed in.
///
/// The counts are what a driver needs to know where to carry on scanning; the
/// applier itself has no opinion about that.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SpliceInfo {
    pub(crate) removed: usize,
    pub(crate) inserted: usize,
}

/// Why a step could not be applied.
///
/// The context is the same for every cause — which step, which rule, which way
/// round, and where — so it is carried once here rather than repeated in each
/// variant.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ApplyError {
    pub(crate) step: usize,
    pub(crate) rule: &'static str,
    pub(crate) dir: Direction,
    pub(crate) loc: Location,
    pub(crate) cause: Cause,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Cause {
    /// The descent named a factor that is not there.
    PathIndex {
        depth: usize,
        index: usize,
        len: usize,
    },
    /// The descent asked for a kind of sub-term the factor does not have — a
    /// `then` arm of a `par`, say.
    PathKind {
        depth: usize,
        selector: Selector,
        found: String,
    },
    /// The window runs off the end of the spine it starts in.
    WindowRange { at: usize, need: usize, len: usize },
    /// The window is there but is not what the equation says it should be.
    WindowMismatch { expected: String, found: String },
    /// The arguments do not satisfy the equation.
    SideCondition(SideCondition),
    /// `--check`: the two sides of the equation are stated at different types.
    ArityChanged {
        before: Option<(i64, i64)>,
        after: Option<(i64, i64)>,
    },
    /// The replacement demands a deeper stack than the term it lands in has, so
    /// there is no padding that would make it fit.
    TooShallow { entry: i64, needs: i64 },
}

impl std::fmt::Display for ApplyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "step {} ({} {} {}): ",
            self.step,
            self.rule,
            self.dir.arrow(),
            self.loc
        )?;
        match &self.cause {
            Cause::PathIndex { depth, index, len } => write!(
                f,
                "the path turns at factor {} on the way down (leg {}), but that \
                 term holds {}",
                index, depth, len
            ),
            Cause::PathKind {
                depth,
                selector,
                found,
            } => write!(
                f,
                "the path asks for the {} of `{}` (leg {}), which has no such part",
                selector_name(*selector),
                found,
                depth
            ),
            Cause::WindowRange { at, need, len } => write!(
                f,
                "the window wants {} factor(s) from @{}, but the term holds {}",
                need, at, len
            ),
            Cause::WindowMismatch { expected, found } => write!(
                f,
                "the window does not match the equation.\n  expected: {}\n  found:    {}",
                expected, found
            ),
            Cause::SideCondition(sc) => write!(f, "{}", sc),
            Cause::ArityChanged { before, after } => write!(
                f,
                "the two sides are stated at different types ({:?} -> {:?})",
                before, after
            ),
            Cause::TooShallow { entry, needs } => write!(
                f,
                "the replacement needs {} value(s) and the term it lands in is \
                 stated at {}",
                needs, entry
            ),
        }
    }
}

/// The two sides of a step's equation, source first, as spines.
///
/// Source is what must be found in the term, destination what replaces it —
/// which way round that puts the equation is exactly what [`Direction`] says.
/// An [`StepKind::Unfold`] builds its sides from the library here, so no copy
/// of a sentence's body ever has to travel inside a script.
fn sides(prog: &Program, step: &Step) -> Result<(Term, Term), SideCondition> {
    let (lhs, rhs) = match &step.kind {
        StepKind::Rule(rule) => {
            rule.check(prog)?;
            (rule.lhs(), rule.rhs())
        }
        StepKind::Unfold { target } => (Term::Call(*target), expand_call(prog, *target)),
    };
    Ok(match step.dir {
        Direction::Forward => (lhs, rhs),
        Direction::Reverse => (rhs, lhs),
    })
}

/// The same, as the spines a window is matched and spliced against.
///
/// **Bare**, where the sides themselves are typed. An equation is stated at one
/// arity — `counit` is `pick d ; drop = id (d+1)`, not `= id 0` — and that is
/// what `--check` compares; but the term it lands in is padded to *its* type, so
/// what gets spliced is the equation with its own padding taken back off.
fn bare_sides(prog: &Program, step: &Step) -> Result<(Vec<Term>, Vec<Term>), SideCondition> {
    let (src, dst) = sides(prog, step)?;
    Ok((unpad(&src).into_spine(), unpad(&dst).into_spine()))
}

/// The `i`th factor of a term's spine.
fn nth_mut(term: &mut Term, i: usize) -> Option<&mut Term> {
    match term {
        Term::Compose(a, b) => {
            let left = a.width();
            if i < left {
                nth_mut(a, i)
            } else {
                nth_mut(b, i - left)
            }
        }
        Term::Id(0) => None,
        other => (i == 0).then_some(other),
    }
}

/// The spine a step splices into.
///
/// Two cases because the root of a run *is* a spine — the engine scans one and
/// hands it here — while everything below the root is a sub-term that has to be
/// taken apart and put back together around the splice.
enum Target<'t> {
    Root(&'t mut Vec<Term>),
    Sub(&'t mut Term),
}

impl Target<'_> {
    fn factors(&self) -> Vec<&Term> {
        match self {
            Target::Root(v) => v.iter().collect(),
            Target::Sub(t) => t.spine(),
        }
    }

    /// Puts a whole rebuilt spine back.
    fn replace(&mut self, factors: Vec<Term>) {
        match self {
            Target::Root(v) => **v = factors,
            Target::Sub(t) => **t = Term::seq(factors),
        }
    }
}

/// Walks a descent to the spine it names.
fn locate<'t>(
    root: &'t mut Vec<Term>,
    descent: &[(usize, Selector)],
) -> Result<Target<'t>, Cause> {
    let Some(((index, sel), rest)) = descent.split_first() else {
        return Ok(Target::Root(root));
    };
    let len = root.len();
    let Some(node) = root.get_mut(*index) else {
        return Err(Cause::PathIndex {
            depth: 0,
            index: *index,
            len,
        });
    };
    let found = sketch_head(node);
    let Some(mut cur) = child_seq(node, *sel) else {
        return Err(Cause::PathKind {
            depth: 0,
            selector: *sel,
            found,
        });
    };
    for (leg, (index, sel)) in rest.iter().enumerate() {
        let depth = leg + 1;
        let len = cur.width();
        let Some(node) = nth_mut(cur, *index) else {
            return Err(Cause::PathIndex {
                depth,
                index: *index,
                len,
            });
        };
        let found = sketch_head(node);
        match child_seq(node, *sel) {
            Some(body) => cur = body,
            None => {
                return Err(Cause::PathKind {
                    depth,
                    selector: *sel,
                    found,
                });
            }
        }
    }
    Ok(Target::Sub(cur))
}

/// The spine a splice leaves behind, and how many factors it inserted.
///
/// **This is where the padding invariant is maintained.** A window is replaced
/// at the *bare* type both sides of the equation are stated at, and the whole
/// spine is then re-stated at the type it had — so a rewrite cannot quietly
/// widen or narrow the term it sits in, and every composition still lines up
/// afterwards. `None` when the replacement demands a deeper stack than the
/// spine is stated at, which is the one thing padding cannot fix.
fn respliced(
    prog: &Program,
    factors: &[&Term],
    range: std::ops::Range<usize>,
    dst: Vec<Term>,
) -> Option<(Vec<Term>, usize)> {
    // What the spine is stated at: what its first factor takes. A spine that is
    // nothing but an identity is the empty program at that type, and unpadding
    // it leaves no factors — which is why the window into one can only ever be
    // the empty one, at 0.
    let entry = match factors.first() {
        Some(first) => term_arity(prog, first)?.0,
        None => 0,
    };
    // A term the tool built is padded; one a test wrote by hand may not be.
    // The invariant is *maintained* rather than imposed: a spine that did not
    // line up going in does not line up coming out, and nothing here quietly
    // restates a caller's term at a type it did not choose.
    let was_aligned = aligned(prog, &Term::seq(cloned(factors)));
    let mut bare = Term::seq(factors.iter().map(|f| unpad(f))).into_spine();
    let inserted: Vec<Term> = Term::seq(dst).into_spine();
    let count = inserted.len();
    if range.end > bare.len() {
        return None;
    }
    bare.splice(range, inserted);
    let whole = Term::seq(bare);
    if !was_aligned {
        return Some((whole.into_spine(), count));
    }
    Some((pad(prog, &whole, entry)?.into_spine(), count))
}

/// Applies one step to a spine, or explains why it does not fit.
///
/// `idx` is the step's place in its script and appears in any error; a step
/// applied on its own can pass 0.
pub(crate) fn apply_step(
    prog: &Program,
    tree: &mut Vec<Term>,
    step: &Step,
    idx: usize,
    check: bool,
) -> Result<SpliceInfo, ApplyError> {
    let fail = |cause: Cause| ApplyError {
        step: idx,
        rule: step.kind.name(),
        dir: step.dir,
        loc: step.loc.clone(),
        cause,
    };

    let (src, dst) = bare_sides(prog, step).map_err(|sc| fail(Cause::SideCondition(sc)))?;

    if check {
        // **The two sides must be stated at the same type.** That is stricter
        // than the net-change comparison it replaces: net is preserved by a
        // misreported arity as readily as by a correct one, and it said nothing
        // about a rewrite that quietly demanded a deeper stack. Since every
        // equation is padded to a common arity, equality here is exactly the
        // claim that the two sides are the same morphism.
        //
        // Learning an arity that was previously unknown stays permissible.
        // Under the global precondition it should not arise — every term has an
        // arity once panics are excluded — but tolerating it costs nothing and
        // keeps the applier usable on synthetic terms.
        let (typed_src, typed_dst) =
            sides(prog, step).map_err(|sc| fail(Cause::SideCondition(sc)))?;
        let (before, after) = (
            term_arity(prog, &typed_src),
            term_arity(prog, &typed_dst),
        );
        let broke = match (before, after) {
            (Some(a), Some(b)) => a != b,
            (Some(_), None) => true,
            (None, _) => false,
        };
        if broke {
            return Err(fail(Cause::ArityChanged { before, after }));
        }
    }

    let mut target = locate(tree, &step.loc.descent).map_err(fail)?;

    let at = step.loc.at;
    let end = at + src.len();
    let factors = target.factors();
    if end > factors.len() {
        let len = factors.len();
        return Err(fail(Cause::WindowRange {
            at,
            need: src.len(),
            len,
        }));
    }
    let window = &factors[at..end];
    if !same_effect_refs(window, &src) {
        let found = sketch(&cloned(window));
        return Err(fail(Cause::WindowMismatch {
            expected: sketch(&src),
            found,
        }));
    }

    // The splice is on the spine, and the term is rebuilt from it: a rewrite
    // does not have to respect the nesting it found, because the nesting was
    // never part of what the term means.
    let entry = factors
        .first()
        .and_then(|f| term_arity(prog, f))
        .map(|(n, _)| n)
        .unwrap_or(0);
    let Some((rebuilt, inserted)) = respliced(prog, &factors, at..end, dst) else {
        let needs = seq_arity(prog, &cloned(&factors)).0;
        return Err(fail(Cause::TooShallow { entry, needs }));
    };
    drop(factors);
    let info = SpliceInfo {
        removed: src.len(),
        inserted,
    };
    target.replace(rebuilt);
    Ok(info)
}

/// What a step would replace, and with what — sketched, for a listing.
///
/// The same two sides [`apply_step`] works from, so what this shows is what
/// would actually happen rather than a second account of it. `None` when the
/// arguments do not satisfy the equation, which for a recorded step means
/// something has changed underneath it.
pub(crate) fn preview(prog: &Program, step: &Step) -> Option<(String, String)> {
    let (src, dst) = bare_sides(prog, step).ok()?;
    Some((sketch(&src), sketch(&dst)))
}

/// Applies a whole script, in order.
///
/// Over a spine rather than a term, because that is what a script addresses:
/// putting the composition back together between steps would be work no step
/// can see.
pub(crate) fn apply_script_seq(
    prog: &Program,
    tree: &mut Vec<Term>,
    script: &[Step],
    check: bool,
) -> Result<(), ApplyError> {
    for (idx, step) in script.iter().enumerate() {
        apply_step(prog, tree, step, idx, check)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::Rule;
    use bytecode::{Instruction, Library, Value, assemble};

    fn prog() -> Program<'static> {
        Program::new(Box::leak(Box::new(Library::new())))
    }

    fn op(i: Instruction) -> Term {
        Term::Op(i)
    }

    /// `par { body } { id k }`, which is what a `dip k` is.
    fn frame(k: usize, body: Vec<Term>) -> Term {
        Term::frame(Vec::new(), k, Term::seq(body))
    }

    fn arms(then_body: Vec<Term>, else_body: Vec<Term>) -> Term {
        Term::Branch {
            then_origin: "then".to_string(),
            then_body: Box::new(Term::seq(then_body)),
            else_origin: "else".to_string(),
            else_body: Box::new(Term::seq(else_body)),
        }
    }

    fn step(kind: Rule, dir: Direction, loc: Location) -> Step {
        Step {
            kind: StepKind::Rule(kind),
            dir,
            loc,
        }
    }

    fn collapse(k: usize, j: usize, a: Vec<Term>) -> Rule {
        Rule::Collapse {
            k,
            j,
            a: Term::seq(a),
            outer: Vec::new(),
            inner: Vec::new(),
        }
    }

    // -- the happy path -----------------------------------------------------

    #[test]
    fn a_step_rewrites_exactly_its_window() {
        let mut tree = vec![
            op(Instruction::Add),
            frame(2, vec![frame(3, vec![op(Instruction::Drop)])]),
            op(Instruction::Not),
        ];
        let s = step(
            collapse(2, 3, vec![op(Instruction::Drop)]),
            Direction::Forward,
            Location::root(1),
        );
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 1,
                inserted: 1
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Add),
                frame(5, vec![op(Instruction::Drop)]),
                op(Instruction::Not),
            ]
        );
    }

    #[test]
    fn a_descent_reaches_inside_a_branch_arm() {
        let mut tree = vec![arms(
            vec![op(Instruction::Not), frame(1, vec![frame(1, Vec::new())])],
            Vec::new(),
        )];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Then)],
                at: 1,
            },
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            tree,
            vec![arms(
                vec![op(Instruction::Not), frame(2, Vec::new())],
                Vec::new()
            )]
        );
    }

    #[test]
    fn a_descent_reaches_the_left_of_a_par() {
        // A frame's body is the left-hand side, which is where a rewrite under
        // a hidden window happens.
        let mut tree = vec![frame(1, vec![frame(1, vec![frame(1, Vec::new())])])];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Left)],
                at: 0,
            },
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![frame(1, vec![frame(2, Vec::new())])]);
    }

    #[test]
    fn a_window_may_be_wider_than_one_factor_and_shrink() {
        // `counit` takes two factors and leaves none.
        let mut tree = vec![
            op(Instruction::Not),
            op(Instruction::Copy),
            op(Instruction::Drop),
            op(Instruction::Add),
        ];
        let s = step(Rule::Counit { d: 0 }, Direction::Forward, Location::root(1));
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 2,
                inserted: 0
            }
        );
        assert_eq!(tree, vec![op(Instruction::Not), op(Instruction::Add)]);
    }

    // -- direction ----------------------------------------------------------

    #[test]
    fn reverse_finds_the_right_hand_side_and_leaves_the_left() {
        let mut tree = vec![frame(5, vec![op(Instruction::Drop)])];
        let s = step(
            collapse(2, 3, vec![op(Instruction::Drop)]),
            Direction::Reverse,
            Location::root(0),
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![frame(2, vec![frame(3, vec![op(Instruction::Drop)])])]);
    }

    #[test]
    fn forward_then_reverse_is_the_identity_for_every_equation() {
        // The strongest single statement about the lower layer: a step and its
        // opposite leave the term exactly as they found it — origins included,
        // which is why the equations carry provenance in their arguments.
        let prog = prog();
        for rule in equations() {
            let mut tree = rule.lhs().into_spine();
            let before = tree.clone();
            let fwd = step(rule.clone(), Direction::Forward, Location::root(0));
            apply_step(&prog, &mut tree, &fwd, 0, true)
                .unwrap_or_else(|e| panic!("{} forward: {}", rule.name(), e));
            assert_ne!(tree, before, "{} changed nothing", rule.name());

            let back = step(rule.clone(), Direction::Reverse, Location::root(0));
            apply_step(&prog, &mut tree, &back, 1, true)
                .unwrap_or_else(|e| panic!("{} reverse: {}", rule.name(), e));
            assert_eq!(tree, before, "{} does not round-trip", rule.name());
        }
    }

    fn equations() -> Vec<Rule> {
        vec![
            collapse(2, 3, vec![op(Instruction::Add)]),
            Rule::ElimPar0 {
                a: op(Instruction::Add),
                origins: vec!["o".to_string()],
            },
            Rule::Interchange {
                x: op(Instruction::Add),
                framed: frame(2, vec![op(Instruction::Drop)]),
                n: 2,
                m: 2,
            },
            Rule::Fuse {
                k: 1,
                a: op(Instruction::Add),
                b: op(Instruction::Drop),
                a_origins: vec!["a".to_string()],
                b_origins: vec!["b".to_string()],
            },
            Rule::Hoist {
                k: 1,
                x: op(Instruction::Add),
                origins: Vec::new(),
                then_arm: op(Instruction::Drop),
                else_arm: op(Instruction::Not),
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::Distribute {
                then_arm: op(Instruction::Add),
                else_arm: op(Instruction::Add),
                suffix: op(Instruction::Drop),
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::FoldBranch {
                c: Value::Bool(true),
                then_arm: op(Instruction::Add),
                else_arm: op(Instruction::Add),
                then_origin: "then".to_string(),
                else_origin: "else".to_string(),
            },
            Rule::Eval {
                op: Instruction::And,
                inputs: vec![Value::Bool(true), Value::Bool(false)],
            },
            Rule::Annihilate {
                x: op(Instruction::Add),
                n: 2,
                m: 2,
            },
            Rule::Counit { d: 3 },
            Rule::CopyConst { c: Value::Int(7) },
            Rule::CopyAssoc,
            Rule::CancelTuple { n: 3 },
        ]
    }

    // -- every way a step can fail ------------------------------------------

    #[test]
    fn a_descent_past_the_end_is_refused() {
        let mut tree = vec![op(Instruction::Add)];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(4, Selector::Left)],
                at: 0,
            },
        );
        assert!(matches!(
            apply_step(&prog(), &mut tree, &s, 3, false)
                .unwrap_err()
                .cause,
            Cause::PathIndex {
                depth: 0,
                index: 4,
                len: 1
            }
        ));
    }

    #[test]
    fn a_descent_into_a_part_the_factor_does_not_have_is_refused() {
        // A `par` has a left and a right, not a then arm.
        let mut tree = vec![frame(1, vec![op(Instruction::Add)])];
        let s = step(
            collapse(1, 1, Vec::new()),
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Then)],
                at: 0,
            },
        );
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        assert!(matches!(
            err.cause,
            Cause::PathKind {
                selector: Selector::Then,
                ..
            }
        ));
        assert!(err.to_string().contains("no such part"));
    }

    #[test]
    fn a_window_running_off_the_end_is_refused() {
        let mut tree = vec![op(Instruction::Copy)];
        let s = step(Rule::Counit { d: 0 }, Direction::Forward, Location::root(0));
        assert!(matches!(
            apply_step(&prog(), &mut tree, &s, 0, false)
                .unwrap_err()
                .cause,
            Cause::WindowRange {
                at: 0,
                need: 2,
                len: 1
            }
        ));
    }

    #[test]
    fn a_window_that_is_not_what_the_equation_says_is_refused() {
        let mut tree = vec![op(Instruction::Copy), op(Instruction::Add)];
        let s = step(Rule::Counit { d: 0 }, Direction::Forward, Location::root(0));
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        let Cause::WindowMismatch { expected, found } = &err.cause else {
            panic!("expected a mismatch, got {:?}", err.cause)
        };
        assert!(expected.contains("drop"), "{}", expected);
        assert!(found.contains("add"), "{}", found);
    }

    #[test]
    fn a_fabricated_arity_is_refused_even_though_the_window_fits() {
        // The window really does read `add ; par { } { id }`. What the step
        // claims about `add` is what the library disagrees with, and that is
        // enough.
        let before = vec![op(Instruction::Add), frame(1, Vec::new())];
        let mut tree = before.clone();
        let s = step(
            Rule::Interchange {
                x: op(Instruction::Add),
                framed: frame(1, Vec::new()),
                n: 1,
                m: 1,
            },
            Direction::Forward,
            Location::root(0),
        );
        let err = apply_step(&prog(), &mut tree, &s, 0, false).unwrap_err();
        assert!(matches!(
            err.cause,
            Cause::SideCondition(SideCondition::ClaimedArityMismatch { .. })
        ));
        // And the term is untouched.
        assert_eq!(tree, before);
    }

    #[test]
    fn a_failed_step_leaves_the_term_alone() {
        let before = vec![op(Instruction::Copy), op(Instruction::Add)];
        let mut tree = before.clone();
        let s = step(Rule::Counit { d: 0 }, Direction::Forward, Location::root(0));
        assert!(apply_step(&prog(), &mut tree, &s, 0, false).is_err());
        assert_eq!(tree, before);
    }

    #[test]
    fn an_equation_with_an_empty_side_is_placed_by_its_location_alone() {
        // `counit` backwards introduces a copy-and-discard where there was
        // nothing. An empty source window matches at every offset, so the
        // location is the *only* thing deciding where the work lands — which
        // is precisely what a script is for, and why introducing rules need
        // addressing to be exact.
        let mut tree = vec![op(Instruction::Not), op(Instruction::Add)];
        let s = step(Rule::Counit { d: 0 }, Direction::Reverse, Location::root(1));
        let info = apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 0,
                inserted: 2
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Not),
                op(Instruction::Copy),
                op(Instruction::Drop),
                op(Instruction::Add),
            ]
        );
    }

    #[test]
    fn a_window_is_found_however_the_composition_was_parenthesized() {
        // The point of reading a term as its spine: `swap ; (swap ; add)` and
        // `(swap ; swap) ; add` are one program, and an equation about the two
        // swaps has to fire in both. Here the nesting is inside a `par`'s left,
        // which is a term rather than a spine, so the applier has to take it
        // apart to find the window.
        let nested = Term::Compose(
            Box::new(op(Instruction::Swap)),
            Box::new(Term::Compose(
                Box::new(op(Instruction::Swap)),
                Box::new(op(Instruction::Add)),
            )),
        );
        let mut tree = vec![Term::frame(Vec::new(), 1, nested)];
        let s = step(
            Rule::SwapCycle,
            Direction::Forward,
            Location {
                descent: vec![(0, Selector::Left)],
                at: 0,
            },
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![frame(1, vec![op(Instruction::Add)])]);
    }

    #[test]
    fn vacuous_is_derivable_from_annihilate_and_counit() {
        // Is `vacuous` an axiom, or a lemma? Run the derivation and find out.
        //
        //   id 0
        //     counit(n-1) backwards, n times, each inside the last  -> pick^n drop^n
        //     annihilate backwards on the drops                     -> pick^n X drop^m
        //
        // If this reproduces `vacuous`'s left-hand side exactly then the
        // equation is a consequence of two others and does not earn a place
        // among the axioms.
        for (x, n, m) in [
            (op(Instruction::Add), 2usize, 2usize),
            (op(Instruction::Untuple(2)), 1, 3),
            (op(Instruction::Not), 1, 1),
        ] {
            // A `pick (n-1)` is one factor at depth 0 and two under frames, so
            // the `i`th pair goes in past what the `i` before it wrote.
            let wide = crate::rule::pick(n - 1).width();
            let mut script: Vec<Step> = (0..n)
                .map(|i| {
                    step(
                        Rule::Counit { d: n - 1 },
                        Direction::Reverse,
                        Location::root(i * wide),
                    )
                })
                .collect();
            script.push(step(
                Rule::Annihilate {
                    x: x.clone(),
                    n,
                    m,
                },
                Direction::Reverse,
                Location::root(n * wide),
            ));

            let mut tree: Vec<Term> = Vec::new();
            apply_script_seq(&prog(), &mut tree, &script, true)
                .unwrap_or_else(|e| panic!("deriving vacuous for {:?}: {}", x, e));

            let expected = Term::seq([
                crate::rule::tests::copies(n),
                x.clone(),
                Term::seq(std::iter::repeat_n(op(Instruction::Drop), m)),
            ])
            .into_spine();
            assert_eq!(
                tree, expected,
                "the derivation did not reproduce vacuous for {:?}",
                x
            );

            // And forwards, deleting the whole thing again: the derivation is
            // reversible step for step, which is what makes it a lemma rather
            // than a one-way trick.
            let back: Vec<Step> = script
                .iter()
                .rev()
                .map(|s| Step {
                    dir: s.dir.flipped(),
                    ..s.clone()
                })
                .collect();
            apply_script_seq(&prog(), &mut tree, &back, true)
                .unwrap_or_else(|e| panic!("undoing vacuous for {:?}: {}", x, e));
            assert!(tree.is_empty(), "vacuous did not undo for {:?}", x);
        }
    }

    #[test]
    fn copy_const_is_derivable_from_copy_nat() {
        // Is `copy_const` an axiom, or a lemma? Run the derivation and find out.
        //
        //   push c ; copy
        //     copy_nat backwards, at n = 0   -> push c ; par { push c } { id }
        //     interchange forwards           -> par { push c } { id 0 } ; push c
        //     elim_par0 forwards             -> push c ; push c
        //
        // Copying a constant is the constant case of copying being natural, so
        // the general law demotes this one. It stays a matcher — `values` and
        // `cleanup` lean on it, and one step beats three — but it is no longer
        // something the set has to take on faith.
        let c = Value::Int(7);
        let push_c = || op(Instruction::Push(c.clone()));
        let rule = Rule::CopyConst { c: c.clone() };

        let script = vec![
            step(
                Rule::CopyNat {
                    x: push_c(),
                    n: 0,
                    m: 1,
                },
                Direction::Reverse,
                Location::root(0),
            ),
            step(
                Rule::Interchange {
                    x: push_c(),
                    framed: frame(1, vec![push_c()]),
                    n: 0,
                    m: 1,
                },
                Direction::Forward,
                Location::root(0),
            ),
            step(
                Rule::ElimPar0 {
                    a: push_c(),
                    origins: Vec::new(),
                },
                Direction::Forward,
                Location::root(0),
            ),
        ];

        let mut tree = rule.lhs().into_spine();
        apply_script_seq(&prog(), &mut tree, &script, true)
            .unwrap_or_else(|e| panic!("deriving copy_const: {}", e));
        assert_eq!(
            tree,
            rule.rhs().into_spine(),
            "the derivation did not reproduce copy_const"
        );

        // And back, step for step, which is what makes it a lemma rather than
        // a coincidence that happens to land on the same term.
        let back: Vec<Step> = script
            .iter()
            .rev()
            .map(|s| Step {
                dir: s.dir.flipped(),
                ..s.clone()
            })
            .collect();
        apply_script_seq(&prog(), &mut tree, &back, true)
            .unwrap_or_else(|e| panic!("undoing the derivation: {}", e));
        assert_eq!(tree, rule.lhs().into_spine());
    }

    #[test]
    fn copy_const_at_depth_is_derivable_from_the_movement_laws() {
        // The question the movement laws exist to answer: does a literal held
        // *below* the top of the stack still read as a literal? `copy_const` is
        // stated at the top, and the slot below is read with `pick 1`, which
        // phase 4 writes as `par { copy } { id } ; swap`. Run the derivation and
        // find out.
        //
        //   par { push c } { id } ; par { copy } { id } ; swap
        //     fuse forwards           -> par { push c ; copy } { id } ; swap
        //     copy_const, on the left -> par { push c ; push c } { id } ; swap
        //     fuse backwards          -> par { push c } { id } ; par { push c } { id } ; swap
        //     unframe forwards        -> par { push c } { id } ; push c
        let c = Value::Int(7);
        let push_c = || op(Instruction::Push(c.clone()));

        let script = vec![
            step(
                Rule::Fuse {
                    k: 1,
                    a: push_c(),
                    b: op(Instruction::Copy),
                    a_origins: Vec::new(),
                    b_origins: Vec::new(),
                },
                Direction::Forward,
                Location::root(0),
            ),
            step(
                Rule::CopyConst { c: c.clone() },
                Direction::Forward,
                Location {
                    descent: vec![(0, Selector::Left)],
                    at: 0,
                },
            ),
            step(
                Rule::Fuse {
                    k: 1,
                    a: push_c(),
                    b: push_c(),
                    a_origins: Vec::new(),
                    b_origins: Vec::new(),
                },
                Direction::Reverse,
                Location::root(0),
            ),
            step(
                Rule::Unframe {
                    framed: frame(1, vec![push_c()]),
                    n: 0,
                    m: 1,
                },
                Direction::Forward,
                Location::root(1),
            ),
        ];

        // `pick 1`, as phase 4 writes it.
        let start = || {
            vec![
                frame(1, vec![push_c()]),
                frame(1, vec![op(Instruction::Copy)]),
                op(Instruction::Swap),
            ]
        };

        let mut tree = start();
        apply_script_seq(&prog(), &mut tree, &script, true)
            .unwrap_or_else(|e| panic!("deriving copy_const at depth: {}", e));
        assert_eq!(
            tree,
            vec![frame(1, vec![push_c()]), push_c()],
            "the derivation did not read the deep slot as the literal it holds"
        );

        // And back, so it is a lemma rather than a term that happens to match.
        let back: Vec<Step> = script
            .iter()
            .rev()
            .map(|s| Step {
                dir: s.dir.flipped(),
                ..s.clone()
            })
            .collect();
        apply_script_seq(&prog(), &mut tree, &back, true)
            .unwrap_or_else(|e| panic!("undoing the derivation: {}", e));
        assert_eq!(tree, start());
    }

    // -- provenance is not identity -----------------------------------------

    #[test]
    fn a_window_matches_by_effect_not_by_where_its_code_came_from() {
        // Phase 4 gives every inline block a fresh label, so two identical
        // blocks never share provenance. A step written against one has to fit
        // the other.
        let mut tree = vec![Term::frame(
            vec!["#12 somewhere".to_string()],
            0,
            op(Instruction::Add),
        )];
        let s = step(
            Rule::ElimPar0 {
                a: op(Instruction::Add),
                origins: Vec::new(),
            },
            Direction::Forward,
            Location::root(0),
        );
        apply_step(&prog(), &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![op(Instruction::Add)]);
    }

    // -- unfold -------------------------------------------------------------

    fn library() -> &'static Library {
        Box::leak(Box::new(
            assemble(
                r#"
                sentence pushy { push 7 }
                sentence pair { push 1 push 2 }
                "#,
            )
            .unwrap(),
        ))
    }

    fn named(library: &Library, name: &str) -> bytecode::SentenceIndex {
        library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(i, _)| i)
            .unwrap_or_else(|| panic!("no sentence '{}'", name))
    }

    #[test]
    fn unfold_takes_its_body_from_the_library_not_from_the_script() {
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");

        let mut tree = vec![Term::Call(pushy)];
        let s = Step {
            kind: StepKind::Unfold { target: pushy },
            dir: Direction::Forward,
            loc: Location::root(0),
        };
        apply_step(&prog, &mut tree, &s, 0, true).unwrap();
        assert_eq!(tree, vec![op(Instruction::Push(Value::Int(7)))]);

        // And backwards: recognizing the body and folding it into the call.
        let back = Step {
            dir: Direction::Reverse,
            ..s
        };
        apply_step(&prog, &mut tree, &back, 1, true).unwrap();
        assert_eq!(tree, vec![Term::Call(pushy)]);
    }

    #[test]
    fn unfold_produces_a_body_the_step_never_carried() {
        // One call becomes two factors. The step names only the target, so
        // those can have come from nowhere but the library — which is the whole
        // reason unfolding is not a [`Rule`].
        let library = library();
        let prog = Program::new(library);
        let pair = named(library, "pair");
        let mut tree = vec![Term::Call(pair)];
        let info = apply_step(
            &prog,
            &mut tree,
            &Step {
                kind: StepKind::Unfold { target: pair },
                dir: Direction::Forward,
                loc: Location::root(0),
            },
            0,
            true,
        )
        .unwrap();
        assert_eq!(
            info,
            SpliceInfo {
                removed: 1,
                inserted: 2
            }
        );
        assert_eq!(
            tree,
            vec![
                op(Instruction::Push(Value::Int(1))),
                op(Instruction::Push(Value::Int(2))),
            ]
        );
    }

    #[test]
    fn unfolding_a_framed_call_leaves_the_frame_where_it_was() {
        // A call that hides values is `par { jump S } { id k }`, so the step
        // reaches the call through the `par`'s left and the frame is untouched
        // by the rewrite.
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");
        let mut tree = vec![Term::frame(Vec::new(), 2, Term::Call(pushy))];
        apply_step(
            &prog,
            &mut tree,
            &Step {
                kind: StepKind::Unfold { target: pushy },
                dir: Direction::Forward,
                loc: Location {
                    descent: vec![(0, Selector::Left)],
                    at: 0,
                },
            },
            0,
            true,
        )
        .unwrap();
        assert_eq!(
            tree,
            vec![Term::frame(
                Vec::new(),
                2,
                op(Instruction::Push(Value::Int(7)))
            )]
        );
    }

    #[test]
    fn folding_a_body_that_is_not_the_target_is_refused() {
        let library = library();
        let prog = Program::new(library);
        let pushy = named(library, "pushy");
        let mut tree = vec![op(Instruction::Drop)];
        let s = Step {
            kind: StepKind::Unfold { target: pushy },
            dir: Direction::Reverse,
            loc: Location::root(0),
        };
        assert!(matches!(
            apply_step(&prog, &mut tree, &s, 0, false)
                .unwrap_err()
                .cause,
            Cause::WindowMismatch { .. }
        ));
    }

    // -- scripts ------------------------------------------------------------

    #[test]
    fn a_script_runs_its_steps_in_order() {
        // Two collapses, the second only possible because the first ran.
        let mut tree = vec![frame(1, vec![frame(1, vec![frame(1, Vec::new())])])];
        let script = vec![
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location {
                    descent: vec![(0, Selector::Left)],
                    at: 0,
                },
            ),
            step(
                collapse(1, 2, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
        ];
        apply_script_seq(&prog(), &mut tree, &script, true).unwrap();
        assert_eq!(tree, vec![frame(3, Vec::new())]);
    }

    #[test]
    fn a_script_reports_which_step_stopped_fitting() {
        let mut tree = vec![frame(1, vec![frame(1, Vec::new())])];
        let script = vec![
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
            // Now `par { } { id 2 }`, so this one cannot fire.
            step(
                collapse(1, 1, Vec::new()),
                Direction::Forward,
                Location::root(0),
            ),
        ];
        let err = apply_script_seq(&prog(), &mut tree, &script, true).unwrap_err();
        assert_eq!(err.step, 1);
        assert!(matches!(err.cause, Cause::WindowMismatch { .. }));
    }

    #[test]
    fn the_factoring_derivation_runs_as_a_script_of_three_laws() {
        // What `factor_branch` used to do in one motion: hoist the shared
        // prefix `add` out of both arms. Wrap it in a frame in each arm, then
        // read the hoist law backwards.
        let mut tree = vec![arms(
            vec![op(Instruction::Add), op(Instruction::Drop)],
            vec![op(Instruction::Add), op(Instruction::Not)],
        )];
        let wrap = |sel| {
            step(
                Rule::ElimPar0 {
                    a: op(Instruction::Add),
                    origins: Vec::new(),
                },
                Direction::Reverse,
                Location {
                    descent: vec![(0, sel)],
                    at: 0,
                },
            )
        };
        let script = vec![
            wrap(Selector::Then),
            wrap(Selector::Else),
            step(
                Rule::Hoist {
                    k: 0,
                    x: op(Instruction::Add),
                    origins: Vec::new(),
                    then_arm: op(Instruction::Drop),
                    else_arm: op(Instruction::Not),
                    then_origin: "then".to_string(),
                    else_origin: "else".to_string(),
                },
                Direction::Reverse,
                Location::root(0),
            ),
        ];
        apply_script_seq(&prog(), &mut tree, &script, true).unwrap();
        assert_eq!(
            tree,
            vec![
                frame(1, vec![op(Instruction::Add)]),
                arms(vec![op(Instruction::Drop)], vec![op(Instruction::Not)]),
            ]
        );
    }
}
