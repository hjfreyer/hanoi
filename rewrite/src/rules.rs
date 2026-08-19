//! The equations, as e-graph rewrites.
//!
//! Every rule here is an equation between programs; saturation applies them
//! all, in both directions where both are bounded, and equality is discovered
//! rather than steered. Three kinds of rule appear, in increasing order of
//! machinery:
//!
//! - **Pattern rules** say both sides syntactically (`rewrite!`), and are used
//!   wherever a law mentions no width and needs no fact — associativity, the
//!   branch laws.
//! - **Fact rules** match a small pattern and read the [`Facts`] of what they
//!   bound — "is this class an identity", "does this class push literals" —
//!   because a width or a side condition cannot be said in a pattern.
//! - **The evaluation rule** consults the interpreter itself: a literal window
//!   is run on a scratch [`vm::VM`], so folding cannot disagree with the
//!   machine. What `eval` owes is an obligation, not a licence.
//!
//! Deliberately absent: unfolding a [`Call`](crate::term::Term::Call) — that
//! is a goal-level decision (see [`crate::strategy`]) — and any rule that
//! conjures code from nothing (`drop(n) = X ; drop(m)` backwards); a stepping
//! stone seeded into the e-graph is how that direction is reached.

use bytecode::{Instruction, Value};
use egg::{Applier, Id, Pattern, PatternAst, Rewrite, Subst, Symbol, Var, rewrite};

use crate::diagram::run_window;
use crate::lang::{
    AsTupleW, CopyW, DropW, Facts, HanaLang, IdW, ProofGraph, Proving, PushW, TupleW, UntupleW,
};

/// A rewrite over the proving e-graph.
pub type ProofRewrite = Rewrite<HanaLang, Proving>;

/// The whole rule set.
pub fn rules() -> Vec<ProofRewrite> {
    let mut out: Vec<ProofRewrite> = Vec::new();

    // ---- associativity: both operators, both ways --------------------------
    out.extend(rewrite!("assoc-compose"; "(; (; ?a ?b) ?c)" <=> "(; ?a (; ?b ?c))"));
    out.extend(rewrite!("assoc-par"; "(* (* ?a ?b) ?c)" <=> "(* ?a (* ?b ?c))"));

    // ---- units -------------------------------------------------------------
    // `id ; a` = `a` = `a ; id`, and the width-0 structural leaves are the
    // unit of `*`. Elimination only: introduction is unbounded, and the
    // staircase rules below are the bounded way shapes get re-padded.
    out.push(dyn_rule(
        "unit-compose-left",
        "(; ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| facts(eg, vars[0]).is_id.then_some(vars[1]),
    ));
    out.push(dyn_rule(
        "unit-compose-right",
        "(; ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| facts(eg, vars[1]).is_id.then_some(vars[0]),
    ));
    out.push(dyn_rule(
        "par-unit-deep",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let fa = facts(eg, vars[0]);
            (fa.is_id && fa.arity.inputs == 0).then_some(vars[1])
        },
    ));
    out.push(dyn_rule(
        "par-unit-top",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let fb = facts(eg, vars[1]);
            (fb.is_id && fb.arity.inputs == 0).then_some(vars[0])
        },
    ));
    out.push(dyn_rule(
        "par-id-fuse",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (fa.is_id && fb.is_id)
                .then(|| eg.add(HanaLang::Idn(IdW(fa.arity.inputs + fb.arity.inputs))))
        },
    ));
    out.push(dyn_rule("copy-nothing", "copy@0", [], |eg, _, _| {
        Some(eg.add(HanaLang::Idn(IdW(0))))
    }));
    out.push(dyn_rule("drop-nothing", "drop@0", [], |eg, _, _| {
        Some(eg.add(HanaLang::Idn(IdW(0))))
    }));

    // ---- interchange, as staircases ----------------------------------------
    // `a * b` = `(a * id) ; (id * b)` = `(id * b) ; (a * id)`: the two sides
    // of a par happen in either order once the other side is padded out. This
    // is the middle-four interchange in the bounded shape, and the recognizers
    // reading a staircase back into a par are what let two different paddings
    // of one program meet.
    out.push(dyn_rule(
        "stair-deep-first",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            let bi = eg.add(HanaLang::Idn(IdW(fb.arity.inputs)));
            let ao = eg.add(HanaLang::Idn(IdW(fa.arity.outputs)));
            let first = eg.add(HanaLang::Par([vars[0], bi]));
            let second = eg.add(HanaLang::Par([ao, vars[1]]));
            Some(eg.add(HanaLang::Compose([first, second])))
        },
    ));
    out.push(dyn_rule(
        "stair-top-first",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            let ai = eg.add(HanaLang::Idn(IdW(fa.arity.inputs)));
            let bo = eg.add(HanaLang::Idn(IdW(fb.arity.outputs)));
            let first = eg.add(HanaLang::Par([ai, vars[1]]));
            let second = eg.add(HanaLang::Par([vars[0], bo]));
            Some(eg.add(HanaLang::Compose([first, second])))
        },
    ));
    out.push(dyn_rule(
        "stair-read-deep-first",
        "(; (* ?a ?i) (* ?j ?b))",
        ["?a", "?i", "?j", "?b"],
        |eg, vars, _| {
            let [a, i, j, b] = [vars[0], vars[1], vars[2], vars[3]];
            let (fa, fi, fj, fb) = (facts(eg, a), facts(eg, i), facts(eg, j), facts(eg, b));
            (fi.is_id
                && fj.is_id
                && fi.arity.inputs == fb.arity.inputs
                && fj.arity.inputs == fa.arity.outputs)
                .then(|| eg.add(HanaLang::Par([a, b])))
        },
    ));
    out.push(dyn_rule(
        "stair-read-top-first",
        "(; (* ?i ?b) (* ?a ?j))",
        ["?i", "?b", "?a", "?j"],
        |eg, vars, _| {
            let [i, b, a, j] = [vars[0], vars[1], vars[2], vars[3]];
            let (fi, fb, fa, fj) = (facts(eg, i), facts(eg, b), facts(eg, a), facts(eg, j));
            (fi.is_id
                && fj.is_id
                && fi.arity.inputs == fa.arity.inputs
                && fj.arity.inputs == fb.arity.outputs)
                .then(|| eg.add(HanaLang::Par([a, b])))
        },
    ));
    // The full middle-four interchange, forward: two pars in sequence whose
    // split lines up fuse into one par of composes. The staircases above are
    // its identity cases; this is the general one, and it is what lets a
    // computation and the counit meet across a par boundary.
    out.push(dyn_rule(
        "par-fuse",
        "(; (* ?a ?b) (* ?c ?d))",
        ["?a", "?b", "?c", "?d"],
        |eg, vars, _| {
            let [a, b, c, d] = [vars[0], vars[1], vars[2], vars[3]];
            let (fa, fb, fc, fd) = (facts(eg, a), facts(eg, b), facts(eg, c), facts(eg, d));
            (fa.arity.outputs == fc.arity.inputs && fb.arity.outputs == fd.arity.inputs).then(
                || {
                    let deep = eg.add(HanaLang::Compose([a, c]));
                    let top = eg.add(HanaLang::Compose([b, d]));
                    eg.add(HanaLang::Par([deep, top]))
                },
            )
        },
    ));
    // A frame off a composition: `id * (f ; g)` runs its framed factors one
    // at a time. This is the *splitting* reading of the interchange that
    // `par-fuse` fuses — bounded here because one leg is an identity and
    // the other is literally a composition node, so nothing has to guess a
    // split. It is what lets a branch buried in a framed body surface:
    // `id(1) * (P ; branch { … })` has no other road to `branch-beside`'s
    // window, which is why the contract proof's first cut used to spread
    // the padding by hand.
    out.push(dyn_rule(
        "frame-split-deep",
        "(* ?i (; ?f ?g))",
        ["?i", "?f", "?g"],
        |eg, vars, _| {
            facts(eg, vars[0]).is_id.then(|| {
                let first = eg.add(HanaLang::Par([vars[0], vars[1]]));
                let second = eg.add(HanaLang::Par([vars[0], vars[2]]));
                eg.add(HanaLang::Compose([first, second]))
            })
        },
    ));
    out.push(dyn_rule(
        "frame-split-top",
        "(* (; ?f ?g) ?i)",
        ["?f", "?g", "?i"],
        |eg, vars, _| {
            facts(eg, vars[2]).is_id.then(|| {
                let first = eg.add(HanaLang::Par([vars[0], vars[2]]));
                let second = eg.add(HanaLang::Par([vars[1], vars[2]]));
                eg.add(HanaLang::Compose([first, second]))
            })
        },
    ));
    // A producer beside a computation: `a ; (id(a.out) * b)` is `a * b` when
    // `b` reads nothing — `b`'s pushes land on top of `a`'s untouched answer.
    out.push(dyn_rule(
        "compose-to-par",
        "(; ?a (* ?i ?b))",
        ["?a", "?i", "?b"],
        |eg, vars, _| {
            let [a, i, b] = [vars[0], vars[1], vars[2]];
            let (fa, fi, fb) = (facts(eg, a), facts(eg, i), facts(eg, b));
            (fi.is_id && fi.arity.inputs == fa.arity.outputs && fb.arity.inputs == 0)
                .then(|| eg.add(HanaLang::Par([a, b])))
        },
    ));

    // ---- the symmetry ------------------------------------------------------
    out.push(dyn_rule("swap-cycle", "(; swap swap)", [], |eg, _, _| {
        Some(eg.add(HanaLang::Idn(IdW(2))))
    }));
    out.push(dyn_rule(
        "swap-nat",
        "(; (* ?a ?b) swap)",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (one_to_one(&fa) && one_to_one(&fb)).then(|| {
                let swap = eg.add(HanaLang::Swap);
                let flipped = eg.add(HanaLang::Par([vars[1], vars[0]]));
                eg.add(HanaLang::Compose([swap, flipped]))
            })
        },
    ));
    out.push(dyn_rule(
        "swap-nat-rev",
        "(; swap (* ?b ?a))",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (one_to_one(&fa) && one_to_one(&fb)).then(|| {
                let swap = eg.add(HanaLang::Swap);
                let flipped = eg.add(HanaLang::Par([vars[0], vars[1]]));
                eg.add(HanaLang::Compose([flipped, swap]))
            })
        },
    ));

    // ---- the comonoid ------------------------------------------------------
    // Copy a block and discard one of the two: either one, and nothing
    // happened. `counit-copy` takes the copy (on top), `counit-original`
    // takes the original out from underneath it.
    out.push(dyn_rule(
        "counit-copy",
        "(; ?c (* ?i ?d))",
        ["?c", "?i", "?d"],
        |eg, vars, _| counit(eg, vars[0], vars[1], vars[2]),
    ));
    out.push(dyn_rule(
        "counit-original",
        "(; ?c (* ?d ?i))",
        ["?c", "?d", "?i"],
        |eg, vars, _| counit(eg, vars[0], vars[2], vars[1]),
    ));
    out.push(dyn_rule(
        "cocommutative",
        "(; ?c swap)",
        ["?c"],
        |eg, vars, _| {
            let fc = facts(eg, vars[0]);
            (fc.is_copy && fc.arity.inputs == 1).then_some(vars[0])
        },
    ));
    // A block copy of two is the two `pick 1`s it lowers from. One direction
    // only — recognize the frame spelling and give its class the `copy@2`
    // leaf. That is enough for both ways of meeting: two `copy@2` leaves are
    // one e-node, so a block the naturality rules built and a block the
    // compiler spelled as frames land in one class without ever *expanding*
    // a `copy@2` into frames, which was a growth engine.
    out.push(rewrite!("copy-block-two";
        "(; (* copy@1 id@1) (; (* id@1 swap) (; (* id@1 (* copy@1 id@1)) (* id@2 swap))))"
        => "copy@2"));
    out.extend(rewrite!("coassociative";
        "(; copy@1 (* id@1 copy@1))" <=> "(; copy@1 (* copy@1 id@1))"));

    // ---- the two naturalities ----------------------------------------------
    // Copying is natural: run once and copy the outputs, or copy the inputs
    // and run twice. Both directions are bounded, and backwards — un-sharing
    // a copy into a second run — is the reading proofs reach for.
    out.push(dyn_rule(
        "copy-nat",
        "(; ?x ?c)",
        ["?x", "?c"],
        |eg, vars, _| {
            let (fx, fc) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (fc.is_copy && fc.arity.inputs == fx.arity.outputs && !fx.is_id && !fx.is_copy).then(
                || {
                    let copy_in = eg.add(HanaLang::Copyn(CopyW(fx.arity.inputs)));
                    let both = eg.add(HanaLang::Par([vars[0], vars[0]]));
                    eg.add(HanaLang::Compose([copy_in, both]))
                },
            )
        },
    ));
    out.push(dyn_rule(
        "copy-nat-rev",
        "(; ?c (* ?x ?y))",
        ["?c", "?x", "?y"],
        |eg, vars, _| {
            let fc = facts(eg, vars[0]);
            let fx = facts(eg, vars[1]);
            (fc.is_copy && vars[1] == vars[2] && fc.arity.inputs == fx.arity.inputs).then(|| {
                let copy_out = eg.add(HanaLang::Copyn(CopyW(fx.arity.outputs)));
                eg.add(HanaLang::Compose([vars[1], copy_out]))
            })
        },
    ));
    // Discarding is natural: a computation whose results are all dropped is
    // the dropping of its inputs. One direction — the other conjures work.
    out.push(dyn_rule(
        "drop-nat",
        "(; ?x ?d)",
        ["?x", "?d"],
        |eg, vars, _| {
            let (fx, fd) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (fd.is_drop && !fx.is_id && !fx.is_drop)
                .then(|| eg.add(HanaLang::Dropn(DropW(fx.arity.inputs))))
        },
    ));
    out.push(dyn_rule(
        "drop-par-fuse",
        "(* ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let (fa, fb) = (facts(eg, vars[0]), facts(eg, vars[1]));
            (fa.is_drop && fb.is_drop)
                .then(|| eg.add(HanaLang::Dropn(DropW(fa.arity.inputs + fb.arity.inputs))))
        },
    ));
    out.extend(rewrite!("drop-split-two"; "drop@2" <=> "(* drop@1 drop@1)"));
    // The symmetry slides past a dropping leg: exchange two values and drop
    // one, or drop the other one where it stood. `swap-nat` above wants both
    // legs `1 -> 1`, and a `drop` is the one-legged case it cannot say.
    out.extend(rewrite!("swap-drop-top"; "(; swap (* id@1 drop@1))" <=> "(* drop@1 id@1)"));
    out.extend(rewrite!("swap-drop-deep"; "(; swap (* drop@1 id@1))" <=> "(* id@1 drop@1)"));

    // ---- evaluation --------------------------------------------------------
    // A literal window is run on the machine itself, so the fold and the
    // interpreter cannot disagree; see `run_window`.
    out.push(dyn_rule(
        "eval",
        "(; ?l ?op)",
        ["?l", "?op"],
        |eg, vars, _| fold_window(eg, vars[0], vars[1]),
    ));
    // The same fold when the operation sits over a frame: the identity part
    // passes literals (or anything else) through untouched, and the operation
    // still reads the top of the pushed run.
    out.push(dyn_rule(
        "eval-padded",
        "(; ?l (* ?i ?op))",
        ["?l", "?i", "?op"],
        |eg, vars, _| {
            facts(eg, vars[1]).is_id.then_some(())?;
            fold_window(eg, vars[0], vars[2])
        },
    ));
    out.push(dyn_rule("eval-nothing", "tuple@0", [], |eg, _, _| {
        let unit = eg.analysis.session.value(&Value::unit());
        Some(eg.add(HanaLang::Push(unit)))
    }));
    out.push(dyn_rule(
        "fold-branch",
        "(; ?l (branch ?t ?f))",
        ["?l", "?t", "?f"],
        |eg, vars, _| {
            let fl = facts(eg, vars[0]);
            let vs = fl.literal.clone()?;
            let (&cond, rest) = vs.split_last()?;
            let taken = if eg.analysis.session.value_of(cond).truthy() {
                vars[1]
            } else {
                vars[2]
            };
            let prefix = literal_chain(eg, fl.arity.inputs, rest);
            Some(eg.add(HanaLang::Compose([prefix, taken])))
        },
    ));
    out.push(dyn_rule(
        "commute",
        "(; swap ?op)",
        ["?op"],
        |eg, vars, _| {
            class_instruction(eg, vars[0])?
                .commutative()
                .then_some(vars[0])
        },
    ));

    // ---- codomains ---------------------------------------------------------
    // The one fact no case split reaches: what an operation is *known to
    // leave*. `Instruction::yields_bool` is measured by `vm`; the analysis
    // lifts it through composition, and this is the rule that spends it.
    out.push(dyn_rule(
        "bool-result",
        "(; ?x is_bool)",
        ["?x"],
        |eg, vars, _| {
            let fx = facts(eg, vars[0]);
            (fx.yields_bool && fx.arity.outputs >= 1).then(|| {
                let dropper = top_drop(eg, fx.arity.outputs - 1);
                let truth = eg.analysis.session.value(&Value::Bool(true));
                let pushed = literal_chain(eg, fx.arity.outputs - 1, &[truth]);
                let suffix = eg.add(HanaLang::Compose([dropper, pushed]));
                eg.add(HanaLang::Compose([vars[0], suffix]))
            })
        },
    ));

    // ---- branches ----------------------------------------------------------
    // A shared suffix distributes into both arms and factors back out.
    out.extend(rewrite!("branch-distribute";
        "(; (branch ?t ?f) ?k)" <=> "(branch (; ?t ?k) (; ?f ?k))"));
    // A framed computation slides into both arms of the branch it precedes:
    // the frame hid exactly the condition.
    out.extend(rewrite!("branch-hoist";
        "(; (* ?x id@1) (branch ?t ?f))" <=> "(branch (; ?x ?t) (; ?x ?f))"));
    // And what runs *beside* a branch runs inside whichever arm it takes: the
    // deeper region the branch never looks at does not care which one that
    // was. The conversion `branch-hoist` cannot say, and the one lowering
    // makes constantly — a branch whose arms are narrower than the stack is
    // emitted framed, and every law about branches is stated unframed.
    out.extend(rewrite!("branch-beside";
        "(* ?x (branch ?t ?f))" <=> "(branch (* ?x ?t) (* ?x ?f))"));
    // The condition was a copy, and both arms open by dropping it: nothing is
    // left of the copy at all.
    out.push(dyn_rule(
        "branch-absorbs-copy",
        "(; ?c (branch (; ?d ?a) (; ?e ?b)))",
        ["?c", "?d", "?a", "?e", "?b"],
        |eg, vars, _| {
            let fc = facts(eg, vars[0]);
            let (fd, fe) = (facts(eg, vars[1]), facts(eg, vars[3]));
            (fc.is_copy
                && fc.arity.inputs == 1
                && fd.is_drop
                && fd.arity.inputs == 1
                && fe.is_drop
                && fe.arity.inputs == 1)
                .then(|| eg.add(HanaLang::Branch([vars[2], vars[4]])))
        },
    ));
    // The same value tested twice answers the same: the arm an outer branch
    // took already decides an inner branch on a copy of its condition, so the
    // other inner arm is dead. Four rules: either arm, with or without a
    // continuation after the inner branch.
    out.push(retest_then(
        "retest-then",
        "(; ?c (branch (; (branch ?p ?q) ?r) ?e))",
        true,
    ));
    out.push(retest_then(
        "retest-then-bare",
        "(; ?c (branch (branch ?p ?q) ?e))",
        false,
    ));
    out.push(retest_else(
        "retest-else",
        "(; ?c (branch ?t (; (branch ?p ?q) ?r)))",
        true,
    ));
    out.push(retest_else(
        "retest-else-bare",
        "(; ?c (branch ?t (branch ?p ?q)))",
        false,
    ));
    // A value that tested `equal` to a literal *is* that literal, inside the
    // arm that saw `true`.
    out.push(dyn_rule(
        "specialize-equal",
        "(; ?c (; ?p (; (* ?i equal) (branch ?t ?f))))",
        ["?c", "?p", "?i", "?t", "?f"],
        |eg, vars, _| {
            let fc = facts(eg, vars[0]);
            let fp = facts(eg, vars[1]);
            let fi = facts(eg, vars[2]);
            let lit = fp.literal.clone()?;
            let [v] = lit[..] else { return None };
            // The copy keeps the original one deep, so the `equal` reading
            // the copy against the literal is always framed over it.
            if !(fc.is_copy && fc.arity.inputs == 1 && fi.is_id && fi.arity.inputs == 1) {
                return None;
            }
            // The then arm holds the original on top; drop it, write the
            // literal in its place, and carry on.
            let dropper = eg.add(HanaLang::Dropn(DropW(1)));
            let pushed = eg.add(HanaLang::Push(v));
            let rewritten = eg.add(HanaLang::Compose([dropper, pushed]));
            let t_new = eg.add(HanaLang::Compose([rewritten, vars[3]]));
            let branch = eg.add(HanaLang::Branch([t_new, vars[4]]));
            let id1 = eg.add(HanaLang::Idn(IdW(1)));
            let equal = eg.add(HanaLang::Equal);
            let framed = eg.add(HanaLang::Par([id1, equal]));
            let tail = eg.add(HanaLang::Compose([framed, branch]));
            let mid = eg.add(HanaLang::Compose([vars[1], tail]));
            Some(eg.add(HanaLang::Compose([vars[0], mid])))
        },
    ));

    // ---- coercions and tuples ----------------------------------------------
    out.extend(rewrite!("as-bool-idem"; "(; as_bool as_bool)" <=> "as_bool"));
    out.extend(rewrite!("as-int-idem"; "(; as_int as_int)" <=> "as_int"));
    out.push(dyn_rule(
        "as-tuple-idem",
        "(; ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let n = class_width(eg, vars[0], as_tuple_width)?;
            let m = class_width(eg, vars[1], as_tuple_width)?;
            (n == m).then(|| eg.add(HanaLang::AsTuplen(AsTupleW(n))))
        },
    ));
    out.push(dyn_rule(
        "tuple-cancel",
        "(; ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let n = class_width(eg, vars[0], tuple_width)?;
            let m = class_width(eg, vars[1], untuple_width)?;
            (n == m).then(|| eg.add(HanaLang::Idn(IdW(n))))
        },
    ));
    out.push(dyn_rule(
        "untuple-retuple",
        "(; ?a ?b)",
        ["?a", "?b"],
        |eg, vars, _| {
            let n = class_width(eg, vars[0], untuple_width)?;
            let m = class_width(eg, vars[1], tuple_width)?;
            (n == m).then(|| eg.add(HanaLang::AsTuplen(AsTupleW(n))))
        },
    ));

    out
}

// ---- the pieces the rules share --------------------------------------------

fn facts(egraph: &ProofGraph, id: Id) -> Facts {
    egraph[id].data.clone()
}

fn one_to_one(f: &Facts) -> bool {
    f.arity.inputs == 1 && f.arity.outputs == 1
}

/// The one instruction a class is spelled as, if any spelling is a single
/// instruction node.
fn class_instruction(egraph: &ProofGraph, id: Id) -> Option<Instruction> {
    egraph[id]
        .nodes
        .iter()
        .find_map(|n| egraph.analysis.session.instruction_of(n))
}

/// Reads a width off a class through one of the leaf projections below.
fn class_width(egraph: &ProofGraph, id: Id, read: fn(&HanaLang) -> Option<usize>) -> Option<usize> {
    egraph[id].nodes.iter().find_map(read)
}

fn as_tuple_width(n: &HanaLang) -> Option<usize> {
    match n {
        HanaLang::AsTuplen(AsTupleW(k)) => Some(*k),
        _ => None,
    }
}

fn tuple_width(n: &HanaLang) -> Option<usize> {
    match n {
        HanaLang::Tuplen(TupleW(k)) => Some(*k),
        _ => None,
    }
}

fn untuple_width(n: &HanaLang) -> Option<usize> {
    match n {
        HanaLang::Untuplen(UntupleW(k)) => Some(*k),
        _ => None,
    }
}

/// The shared body of the two eval rules: a literal prefix feeding an
/// instruction folds to the pushes of what the machine answers.
fn fold_window(eg: &mut ProofGraph, literal: Id, op: Id) -> Option<Id> {
    let fl = facts(eg, literal);
    let vs = fl.literal.clone()?;
    let inst = class_instruction(eg, op)?;
    if matches!(inst, Instruction::Push(_)) {
        return None;
    }
    let k = facts(eg, op).arity.inputs;
    if vs.len() < k {
        return None;
    }
    let operands: Vec<Value> = vs[vs.len() - k..]
        .iter()
        .map(|w| eg.analysis.session.value_of(*w).clone())
        .collect();
    let answers = run_window(&operands, &inst)?;
    let mut result: Vec<PushW> = vs[..vs.len() - k].to_vec();
    for v in &answers {
        result.push(eg.analysis.session.value(v));
    }
    Some(literal_chain(eg, fl.arity.inputs, &result))
}

/// Both counit laws share this shape: a block copy followed by a par that
/// keeps one block (`kept`, an identity) and drops the other.
fn counit(eg: &mut ProofGraph, c: Id, kept: Id, dropped: Id) -> Option<Id> {
    let fc = facts(eg, c);
    let (fk, fd) = (facts(eg, kept), facts(eg, dropped));
    let n = fc.arity.inputs;
    (fc.is_copy && fk.is_id && fk.arity.inputs == n && fd.is_drop && fd.arity.inputs == n)
        .then(|| eg.add(HanaLang::Idn(IdW(n))))
}

/// `drop(1)` at the top of `under + 1` values: the deep `under` pass through.
fn top_drop(eg: &mut ProofGraph, under: usize) -> Id {
    let drop = eg.add(HanaLang::Dropn(DropW(1)));
    if under == 0 {
        drop
    } else {
        let id = eg.add(HanaLang::Idn(IdW(under)));
        eg.add(HanaLang::Par([id, drop]))
    }
}

/// The canonical spelling of "push these values over `inputs` untouched
/// ones" — the shape [`crate::term::lower`] gives a run of pushes, and the
/// shape whose class the literal fact recognizes.
fn literal_chain(eg: &mut ProofGraph, inputs: usize, vs: &[PushW]) -> Id {
    let mut acc = eg.add(HanaLang::Idn(IdW(inputs)));
    for (depth, v) in (inputs..).zip(vs) {
        let push = eg.add(HanaLang::Push(*v));
        let step = if depth == 0 {
            push
        } else {
            let id = eg.add(HanaLang::Idn(IdW(depth)));
            eg.add(HanaLang::Par([id, push]))
        };
        acc = eg.add(HanaLang::Compose([acc, step]));
    }
    acc
}

/// The retest rules, then side: the outer condition was truthy, so an inner
/// branch on a copy of it takes its then arm.
fn retest_then(name: &str, pattern: &str, with_rest: bool) -> ProofRewrite {
    let vars: Vec<&str> = if with_rest {
        vec!["?c", "?p", "?q", "?r", "?e"]
    } else {
        vec!["?c", "?p", "?q", "?e"]
    };
    dyn_rule_vec(name, pattern, vars, move |eg, vars, _| {
        let (c, p, e) = (vars[0], vars[1], *vars.last().unwrap());
        let rest = with_rest.then(|| vars[3]);
        retest_arm(eg, c, p, rest, e, true)
    })
}

/// The retest rules, else side: the outer condition was `false` — the one
/// falsy value — so an inner branch on a copy of it takes its else arm.
fn retest_else(name: &str, pattern: &str, with_rest: bool) -> ProofRewrite {
    let vars: Vec<&str> = if with_rest {
        vec!["?c", "?t", "?p", "?q", "?r"]
    } else {
        vec!["?c", "?t", "?p", "?q"]
    };
    dyn_rule_vec(name, pattern, vars, move |eg, vars, _| {
        let (c, t, q) = (vars[0], vars[1], vars[3]);
        let rest = with_rest.then(|| vars[4]);
        retest_arm(eg, c, q, rest, t, false)
    })
}

/// The shared construction: replace the decided inner branch with "drop the
/// copy, run the arm it would have taken", and put the whole term back
/// together around it.
fn retest_arm(
    eg: &mut ProofGraph,
    c: Id,
    taken: Id,
    rest: Option<Id>,
    other_arm: Id,
    then_side: bool,
) -> Option<Id> {
    let fc = facts(eg, c);
    if !(fc.is_copy && fc.arity.inputs == 1) {
        return None;
    }
    let ft = facts(eg, taken);
    let dropper = top_drop(eg, ft.arity.inputs);
    let decided = eg.add(HanaLang::Compose([dropper, taken]));
    let arm = match rest {
        Some(r) => eg.add(HanaLang::Compose([decided, r])),
        None => decided,
    };
    let arms = if then_side {
        [arm, other_arm]
    } else {
        [other_arm, arm]
    };
    let branch = eg.add(HanaLang::Branch(arms));
    Some(eg.add(HanaLang::Compose([c, branch])))
}

// ---- the applier plumbing ---------------------------------------------------

/// A rule whose right-hand side is computed: match `pattern`, hand the bound
/// classes to `build`, and union what it answers with the match.
///
/// `build` returning `None` is the rule declining — a side condition did not
/// hold. Everything it adds stays in the e-graph either way, which is how egg
/// works and is harmless: an unattached node is never extracted.
fn dyn_rule<const N: usize>(
    name: &str,
    pattern: &str,
    vars: [&str; N],
    build: impl Fn(&mut ProofGraph, &[Id], &Subst) -> Option<Id> + Send + Sync + 'static,
) -> ProofRewrite {
    dyn_rule_vec(name, pattern, vars.to_vec(), build)
}

fn dyn_rule_vec(
    name: &str,
    pattern: &str,
    vars: Vec<&str>,
    build: impl Fn(&mut ProofGraph, &[Id], &Subst) -> Option<Id> + Send + Sync + 'static,
) -> ProofRewrite {
    struct Build<F> {
        vars: Vec<Var>,
        build: F,
    }
    impl<F> Applier<HanaLang, Proving> for Build<F>
    where
        F: Fn(&mut ProofGraph, &[Id], &Subst) -> Option<Id> + Send + Sync + 'static,
    {
        fn apply_one(
            &self,
            egraph: &mut ProofGraph,
            eclass: Id,
            subst: &Subst,
            _searcher_ast: Option<&PatternAst<HanaLang>>,
            rule_name: Symbol,
        ) -> Vec<Id> {
            let bound: Vec<Id> = self.vars.iter().map(|v| subst[*v]).collect();
            match (self.build)(egraph, &bound, subst) {
                Some(other) if egraph.union_trusted(eclass, other, rule_name) => vec![other],
                _ => vec![],
            }
        }
    }
    let searcher: Pattern<HanaLang> = pattern.parse().unwrap_or_else(|e| {
        panic!(
            "rule {} has an unparseable pattern {:?}: {}",
            name, pattern, e
        )
    });
    let vars = vars
        .into_iter()
        .map(|v| v.parse().expect("a var spelled ?x"))
        .collect();
    Rewrite::new(name, searcher, Build { vars, build }).expect("a well-formed rewrite")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr_of;
    use crate::term::{Arity, Prim, Term};
    use egg::Runner;

    /// Saturates the two terms and answers whether they met.
    fn provable(lhs: &Term, rhs: &Term) -> bool {
        let mut analysis = Proving::default();
        let lhs = expr_of(lhs, &mut analysis.session);
        let rhs = expr_of(rhs, &mut analysis.session);
        let runner = Runner::default()
            .with_explanations_enabled()
            .with_egraph(egg::EGraph::new(analysis))
            .with_expr(&lhs)
            .with_expr(&rhs)
            .run(&rules());
        let (l, r) = (runner.roots[0], runner.roots[1]);
        runner.egraph.find(l) == runner.egraph.find(r)
    }

    fn op(p: Prim) -> Term {
        Term::op(p)
    }

    #[test]
    fn a_test_of_a_test_is_decided() {
        // `is_bool ; is_bool` = `drop ; push true`.
        let lhs = Term::pad_compose(op(Prim::IsBool), op(Prim::IsBool));
        let rhs = Term::pad_compose(Term::drop(1), op(Prim::Push(Value::Bool(true))));
        assert!(provable(&lhs, &rhs));
    }

    #[test]
    fn two_spellings_of_one_test_meet_in_the_middle() {
        // `is_bool ; is_bool` = `is_int ; is_bool`: neither reduces to the
        // other, and the e-graph does not care.
        let lhs = Term::pad_compose(op(Prim::IsBool), op(Prim::IsBool));
        let rhs = Term::pad_compose(op(Prim::IsInt), op(Prim::IsBool));
        assert!(provable(&lhs, &rhs));
    }

    #[test]
    fn a_literal_window_folds_to_what_the_machine_answers() {
        // `push 1 ; push 2 ; add` = `push 3`, junk semantics included.
        let lhs = Term::pad_compose(
            Term::pad_compose(op(Prim::Push(Value::Int(1))), op(Prim::Push(Value::Int(2)))),
            op(Prim::Add),
        );
        assert!(provable(&lhs, &op(Prim::Push(Value::Int(3)))));

        // And off the domain: `push true ; push 2 ; add` = `push 0`.
        let junk = Term::pad_compose(
            Term::pad_compose(
                op(Prim::Push(Value::Bool(true))),
                op(Prim::Push(Value::Int(2))),
            ),
            op(Prim::Add),
        );
        assert!(provable(&junk, &op(Prim::Push(Value::Int(0)))));
    }

    #[test]
    fn copying_a_constant_is_pushing_it_twice() {
        // `push 9 ; copy` = `push 9 ; push 9` — the constant case of copy
        // naturality, reached through the staircases.
        let nine = || op(Prim::Push(Value::Int(9)));
        let lhs = Term::pad_compose(nine(), Term::copy(1));
        let rhs = Term::pad_compose(nine(), nine());
        assert!(provable(&lhs, &rhs));
    }

    #[test]
    fn discarded_work_is_no_work() {
        // `equal ; drop` = `drop ; drop`.
        let lhs = Term::pad_compose(op(Prim::Equal), Term::drop(1));
        let rhs = Term::pad_compose(Term::drop(1), Term::drop(1));
        assert!(provable(&lhs, &rhs));
    }

    #[test]
    fn a_frame_comes_off_as_rolls() {
        // `not * id(1)` = `swap ; id(1) * not ; swap`.
        let lhs = Term::par(op(Prim::Not), Term::id(1));
        let rhs = Term::pad_compose(
            Term::pad_compose(op(Prim::Swap), Term::par(Term::id(1), op(Prim::Not))),
            op(Prim::Swap),
        );
        assert!(provable(&lhs, &rhs));
    }

    #[test]
    fn a_frame_beside_a_branch_opens_into_the_arms() {
        // `id(1) * branch { A } { B }` = `branch { id(1)*A } { id(1)*B }`.
        // Lowering emits the left whenever a branch's arms are narrower than
        // the stack, and every other branch law is stated about the right.
        let arm = |v| Term::pad_compose(Term::drop(1), op(Prim::Push(Value::Int(v))));
        let framed = Term::par(Term::id(1), Term::branch(arm(1), arm(2)).unwrap());
        let opened = Term::branch(
            Term::par(Term::id(1), arm(1)),
            Term::par(Term::id(1), arm(2)),
        )
        .unwrap();
        assert!(provable(&framed, &opened));
    }

    #[test]
    fn a_branch_surfaces_through_a_frame() {
        // `id(1) * (P ; branch { … })` — the shape an inlined call takes —
        // meets its spread spelling, where the branch stands alone and the
        // commuting conversions can reach it. `frame-split-deep` is the only
        // road: nothing else opens a composition inside a framed leg.
        let tst = |v| op(Prim::Push(Value::Bool(v)));
        let body = Term::compose(
            Term::op(Prim::IsBool),
            Term::branch(tst(true), tst(false)).unwrap(),
        )
        .unwrap();
        let framed = Term::par(Term::id(1), body);
        let spread = Term::compose(
            Term::par(Term::id(1), op(Prim::IsBool)),
            Term::par(Term::id(1), Term::branch(tst(true), tst(false)).unwrap()),
        )
        .unwrap();
        assert!(provable(&framed, &spread));
    }

    #[test]
    fn an_unequal_pair_of_terms_does_not_meet() {
        let one = op(Prim::Push(Value::Int(1)));
        let two = op(Prim::Push(Value::Int(2)));
        assert!(!provable(&one, &two));
    }

    #[test]
    fn the_block_counit_closes_alone() {
        // `copy(2) ; id(2) * drop(2)` = `id(2)`: the counit at block width,
        // which is what `discarded_work_on_copies` bottoms out in.
        let lhs = Term::compose(Term::copy(2), Term::par(Term::id(2), Term::drop(2))).unwrap();
        assert!(provable(&lhs, &Term::id(2)));
    }

    #[test]
    fn every_rule_survives_the_corpus_smoke() {
        // The rules on a term with a call in it: nothing panics, nothing
        // unions across arities (the analysis would assert).
        let call = Term::call(bytecode::SentenceIndex::from(7), Arity::new(2, 1));
        let lhs = Term::pad_compose(call.clone(), Term::drop(1));
        let rhs = Term::drop(2);
        assert!(provable(&lhs, &rhs), "drop-nat reads a call's arity");
    }
}
