//! A term rewritten into a listing: layers composed in order, one box each.
//!
//! A [`Term`] hides its boxes inside `*` and `;` trees that the lowering
//! shaped around padding — `dip 3 { X }` as three nested one-deep frames, a
//! spine leaning left because `pad_compose` folds that way. None of that is
//! wrong and all of it is in the way: anything that wants to talk about *what
//! a program does one step at a time* has to see the steps first.
//!
//! [`flatten`] rewrites a term into a **listing** and hands back the
//! derivation that got there, in the steps of [`crate::rules`]. Nothing here
//! is trusted: every step it emits is checked by `replay`, so a bug in this
//! module makes a derivation that fails rather than one that lies.
//!
//! ## What a listing is
//!
//! Layers composed in order, right-nested, each layer a `*`-product of leaves
//! with exactly one factor that is not an `id`. [`is_flat`] and [`is_layer`]
//! are the definition — a predicate something can check, not a comment.
//!
//! The `*`-association is deliberately **free**. `id(d) * (x * id(u))` and
//! `(id(d) * x) * id(u)` are both layers, which is what lets a frame slide
//! over a layer without renegotiating its shape, and is why nothing here
//! reaches for `AssocPar` — a rule whose two directions undo each other, and
//! which a pass that needed it would not terminate against.
//!
//! The empty listing is `id(n)`: a chain of no layers still has to say how
//! wide it is.
//!
//! ## How it gets there
//!
//! Three recursive pieces, each draining on something that shrinks, so there
//! is no fixpoint loop and no budget. [`flat`] descends the term. [`spread`]
//! pushes a frame onto each layer of a listing, peeling one layer per turn.
//! [`join`] melts two listings into one, peeling the left chain into the
//! right.
//!
//! Blocks are left whole: `copy(3)` is one generator, because a listing asks
//! for one generator per step and a block is one. Splitting it into one-wire
//! copies wants `CopySplit`, which wants the block swap, which belongs to a
//! later pass.

use crate::rules::{
    Direction, Error, Law, Leg, Path, Step, apply, at, compose_of, id_of, par_of, read,
};
use crate::term::{Context, Term, TermIndex};

// ---- flattening a term into a listing ------------------------------------------

/// Whether the term is one **layer**: a `*`-product of leaves with exactly
/// one factor that is not an `id`.
///
/// The `*`-association is deliberately free. `id(d) * (x * id(u))` and
/// `(id(d) * x) * id(u)` are both layers, which is what lets a frame be
/// slid over a layer without renegotiating its shape — and is why
/// [`flatten`] never needs `AssocPar`, whose two directions would otherwise
/// undo each other forever.
pub fn is_layer(ctx: &Context, t: TermIndex) -> bool {
    match generators(ctx, t) {
        Some(gs) => gs.len() == 1 && gs.iter().all(|&g| flat_within(ctx, g)),
        None => false,
    }
}

/// The non-`id` leaves of a `*`-tree, or `None` if a `;` is in the way.
fn generators(ctx: &Context, t: TermIndex) -> Option<Vec<TermIndex>> {
    match ctx.get(t) {
        Term::Id(_) => Some(Vec::new()),
        Term::Drop(_) | Term::Copy(_) | Term::Op(_) | Term::Call { .. } | Term::Branch { .. } => {
            Some(vec![t])
        }
        Term::Par(l, r) => {
            let (l, r) = (*l, *r);
            let mut found = generators(ctx, l)?;
            found.extend(generators(ctx, r)?);
            Some(found)
        }
        Term::Compose(_, _) => None,
    }
}

/// A branch's arms are listings too; anything else has no inside to check.
fn flat_within(ctx: &Context, g: TermIndex) -> bool {
    match ctx.get(g) {
        Term::Branch { if_true, if_false } => {
            let (t, f) = (*if_true, *if_false);
            is_flat(ctx, t) && is_flat(ctx, f)
        }
        _ => true,
    }
}

/// Whether the term is a **listing**: layers composed in order, right-nested,
/// with no layer that does nothing.
///
/// The empty listing is `id(n)` — a chain of no layers still has to say how
/// wide it is.
pub fn is_flat(ctx: &Context, t: TermIndex) -> bool {
    match ctx.get(t) {
        Term::Compose(l, r) => {
            let (l, r) = (*l, *r);
            is_layer(ctx, l) && is_flat(ctx, r)
        }
        Term::Id(_) => true,
        _ => is_layer(ctx, t),
    }
}

/// The term as a listing, and the derivation that gets there.
///
/// Every step is one of the skeleton laws — the interchange doing the work,
/// the units making room for it — so the result is the same program written
/// one box at a time. [`replay`]ing the steps on the input reproduces the
/// output exactly, which is what the tests check rather than assume.
///
/// Blocks are not split: `copy(3)` stays one generator, because a listing
/// asks for one *generator* per step and a block is one. Splitting it into
/// one-wire copies needs `CopySplit`, which needs the block swap, which is
/// the absorb loop's business rather than this pass's.
pub fn flatten(ctx: &mut Context, t: TermIndex) -> Result<(TermIndex, Vec<Step>), Error> {
    let mut steps = Vec::new();
    let out = flat(ctx, t, &mut steps)?;
    Ok((out, steps))
}

/// One rewrite, applied and recorded.
///
/// The law is named; the payload is *read* off the term at the path. That is
/// the division this module is built around — flattening decides which
/// equation to spend and where, and never writes a rule down by hand.
fn step(
    ctx: &mut Context,
    t: TermIndex,
    path: Path,
    law: Law,
    dir: Direction,
    steps: &mut Vec<Step>,
) -> Result<TermIndex, Error> {
    let focus = at(ctx, t, &path)?;
    let rule = read(ctx, focus, law, dir).ok_or(Error::NotThere { law, dir })?;
    let step = Step { path, rule, dir };
    let out = apply(ctx, t, &step)?;
    steps.push(step);
    Ok(out)
}

/// Steps written against a subterm, re-addressed against its parent.
fn beneath(leg: Leg, from: usize, steps: &mut [Step]) {
    for s in &mut steps[from..] {
        s.path.insert(0, leg);
    }
}

fn flat(ctx: &mut Context, t: TermIndex, steps: &mut Vec<Step>) -> Result<TermIndex, Error> {
    match ctx.get(t).clone() {
        Term::Id(_) | Term::Drop(_) | Term::Copy(_) | Term::Op(_) | Term::Call { .. } => Ok(t),

        // A branch is one generator whose arms are listings of their own.
        Term::Branch { if_true, if_false } => {
            let mark = steps.len();
            let yes = flat(ctx, if_true, steps)?;
            beneath(Leg::BranchTrue, mark, steps);
            let mark = steps.len();
            let no = flat(ctx, if_false, steps)?;
            beneath(Leg::BranchFalse, mark, steps);
            Ok(ctx.branch(yes, no)?)
        }

        Term::Compose(a, b) => {
            let mark = steps.len();
            let a = flat(ctx, a, steps)?;
            beneath(Leg::ComposeLeft, mark, steps);
            let mark = steps.len();
            let b = flat(ctx, b, steps)?;
            beneath(Leg::ComposeRight, mark, steps);
            let joined = ctx.compose(a, b)?;
            join(ctx, joined, steps)
        }

        Term::Par(a, b) => {
            // A width-zero side is not there at all.
            if id_of(ctx, a) == Some(0) {
                let out = step(
                    ctx,
                    t,
                    Vec::new(),
                    Law::UnitParLeft,
                    Direction::Forward,
                    steps,
                )?;
                return flat(ctx, out, steps);
            }
            if id_of(ctx, b) == Some(0) {
                let out = step(
                    ctx,
                    t,
                    Vec::new(),
                    Law::UnitParRight,
                    Direction::Forward,
                    steps,
                )?;
                return flat(ctx, out, steps);
            }
            // Two blocks of wire are one block of wire.
            if id_of(ctx, a).is_some() && id_of(ctx, b).is_some() {
                return step(ctx, t, Vec::new(), Law::IdFuse, Direction::Forward, steps);
            }

            // One side a frame: flatten the other in place, then slide the
            // frame over each layer it left behind.
            if id_of(ctx, a).is_some() {
                let mark = steps.len();
                let b = flat(ctx, b, steps)?;
                beneath(Leg::ParRight, mark, steps);
                let framed = ctx.par(a, b);
                if id_of(ctx, b).is_some() {
                    return step(
                        ctx,
                        framed,
                        Vec::new(),
                        Law::IdFuse,
                        Direction::Forward,
                        steps,
                    );
                }
                return spread(ctx, framed, Leg::ParRight, steps);
            }
            if id_of(ctx, b).is_some() {
                let mark = steps.len();
                let a = flat(ctx, a, steps)?;
                beneath(Leg::ParLeft, mark, steps);
                let framed = ctx.par(a, b);
                if id_of(ctx, a).is_some() {
                    return step(
                        ctx,
                        framed,
                        Vec::new(),
                        Law::IdFuse,
                        Direction::Forward,
                        steps,
                    );
                }
                return spread(ctx, framed, Leg::ParLeft, steps);
            }

            // Neither side is wire: make each into a frame of its own, which
            // is the interchange read as "side by side is one after the
            // other".
            let out = step(
                ctx,
                t,
                vec![Leg::ParLeft],
                Law::UnitRight,
                Direction::Backward,
                steps,
            )?;
            let out = step(
                ctx,
                out,
                vec![Leg::ParRight],
                Law::UnitLeft,
                Direction::Backward,
                steps,
            )?;
            let out = step(
                ctx,
                out,
                Vec::new(),
                Law::Interchange,
                Direction::Forward,
                steps,
            )?;
            flat(ctx, out, steps)
        }
    }
}

/// A frame beside a listing, pushed onto each of its layers.
///
/// `side` says which half of the `*` holds the listing. Each turn of the
/// loop peels one layer off the front, so it drains.
fn spread(
    ctx: &mut Context,
    t: TermIndex,
    side: Leg,
    steps: &mut Vec<Step>,
) -> Result<TermIndex, Error> {
    let (a, b) = par_of(ctx, t).expect("spread is given a frame");
    let inner = match side {
        Leg::ParRight => b,
        _ => a,
    };
    // A listing of one layer needs no spreading: the frame beside a layer is
    // a layer.
    if compose_of(ctx, inner).is_none() {
        return Ok(t);
    }
    // Split the wire so the interchange has two composites to cut between.
    let wire = match side {
        Leg::ParRight => Leg::ParLeft,
        _ => Leg::ParRight,
    };
    let out = step(
        ctx,
        t,
        vec![wire],
        Law::UnitLeft,
        Direction::Backward,
        steps,
    )?;
    let out = step(
        ctx,
        out,
        Vec::new(),
        Law::Interchange,
        Direction::Forward,
        steps,
    )?;
    // Now `frame*first ; frame*rest`; the rest gets the same treatment.
    let (first, rest) = compose_of(ctx, out).expect("the interchange left a composition");
    let mark = steps.len();
    let rest = spread(ctx, rest, side, steps)?;
    beneath(Leg::ComposeRight, mark, steps);
    let out = ctx.compose(first, rest)?;
    join(ctx, out, steps)
}

/// Two listings composed, made into one: the left chain is peeled into the
/// right until nothing is left of it but a layer, and a chain that does
/// nothing is dropped.
fn join(ctx: &mut Context, t: TermIndex, steps: &mut Vec<Step>) -> Result<TermIndex, Error> {
    let Some((left, right)) = compose_of(ctx, t) else {
        return Ok(t);
    };
    if id_of(ctx, left).is_some() {
        return step(ctx, t, Vec::new(), Law::UnitLeft, Direction::Forward, steps);
    }
    if id_of(ctx, right).is_some() {
        return step(
            ctx,
            t,
            Vec::new(),
            Law::UnitRight,
            Direction::Forward,
            steps,
        );
    }
    if compose_of(ctx, left).is_none() {
        return Ok(t);
    }
    let out = step(
        ctx,
        t,
        Vec::new(),
        Law::AssocCompose,
        Direction::Forward,
        steps,
    )?;
    let (first, rest) = compose_of(ctx, out).expect("re-association left a composition");
    let mark = steps.len();
    let rest = join(ctx, rest, steps)?;
    beneath(Leg::ComposeRight, mark, steps);
    Ok(ctx.compose(first, rest)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram::{Ctx, normalize};
    use crate::rules::replay;
    use crate::term::Prim;

    // ---- flattening ----

    fn probe(ctx: &mut Context, body: &str) -> TermIndex {
        let code = format!("sentence probe {{ {} }}", body);
        let library = bytecode::assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(i, _)| i)
            .unwrap();
        crate::term::lower(ctx, &library, idx).unwrap()
    }

    /// Flattening a term: the result is a listing, replaying the steps
    /// reproduces it, and nothing about what the term computes moved.
    fn flattens_to(body: &str, want: &str) {
        let mut ctx = Context::new();
        let t = probe(&mut ctx, body);
        let (out, steps) = flatten(&mut ctx, t).unwrap();

        assert!(
            is_flat(&ctx, out),
            "`{}` flattened to {}, which is not a listing",
            body,
            ctx.display(out)
        );
        assert_eq!(
            format!("{}", ctx.display(out)),
            want,
            "flattening `{}`",
            body
        );

        let replayed = replay(&mut ctx, t, &steps).unwrap();
        assert!(
            ctx.equal(replayed, out),
            "`{}`: replay gave {}, flatten gave {}",
            body,
            ctx.display(replayed),
            ctx.display(out)
        );

        let mut engine = Ctx::default();
        assert_eq!(
            normalize(&mut engine, &ctx, t),
            normalize(&mut engine, &ctx, out),
            "flattening `{}` changed what it computes",
            body
        );
    }

    #[test]
    fn a_listing_is_one_generator_per_step() {
        // `dip` frames stay frames; the padding `id`s the lowering put in
        // are what the units take away.
        flattens_to("not", "not");
        flattens_to("dip 1 { not }", "not * id(1)");
        flattens_to("swap swap", "swap ; swap");
        flattens_to("pick 0 add", "copy(1) ; add");
        flattens_to("pick 1", "copy(1) * id(1) ; id(1) * swap");
        flattens_to("dip 1 { not } not", "not * id(1) ; id(1) * not");
    }

    #[test]
    fn a_listing_with_nothing_in_it_is_a_width() {
        // `id(0) * id(2)` and friends fuse rather than surviving as layers
        // that do nothing.
        let mut ctx = Context::new();
        let t = {
            let (a, b) = (ctx.id(0), ctx.id(2));
            ctx.par(a, b)
        };
        let (out, steps) = flatten(&mut ctx, t).unwrap();
        assert_eq!(format!("{}", ctx.display(out)), "id(2)");
        assert!(is_flat(&ctx, out));
        let replayed = replay(&mut ctx, t, &steps).unwrap();
        assert!(ctx.equal(replayed, out));
    }

    #[test]
    fn a_branch_is_one_generator_whose_arms_are_listings() {
        flattens_to(
            "branch { dip 1 { not } } { dip 1 { not } }",
            "branch { not * id(1) } { not * id(1) }",
        );
    }

    #[test]
    fn what_is_flat_accepts_and_refuses() {
        let mut ctx = Context::new();
        // A layer may associate its `*` either way.
        let left = {
            let (d, g) = (ctx.id(1), ctx.op(Prim::Not));
            let inner = ctx.par(d, g);
            let u = ctx.id(1);
            ctx.par(inner, u)
        };
        let right = {
            let d = ctx.id(1);
            let (g, u) = (ctx.op(Prim::Not), ctx.id(1));
            let inner = ctx.par(g, u);
            ctx.par(d, inner)
        };
        assert!(is_layer(&ctx, left) && is_layer(&ctx, right));

        // Two generators in one step is not a layer.
        let two = {
            let (a, b) = (ctx.op(Prim::Not), ctx.op(Prim::Not));
            ctx.par(a, b)
        };
        assert!(!is_layer(&ctx, two));

        // Neither is a step that does nothing...
        let idle = {
            let (a, b) = (ctx.id(1), ctx.id(1));
            ctx.par(a, b)
        };
        assert!(!is_layer(&ctx, idle));

        // ...nor a chain hiding inside a `*`.
        let buried = {
            let (a, b) = (ctx.op(Prim::Not), ctx.op(Prim::Not));
            let chain = ctx.compose(a, b).unwrap();
            let u = ctx.id(1);
            ctx.par(chain, u)
        };
        assert!(!is_layer(&ctx, buried));

        // A left-nested chain is not a listing; a right-nested one is.
        let (x, y, z) = (ctx.op(Prim::Not), ctx.op(Prim::Not), ctx.op(Prim::Not));
        let leaning = {
            let xy = ctx.compose(x, y).unwrap();
            ctx.compose(xy, z).unwrap()
        };
        assert!(!is_flat(&ctx, leaning));
        let upright = {
            let yz = ctx.compose(y, z).unwrap();
            ctx.compose(x, yz).unwrap()
        };
        assert!(is_flat(&ctx, upright));
    }

    /// The load-bearing test: every sentence of the corpus flattens, the
    /// result is a listing, the recorded steps replay to it, and the engine
    /// agrees that nothing changed.
    #[test]
    fn the_whole_corpus_flattens() {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the crate sits in the workspace")
            .join("tests");
        let text = std::fs::read_to_string(tests.join("main.hana")).unwrap();
        let mut map = bytecode::SourceMap::new();
        let file = map.add("main.hana", text);
        let library = bytecode::assemble_source(&mut map, file, Some(&tests))
            .unwrap_or_else(|e| panic!("{}", map.render(&e)));

        let mut ctx = Context::new();
        let terms = crate::term::lower_all(&mut ctx, &library).unwrap();
        assert!(terms.len() > 100, "the corpus should be a real one");

        let mut engine = Ctx::default();
        let mut layers = 0usize;
        for (idx, &term) in terms.iter_enumerated() {
            let name = &library.names[idx];
            let (out, steps) =
                flatten(&mut ctx, term).unwrap_or_else(|e| panic!("sentence {}: {}", name, e));

            assert!(
                is_flat(&ctx, out),
                "sentence {} flattened to something that is not a listing:\n  {}",
                name,
                ctx.display(out)
            );
            assert_eq!(
                ctx.arity(out),
                ctx.arity(term),
                "sentence {} changed arity through flattening",
                name
            );
            let replayed = replay(&mut ctx, term, &steps)
                .unwrap_or_else(|e| panic!("sentence {} did not replay: {}", name, e));
            assert!(
                ctx.equal(replayed, out),
                "sentence {}: replay and flatten disagree",
                name
            );
            assert_eq!(
                normalize(&mut engine, &ctx, term),
                normalize(&mut engine, &ctx, out),
                "flattening changed what sentence {} computes",
                name
            );
            layers += steps.len();
        }
        assert!(layers > 0, "the corpus flattened without a single step");
    }
}
