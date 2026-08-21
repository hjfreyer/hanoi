//! Rewriting terms by named laws, one step at a time.
//!
//! [`crate::diagram`] decides whether two terms are equal and says nothing
//! about why; [`crate::diagram2`] rewrites a graph and leaves the term
//! language behind. This module is the third thing: a **derivation** — a list
//! of [`Step`]s, each naming one law of [docs/algebra.md](../../docs/algebra.md)
//! and one place to apply it — together with a [`replay`] that checks one.
//!
//! The point is the trusted base. `replay` knows the [`Rule`] table, the
//! [`Term`] language and nothing else: no arena of wires, no interning, no
//! condition order, no engine. A derivation that replays is a claim anyone
//! can check against the table below, which is one page, instead of against
//! a normalizer, which is not.
//!
//! ## A rule states its equation; the checker only compares
//!
//! A [`Law`] names one row of the table with its metavariables open. A
//! [`Rule`] is that row filled in, and it carries enough to build **both**
//! sides: [`sides`] reads the payload, tests nothing, and takes no term
//! apart.
//!
//! So checking a step is small enough to state in a sentence — build the two
//! sides, see that the term at the [`Path`] is the one the step claims, hand
//! back the other. The only way a step can be wrong is that two terms differ.
//! There is no destructuring here to go wrong, and no way for a rule to
//! quietly mean something other than what it says.
//!
//! Widths a payload determines are not carried. `UnitLeft { a }` is `id(n) ;
//! a = a` with `n` read off `a`'s own arity, because carrying `n` as well
//! would let a derivation state a rule whose two halves disagree. Arity side
//! conditions are not checked either, they are *enforced*: `swap-nat` wants a
//! one-wire box, and a box of any other arity makes neither side compose, so
//! the checked constructors refuse the rule before anything is compared.
//!
//! The matching lives in [`read`], outside the trusted base. Everything it
//! does — taking a term apart, comparing a width, seeing that two halves
//! agree — is checked by [`apply`] anyway, so a matcher that is wrong makes a
//! derivation that fails to replay rather than one that proves something
//! false.
//!
//! Three directions cannot be read off a term, and they are the three that
//! would have to invent what the other side spends: [`Law::IdFuse`] backward
//! is not told where to split a block, [`Law::DropSplit`] forward the same,
//! and [`Law::DropNat`] backward cannot say what work vanished — that law is
//! what makes work vanish. Those are choices, and they belong to whatever
//! writes the derivation.
//!
//! ## Which laws are here
//!
//! Layer 1 of the algebra sheet, which that sheet marks *representation* —
//! true in the wiring because the wiring cannot spell them. A term can spell
//! them, so here they are axioms. Two are worth pointing at: the sheet calls
//! Yang–Baxter "an instance" and it is, of pure wiring, but a term
//! presentation of the permutation fragment needs [`Rule::YangBaxter`] — `σ² =
//! id` and far-commutation alone present the infinite dihedral group, not the
//! symmetric ones. The block splits are the same story.
//!
//! One law from layer 3 comes along as the template for the rest:
//! [`Rule::NotNot`], `not ; not = as_bool`. It is not restated here — the
//! machine defines it, and `vm` already asserts it for every shape of value.
//!
//! [`crate::flatten`] is the first thing written against this table.

use crate::term::{Arity, Context, Prim, Term, TermIndex};

// ---- where a step lands ---------------------------------------------------------

/// One move down into a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leg {
    /// The first half of a `;`.
    ComposeLeft,
    /// The second half of a `;`.
    ComposeRight,
    /// The deep side of a `*`.
    ParLeft,
    /// The top side of a `*`.
    ParRight,
    /// A branch's `true` arm.
    BranchTrue,
    /// A branch's `false` arm.
    BranchFalse,
}

/// Where in a term a step applies: legs from the root, outermost first.
pub type Path = Vec<Leg>;

/// Which side of a rule's equation to match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Match the left-hand side, leave the right.
    Forward,
    /// Match the right-hand side, leave the left.
    Backward,
}

impl Direction {
    fn flipped(self) -> Direction {
        match self {
            Direction::Forward => Direction::Backward,
            Direction::Backward => Direction::Forward,
        }
    }
}

// ---- the laws -------------------------------------------------------------------

/// Which equation, with its metavariables still open.
///
/// A [`Law`] names one row of the table; a [`Rule`] is that row with its
/// blanks filled in. The split is what keeps matching out of the checker:
/// asking *which law applies here* is a search, and searches belong to
/// whatever writes a derivation, not to what checks one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Law {
    AssocCompose,
    UnitLeft,
    UnitRight,
    AssocPar,
    UnitParLeft,
    UnitParRight,
    IdFuse,
    Interchange,
    SwapInvol,
    SwapNat,
    YangBaxter,
    CopyAssoc,
    CopyComm,
    CopyCounit,
    CopyNat,
    DropNat,
    DropSplit,
    CopyZero,
    DropZero,
    NotNot,
}

/// One equation, stated outright.
///
/// Every variant carries enough to build **both** sides — no side is left to
/// be recovered by looking at the term it is applied to. That is the whole
/// contract: [`sides`] reads the payload and nothing else, so checking a step
/// is building two terms and comparing one of them against what is there.
///
/// Widths that a payload determines are not carried. `UnitLeft { a }` is
/// `id(n) ; a = a` with `n` the input width of `a`, because a term knows its
/// own arity; carrying `n` as well would let a derivation state a rule whose
/// two halves disagree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    /// `(a ; b) ; c  =  a ; (b ; c)`
    AssocCompose {
        a: TermIndex,
        b: TermIndex,
        c: TermIndex,
    },
    /// `id(n) ; a  =  a`
    UnitLeft { a: TermIndex },
    /// `a ; id(m)  =  a`
    UnitRight { a: TermIndex },
    /// `(a * b) * c  =  a * (b * c)`
    AssocPar {
        a: TermIndex,
        b: TermIndex,
        c: TermIndex,
    },
    /// `id(0) * a  =  a`
    UnitParLeft { a: TermIndex },
    /// `a * id(0)  =  a`
    UnitParRight { a: TermIndex },
    /// `id(n) * id(m)  =  id(n + m)`
    IdFuse { n: usize, m: usize },
    /// `(a ; c) * (b ; d)  =  (a * b) ; (c * d)` — the interchange, and with
    /// it the fact that `*` and `;` are one grid rather than two orders.
    Interchange {
        a: TermIndex,
        b: TermIndex,
        c: TermIndex,
        d: TermIndex,
    },
    /// `swap ; swap  =  id(2)`
    SwapInvol,
    /// `(g * id(1)) ; swap  =  swap ; (id(1) * g)` for `g : 1 -> 1` — σ
    /// natural. The width is not a side condition to check: a `g` of any
    /// other arity makes neither side compose, so [`sides`] refuses it.
    SwapNat { g: TermIndex },
    /// The braid relation, on the left-nested spelling of both triples:
    /// `(swap * id(1)) ; (id(1) * swap) ; (swap * id(1))
    ///  = (id(1) * swap) ; (swap * id(1)) ; (id(1) * swap)`.
    ///
    /// An axiom, not a lemma: `swap ; swap = id(2)` and the interchange
    /// present the infinite dihedral group without it.
    YangBaxter,
    /// `copy(1) ; (copy(1) * id(1))  =  copy(1) ; (id(1) * copy(1))` — δ
    /// coassociative.
    CopyAssoc,
    /// `copy(1) ; swap  =  copy(1)` — δ cocommutative.
    CopyComm,
    /// `copy(1) ; (id(1) * drop(1))  =  id(1)` — the counit.
    CopyCounit,
    /// `g ; copy(l)  =  copy(k) ; (g * g)` for `g : k -> l` — δ natural,
    /// which is to say copying an answer is running twice on copied
    /// arguments. Sound because the language is pure and total.
    CopyNat { g: TermIndex },
    /// `g ; drop(l)  =  drop(k)` for `g : k -> l` — ε natural: discarded
    /// work is no work.
    DropNat { g: TermIndex },
    /// `drop(n + m)  =  drop(n) * drop(m)`
    DropSplit { n: usize, m: usize },
    /// `copy(0)  =  id(0)` — no wires at all, spelled two ways.
    CopyZero,
    /// `drop(0)  =  id(0)`
    DropZero,
    /// `not ; not  =  as_bool` — the coercion spelled the long way round.
    /// A layer-3 law, here as the template for the rest; `vm` measures it.
    NotNot,
}

impl Rule {
    /// Which row of the table this is an instance of.
    pub fn law(&self) -> Law {
        match self {
            Rule::AssocCompose { .. } => Law::AssocCompose,
            Rule::UnitLeft { .. } => Law::UnitLeft,
            Rule::UnitRight { .. } => Law::UnitRight,
            Rule::AssocPar { .. } => Law::AssocPar,
            Rule::UnitParLeft { .. } => Law::UnitParLeft,
            Rule::UnitParRight { .. } => Law::UnitParRight,
            Rule::IdFuse { .. } => Law::IdFuse,
            Rule::Interchange { .. } => Law::Interchange,
            Rule::SwapInvol => Law::SwapInvol,
            Rule::SwapNat { .. } => Law::SwapNat,
            Rule::YangBaxter => Law::YangBaxter,
            Rule::CopyAssoc => Law::CopyAssoc,
            Rule::CopyComm => Law::CopyComm,
            Rule::CopyCounit => Law::CopyCounit,
            Rule::CopyNat { .. } => Law::CopyNat,
            Rule::DropNat { .. } => Law::DropNat,
            Rule::DropSplit { .. } => Law::DropSplit,
            Rule::CopyZero => Law::CopyZero,
            Rule::DropZero => Law::DropZero,
            Rule::NotNot => Law::NotNot,
        }
    }
}

/// One rewrite: a place, an equation, and which way round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    pub path: Path,
    pub rule: Rule,
    pub dir: Direction,
}

impl Step {
    /// A step at the root.
    pub fn here(rule: Rule, dir: Direction) -> Step {
        Step {
            path: Vec::new(),
            rule,
            dir,
        }
    }

    /// The same step read the other way — what reversing a derivation does
    /// to each of its steps.
    pub fn reversed(&self) -> Step {
        Step {
            path: self.path.clone(),
            rule: self.rule.clone(),
            dir: self.dir.flipped(),
        }
    }
}

/// A derivation read backwards: equality is symmetric, so a path from `A` to
/// `R` is a path from `R` to `A` with every step flipped and the order
/// undone. This is what closes the valley — `derive(A)` against the reverse
/// of `derive(B)`.
pub fn reversed(steps: &[Step]) -> Vec<Step> {
    steps.iter().rev().map(Step::reversed).collect()
}

// ---- what can go wrong ----------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The path walked into something that does not have that leg.
    NoSuchLeg { at: usize, leg: Leg },
    /// The term at the path is not the side of the equation the step says it
    /// is. This is the only way a step can be wrong, and it is decided by
    /// comparing two terms.
    NotThere { law: Law, dir: Direction },
    /// The payload does not state an equation: one of its two sides does not
    /// compose. A rule that cannot be built cannot be applied.
    Ill(crate::term::Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NoSuchLeg { at, leg } => {
                write!(
                    f,
                    "the path takes {:?} at depth {}, which is not there",
                    leg, at
                )
            }
            Error::NotThere { law, dir } => write!(
                f,
                "the term is not the {} side of {:?}",
                match dir {
                    Direction::Forward => "left",
                    Direction::Backward => "right",
                },
                law
            ),
            Error::Ill(e) => write!(f, "the rule does not state an equation: {}", e),
        }
    }
}

impl std::error::Error for Error {}

impl From<crate::term::Error> for Error {
    fn from(e: crate::term::Error) -> Error {
        Error::Ill(e)
    }
}

// ---- the table, as construction -------------------------------------------------

/// The two terms a rule says are equal, built from its payload alone.
///
/// This is the table. It reads no term it was not handed, tests nothing, and
/// decides nothing — every arity condition a law carries is enforced by the
/// checked constructors, so a payload that does not state an equation comes
/// back as [`Error::Ill`] rather than as a silently wrong pair.
pub fn sides(ctx: &mut Context, rule: &Rule) -> Result<(TermIndex, TermIndex), Error> {
    Ok(match *rule {
        Rule::AssocCompose { a, b, c } => {
            let ab = ctx.compose(a, b)?;
            let bc = ctx.compose(b, c)?;
            (ctx.compose(ab, c)?, ctx.compose(a, bc)?)
        }
        Rule::UnitLeft { a } => {
            let unit = ctx.id(ctx.arity(a).inputs);
            (ctx.compose(unit, a)?, a)
        }
        Rule::UnitRight { a } => {
            let unit = ctx.id(ctx.arity(a).outputs);
            (ctx.compose(a, unit)?, a)
        }
        Rule::AssocPar { a, b, c } => {
            let ab = ctx.par(a, b);
            let bc = ctx.par(b, c);
            (ctx.par(ab, c), ctx.par(a, bc))
        }
        Rule::UnitParLeft { a } => {
            let unit = ctx.id(0);
            (ctx.par(unit, a), a)
        }
        Rule::UnitParRight { a } => {
            let unit = ctx.id(0);
            (ctx.par(a, unit), a)
        }
        Rule::IdFuse { n, m } => {
            let (l, r) = (ctx.id(n), ctx.id(m));
            (ctx.par(l, r), ctx.id(n + m))
        }
        Rule::Interchange { a, b, c, d } => {
            let ac = ctx.compose(a, c)?;
            let bd = ctx.compose(b, d)?;
            let ab = ctx.par(a, b);
            let cd = ctx.par(c, d);
            (ctx.par(ac, bd), ctx.compose(ab, cd)?)
        }
        Rule::SwapInvol => {
            let (l, r) = (ctx.op(Prim::Swap), ctx.op(Prim::Swap));
            (ctx.compose(l, r)?, ctx.id(2))
        }
        Rule::SwapNat { g } => {
            let one = ctx.id(1);
            let framed = ctx.par(g, one);
            let swap = ctx.op(Prim::Swap);
            let lhs = ctx.compose(framed, swap)?;
            let swap = ctx.op(Prim::Swap);
            let one = ctx.id(1);
            let framed = ctx.par(one, g);
            (lhs, ctx.compose(swap, framed)?)
        }
        Rule::YangBaxter => (braid(ctx, true)?, braid(ctx, false)?),
        Rule::CopyAssoc => {
            let copy = ctx.copy(1);
            let (l, r) = (ctx.copy(1), ctx.id(1));
            let framed = ctx.par(l, r);
            let lhs = ctx.compose(copy, framed)?;
            let copy = ctx.copy(1);
            let (l, r) = (ctx.id(1), ctx.copy(1));
            let framed = ctx.par(l, r);
            (lhs, ctx.compose(copy, framed)?)
        }
        Rule::CopyComm => {
            let copy = ctx.copy(1);
            let swap = ctx.op(Prim::Swap);
            (ctx.compose(copy, swap)?, ctx.copy(1))
        }
        Rule::CopyCounit => {
            let copy = ctx.copy(1);
            let (one, gone) = (ctx.id(1), ctx.drop(1));
            let framed = ctx.par(one, gone);
            (ctx.compose(copy, framed)?, ctx.id(1))
        }
        Rule::CopyNat { g } => {
            let Arity { inputs, outputs } = ctx.arity(g);
            let copy = ctx.copy(outputs);
            let lhs = ctx.compose(g, copy)?;
            let copy = ctx.copy(inputs);
            let twice = ctx.par(g, g);
            (lhs, ctx.compose(copy, twice)?)
        }
        Rule::DropNat { g } => {
            let Arity { inputs, outputs } = ctx.arity(g);
            let gone = ctx.drop(outputs);
            (ctx.compose(g, gone)?, ctx.drop(inputs))
        }
        Rule::DropSplit { n, m } => {
            let whole = ctx.drop(n + m);
            let (l, r) = (ctx.drop(n), ctx.drop(m));
            (whole, ctx.par(l, r))
        }
        Rule::CopyZero => (ctx.copy(0), ctx.id(0)),
        Rule::DropZero => (ctx.drop(0), ctx.id(0)),
        Rule::NotNot => {
            let (l, r) = (ctx.op(Prim::Not), ctx.op(Prim::Not));
            (ctx.compose(l, r)?, ctx.op(Prim::AsBool))
        }
    })
}

// ---- replaying a derivation -----------------------------------------------------

/// Every step applied in order. This is the checker: it reads the [`Rule`]
/// table and the term language, and nothing else.
pub fn replay(ctx: &mut Context, start: TermIndex, steps: &[Step]) -> Result<TermIndex, Error> {
    let mut here = start;
    for step in steps {
        here = apply(ctx, here, step)?;
    }
    Ok(here)
}

/// One step: down to the path, swap one side of the equation for the other,
/// and rebuild the spine on the way out — through the *checked* constructors,
/// so a rewrite that breaks an arity says so at the node where it broke.
pub fn apply(ctx: &mut Context, term: TermIndex, step: &Step) -> Result<TermIndex, Error> {
    descend(ctx, term, &step.path, 0, &step.rule, step.dir)
}

/// The whole of what checking a step comes to: build both sides, see that
/// the term is the one the step claims, hand back the other.
fn swap_sides(
    ctx: &mut Context,
    focus: TermIndex,
    rule: &Rule,
    dir: Direction,
) -> Result<TermIndex, Error> {
    let (lhs, rhs) = sides(ctx, rule)?;
    let (want, give) = match dir {
        Direction::Forward => (lhs, rhs),
        Direction::Backward => (rhs, lhs),
    };
    if ctx.equal(focus, want) {
        Ok(give)
    } else {
        Err(Error::NotThere {
            law: rule.law(),
            dir,
        })
    }
}

fn descend(
    ctx: &mut Context,
    term: TermIndex,
    path: &[Leg],
    depth: usize,
    rule: &Rule,
    dir: Direction,
) -> Result<TermIndex, Error> {
    let Some((leg, rest)) = path.split_first() else {
        return swap_sides(ctx, term, rule, dir);
    };
    let node = ctx.get(term).clone();
    match (leg, node) {
        (Leg::ComposeLeft, Term::Compose(l, r)) => {
            let l = descend(ctx, l, rest, depth + 1, rule, dir)?;
            Ok(ctx.compose(l, r)?)
        }
        (Leg::ComposeRight, Term::Compose(l, r)) => {
            let r = descend(ctx, r, rest, depth + 1, rule, dir)?;
            Ok(ctx.compose(l, r)?)
        }
        (Leg::ParLeft, Term::Par(l, r)) => {
            let l = descend(ctx, l, rest, depth + 1, rule, dir)?;
            Ok(ctx.par(l, r))
        }
        (Leg::ParRight, Term::Par(l, r)) => {
            let r = descend(ctx, r, rest, depth + 1, rule, dir)?;
            Ok(ctx.par(l, r))
        }
        (Leg::BranchTrue, Term::Branch { if_true, if_false }) => {
            let if_true = descend(ctx, if_true, rest, depth + 1, rule, dir)?;
            Ok(ctx.branch(if_true, if_false)?)
        }
        (Leg::BranchFalse, Term::Branch { if_true, if_false }) => {
            let if_false = descend(ctx, if_false, rest, depth + 1, rule, dir)?;
            Ok(ctx.branch(if_true, if_false)?)
        }
        (leg, _) => Err(Error::NoSuchLeg {
            at: depth,
            leg: *leg,
        }),
    }
}

/// The subterm a path names.
pub fn at(ctx: &Context, term: TermIndex, path: &[Leg]) -> Result<TermIndex, Error> {
    let mut here = term;
    for (depth, leg) in path.iter().enumerate() {
        let astray = || Error::NoSuchLeg {
            at: depth,
            leg: *leg,
        };
        here = match (leg, ctx.get(here)) {
            (Leg::ComposeLeft, Term::Compose(l, _)) => *l,
            (Leg::ComposeRight, Term::Compose(_, r)) => *r,
            (Leg::ParLeft, Term::Par(l, _)) => *l,
            (Leg::ParRight, Term::Par(_, r)) => *r,
            (Leg::BranchTrue, Term::Branch { if_true, .. }) => *if_true,
            (Leg::BranchFalse, Term::Branch { if_false, .. }) => *if_false,
            _ => return Err(astray()),
        };
    }
    Ok(here)
}

// ---- reading a rule off a term --------------------------------------------------

/// The rule that applies `law` to this term in this direction, if one does.
///
/// This is the half that is *not* the checker. Everything it does — taking a
/// term apart, checking a width, seeing that two halves agree — happens here,
/// outside the trusted base, and every answer it gives is checked by
/// [`apply`] anyway. A matcher that is wrong makes a derivation that fails to
/// replay, not one that proves something false.
///
/// Three directions return `None` for every term, because the side they
/// would have to match does not record what the other side spends: `IdFuse`
/// backward is not told where to split a block, `DropSplit` forward the same,
/// and `DropNat` backward cannot say what work vanished — that law is what
/// makes work vanish. Those payloads have to be chosen, which is the
/// business of whatever is writing the derivation.
pub fn read(ctx: &mut Context, focus: TermIndex, law: Law, dir: Direction) -> Option<Rule> {
    use Direction::{Backward, Forward};
    let rule = match (law, dir) {
        (Law::AssocCompose, Forward) => {
            let (ab, c) = compose_of(ctx, focus)?;
            let (a, b) = compose_of(ctx, ab)?;
            Rule::AssocCompose { a, b, c }
        }
        (Law::AssocCompose, Backward) => {
            let (a, bc) = compose_of(ctx, focus)?;
            let (b, c) = compose_of(ctx, bc)?;
            Rule::AssocCompose { a, b, c }
        }
        (Law::UnitLeft, Forward) => {
            let (unit, a) = compose_of(ctx, focus)?;
            id_of(ctx, unit).filter(|&n| n == ctx.arity(a).inputs)?;
            Rule::UnitLeft { a }
        }
        (Law::UnitLeft, Backward) => Rule::UnitLeft { a: focus },
        (Law::UnitRight, Forward) => {
            let (a, unit) = compose_of(ctx, focus)?;
            id_of(ctx, unit).filter(|&m| m == ctx.arity(a).outputs)?;
            Rule::UnitRight { a }
        }
        (Law::UnitRight, Backward) => Rule::UnitRight { a: focus },
        (Law::AssocPar, Forward) => {
            let (ab, c) = par_of(ctx, focus)?;
            let (a, b) = par_of(ctx, ab)?;
            Rule::AssocPar { a, b, c }
        }
        (Law::AssocPar, Backward) => {
            let (a, bc) = par_of(ctx, focus)?;
            let (b, c) = par_of(ctx, bc)?;
            Rule::AssocPar { a, b, c }
        }
        (Law::UnitParLeft, Forward) => {
            let (unit, a) = par_of(ctx, focus)?;
            id_of(ctx, unit).filter(|&n| n == 0)?;
            Rule::UnitParLeft { a }
        }
        (Law::UnitParLeft, Backward) => Rule::UnitParLeft { a: focus },
        (Law::UnitParRight, Forward) => {
            let (a, unit) = par_of(ctx, focus)?;
            id_of(ctx, unit).filter(|&n| n == 0)?;
            Rule::UnitParRight { a }
        }
        (Law::UnitParRight, Backward) => Rule::UnitParRight { a: focus },
        (Law::IdFuse, Forward) => {
            let (l, r) = par_of(ctx, focus)?;
            Rule::IdFuse {
                n: id_of(ctx, l)?,
                m: id_of(ctx, r)?,
            }
        }
        (Law::Interchange, Forward) => {
            let (ac, bd) = par_of(ctx, focus)?;
            let (a, c) = compose_of(ctx, ac)?;
            let (b, d) = compose_of(ctx, bd)?;
            Rule::Interchange { a, b, c, d }
        }
        (Law::Interchange, Backward) => {
            let (ab, cd) = compose_of(ctx, focus)?;
            let (a, b) = par_of(ctx, ab)?;
            let (c, d) = par_of(ctx, cd)?;
            Rule::Interchange { a, b, c, d }
        }
        (Law::SwapNat, Forward) => {
            let (framed, swap) = compose_of(ctx, focus)?;
            is_prim(ctx, swap, &Prim::Swap).then_some(())?;
            let (g, one) = par_of(ctx, framed)?;
            id_of(ctx, one).filter(|&n| n == 1)?;
            Rule::SwapNat { g }
        }
        (Law::SwapNat, Backward) => {
            let (swap, framed) = compose_of(ctx, focus)?;
            is_prim(ctx, swap, &Prim::Swap).then_some(())?;
            let (one, g) = par_of(ctx, framed)?;
            id_of(ctx, one).filter(|&n| n == 1)?;
            Rule::SwapNat { g }
        }
        (Law::CopyNat, Forward) => {
            let (g, copy) = compose_of(ctx, focus)?;
            copy_of(ctx, copy).filter(|&l| l == ctx.arity(g).outputs)?;
            Rule::CopyNat { g }
        }
        (Law::CopyNat, Backward) => {
            let (copy, twice) = compose_of(ctx, focus)?;
            let (g, again) = par_of(ctx, twice)?;
            ctx.equal(g, again).then_some(())?;
            copy_of(ctx, copy).filter(|&k| k == ctx.arity(g).inputs)?;
            Rule::CopyNat { g }
        }
        (Law::DropNat, Forward) => {
            let (g, gone) = compose_of(ctx, focus)?;
            drop_of(ctx, gone).filter(|&l| l == ctx.arity(g).outputs)?;
            Rule::DropNat { g }
        }
        (Law::DropSplit, Backward) => {
            let (l, r) = par_of(ctx, focus)?;
            Rule::DropSplit {
                n: drop_of(ctx, l)?,
                m: drop_of(ctx, r)?,
            }
        }
        // The payload-free laws have nothing to read; whether they apply is
        // the same question `apply` asks, so ask it.
        (Law::SwapInvol, _) => Rule::SwapInvol,
        (Law::YangBaxter, _) => Rule::YangBaxter,
        (Law::CopyAssoc, _) => Rule::CopyAssoc,
        (Law::CopyComm, _) => Rule::CopyComm,
        (Law::CopyCounit, _) => Rule::CopyCounit,
        (Law::CopyZero, _) => Rule::CopyZero,
        (Law::DropZero, _) => Rule::DropZero,
        (Law::NotNot, _) => Rule::NotNot,
        // The three that invent rather than read.
        (Law::IdFuse, Backward) | (Law::DropSplit, Forward) | (Law::DropNat, Backward) => {
            return None;
        }
    };
    // A matcher's answer is a proposal. Hold it to the same test the checker
    // will apply, so a `read` that succeeds is an `apply` that succeeds.
    let (lhs, rhs) = sides(ctx, &rule).ok()?;
    let want = match dir {
        Forward => lhs,
        Backward => rhs,
    };
    ctx.equal(focus, want).then_some(rule)
}

// ---- taking a term apart, for the matchers only ---------------------------------

pub(crate) fn compose_of(ctx: &Context, t: TermIndex) -> Option<(TermIndex, TermIndex)> {
    match ctx.get(t) {
        Term::Compose(l, r) => Some((*l, *r)),
        _ => None,
    }
}

pub(crate) fn par_of(ctx: &Context, t: TermIndex) -> Option<(TermIndex, TermIndex)> {
    match ctx.get(t) {
        Term::Par(l, r) => Some((*l, *r)),
        _ => None,
    }
}

pub(crate) fn id_of(ctx: &Context, t: TermIndex) -> Option<usize> {
    match ctx.get(t) {
        Term::Id(n) => Some(*n),
        _ => None,
    }
}

fn drop_of(ctx: &Context, t: TermIndex) -> Option<usize> {
    match ctx.get(t) {
        Term::Drop(n) => Some(*n),
        _ => None,
    }
}

fn copy_of(ctx: &Context, t: TermIndex) -> Option<usize> {
    match ctx.get(t) {
        Term::Copy(n) => Some(*n),
        _ => None,
    }
}

fn is_prim(ctx: &Context, t: TermIndex, prim: &Prim) -> bool {
    matches!(ctx.get(t), Term::Op(p) if p == prim)
}

/// `swap * id(1)`, the deep crossing of a braid triple.
fn deep_cross(ctx: &mut Context) -> TermIndex {
    let swap = ctx.op(Prim::Swap);
    let one = ctx.id(1);
    ctx.par(swap, one)
}

/// `id(1) * swap`, the top crossing of a braid triple.
fn top_cross(ctx: &mut Context) -> TermIndex {
    let one = ctx.id(1);
    let swap = ctx.op(Prim::Swap);
    ctx.par(one, swap)
}

/// One side of the braid relation, left-nested.
fn braid(ctx: &mut Context, deep_first: bool) -> Result<TermIndex, Error> {
    let (x, y) = if deep_first {
        (deep_cross(ctx), top_cross(ctx))
    } else {
        (top_cross(ctx), deep_cross(ctx))
    };
    let z = if deep_first {
        deep_cross(ctx)
    } else {
        top_cross(ctx)
    };
    let xy = ctx.compose(x, y)?;
    Ok(ctx.compose(xy, z)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram::{Ctx, normalize};
    use bytecode::Value;

    fn not(ctx: &mut Context) -> TermIndex {
        ctx.op(Prim::Not)
    }

    fn minus(ctx: &mut Context) -> TermIndex {
        ctx.op(Prim::Subtract)
    }

    /// The engine's verdict on the two sides of a rule: a law relating two
    /// terms it calls different programs is not a law.
    fn means_the_same(ctx: &Context, lhs: TermIndex, rhs: TermIndex, law: Law) {
        let mut engine = Ctx::default();
        assert_eq!(
            normalize(&mut engine, ctx, lhs),
            normalize(&mut engine, ctx, rhs),
            "{:?} relates {} and {}, which are different programs",
            law,
            ctx.display(lhs),
            ctx.display(rhs)
        );
    }

    /// A law holds. Four claims, and the payload is the only input: the two
    /// sides are *built* from it rather than written out here, so this tests
    /// the table itself and not a second copy of it.
    ///
    /// 1. Both sides have one arity, so no step can change what a term takes
    ///    or leaves.
    /// 2. `diagram` says they are the same program.
    /// 3. The step rewrites each side into the other.
    /// 4. Each side reads back as the rule that built it — the matcher and
    ///    the table agree, in whichever directions the matcher is total.
    fn holds(law: Law, build: impl FnOnce(&mut Context) -> Rule) {
        let mut ctx = Context::new();
        let rule = build(&mut ctx);
        assert_eq!(rule.law(), law, "the builder made the wrong law");

        let (lhs, rhs) = sides(&mut ctx, &rule)
            .unwrap_or_else(|e| panic!("{:?} does not state an equation: {}", law, e));
        assert_eq!(
            ctx.arity(lhs),
            ctx.arity(rhs),
            "{:?} relates terms of different arity",
            law
        );
        means_the_same(&ctx, lhs, rhs, law);

        let forward = apply(&mut ctx, lhs, &Step::here(rule.clone(), Direction::Forward))
            .unwrap_or_else(|e| panic!("{:?} forward: {}", law, e));
        assert!(
            ctx.equal(forward, rhs),
            "{:?} forward gave {}, wanted {}",
            law,
            ctx.display(forward),
            ctx.display(rhs)
        );
        let backward = apply(
            &mut ctx,
            rhs,
            &Step::here(rule.clone(), Direction::Backward),
        )
        .unwrap_or_else(|e| panic!("{:?} backward: {}", law, e));
        assert!(
            ctx.equal(backward, lhs),
            "{:?} backward gave {}, wanted {}",
            law,
            ctx.display(backward),
            ctx.display(lhs)
        );

        for (side, dir) in [(lhs, Direction::Forward), (rhs, Direction::Backward)] {
            if let Some(found) = read(&mut ctx, side, law, dir) {
                assert_eq!(
                    found,
                    rule,
                    "{:?} read {:?} off {}, not the rule that built it",
                    law,
                    dir,
                    ctx.display(side)
                );
            }
        }
    }

    // ---- the skeleton ----

    /// Three distinct one-wire boxes, so a regrouping that also reordered
    /// them would not pass.
    #[test]
    fn compose_associates() {
        holds(Law::AssocCompose, |c| Rule::AssocCompose {
            a: c.op(Prim::Not),
            b: c.op(Prim::Negate),
            c: c.op(Prim::AsInt),
        });
    }

    #[test]
    fn the_units_of_compose_vanish() {
        holds(Law::UnitLeft, |c| Rule::UnitLeft { a: minus(c) });
        holds(Law::UnitRight, |c| Rule::UnitRight { a: minus(c) });
    }

    #[test]
    fn par_associates_and_its_unit_vanishes() {
        holds(Law::AssocPar, |c| Rule::AssocPar {
            a: c.id(1),
            b: c.op(Prim::Not),
            c: c.op(Prim::Subtract),
        });
        holds(Law::UnitParLeft, |c| Rule::UnitParLeft { a: minus(c) });
        holds(Law::UnitParRight, |c| Rule::UnitParRight { a: minus(c) });
    }

    #[test]
    fn id_blocks_fuse() {
        holds(Law::IdFuse, |_| Rule::IdFuse { n: 2, m: 3 });
    }

    /// Every factor a different width, so a mis-cut would not typecheck.
    #[test]
    fn the_interchange_holds() {
        holds(Law::Interchange, |c| Rule::Interchange {
            a: c.op(Prim::Subtract),
            b: c.op(Prim::Not),
            c: c.op(Prim::Not),
            d: c.op(Prim::Negate),
        });
    }

    // ---- symmetry ----

    #[test]
    fn a_crossing_undoes_itself() {
        holds(Law::SwapInvol, |_| Rule::SwapInvol);
    }

    #[test]
    fn a_box_slides_past_a_crossing() {
        holds(Law::SwapNat, |c| Rule::SwapNat { g: not(c) });
    }

    /// The braid relation. `docs/algebra.md` books this as "an instance" —
    /// true of the wiring, where both sides read one permutation. A term
    /// records the crossings, so here it is an axiom: without it `swap ;
    /// swap = id(2)` and the interchange present the infinite dihedral
    /// group rather than the symmetric ones.
    #[test]
    fn yang_baxter_is_an_axiom_in_the_term_language() {
        holds(Law::YangBaxter, |_| Rule::YangBaxter);
    }

    // ---- the comonoid ----

    #[test]
    fn copying_is_coassociative_and_cocommutative() {
        holds(Law::CopyAssoc, |_| Rule::CopyAssoc);
        holds(Law::CopyComm, |_| Rule::CopyComm);
    }

    #[test]
    fn a_copy_that_is_dropped_was_never_made() {
        holds(Law::CopyCounit, |_| Rule::CopyCounit);
    }

    // ---- the cartesian naturalities ----

    #[test]
    fn copying_an_answer_is_running_twice() {
        holds(Law::CopyNat, |c| Rule::CopyNat { g: minus(c) });
        holds(Law::CopyNat, |c| Rule::CopyNat { g: not(c) });
    }

    #[test]
    fn discarded_work_is_no_work() {
        holds(Law::DropNat, |c| Rule::DropNat { g: minus(c) });
    }

    #[test]
    fn drop_blocks_split_and_the_degenerate_blocks_are_nothing() {
        holds(Law::DropSplit, |_| Rule::DropSplit { n: 2, m: 3 });
        holds(Law::CopyZero, |_| Rule::CopyZero);
        holds(Law::DropZero, |_| Rule::DropZero);
    }

    // ---- one law from the value layer ----

    /// `not ; not = as_bool`. The engine of `diagram` does not know this one
    /// — it folds a literal window and nothing else here — so the judge is
    /// the machine, reached the way `diagram` reaches it: fold each side on
    /// a literal and see that the answers agree. `vm` states the law itself,
    /// over every shape of value.
    #[test]
    fn not_twice_is_the_coercion() {
        let mut ctx = Context::new();
        let (l, r) = sides(&mut ctx, &Rule::NotNot).unwrap();

        let forward = apply(&mut ctx, l, &Step::here(Rule::NotNot, Direction::Forward)).unwrap();
        assert!(ctx.equal(forward, r));
        let backward = apply(&mut ctx, r, &Step::here(Rule::NotNot, Direction::Backward)).unwrap();
        assert!(ctx.equal(backward, l));

        for v in [
            Value::Bool(true),
            Value::Bool(false),
            Value::Int(0),
            Value::Int(42),
            Value::unit(),
        ] {
            let push = ctx.op(Prim::Push(v.clone()));
            let long = ctx.compose(push, l).unwrap();
            let short = ctx.compose(push, r).unwrap();
            let mut engine = Ctx::default();
            assert_eq!(
                normalize(&mut engine, &ctx, long),
                normalize(&mut engine, &ctx, short),
                "not ; not disagrees with as_bool on {:?}",
                v
            );
        }
    }

    // ---- the checker does not match ----

    /// The point of the split. A payload states its equation outright, so a
    /// step that names the wrong one is caught by comparing two terms —
    /// there is no destructuring in the checker to go wrong, and no way for
    /// a rule to quietly mean something other than what it says.
    #[test]
    fn a_rule_that_does_not_fit_is_refused_by_comparison() {
        let mut ctx = Context::new();
        let g = minus(&mut ctx);
        let other = not(&mut ctx);
        let (lhs, _) = sides(&mut ctx, &Rule::CopyNat { g }).unwrap();

        // The right law, a well-formed payload, the wrong instance.
        let err = apply(
            &mut ctx,
            lhs,
            &Step::here(Rule::CopyNat { g: other }, Direction::Forward),
        )
        .unwrap_err();
        assert_eq!(
            err,
            Error::NotThere {
                law: Law::CopyNat,
                dir: Direction::Forward
            }
        );

        // A payload that states no equation at all is refused before it is
        // ever compared: `swap-nat` needs a one-wire box, and `subtract` is
        // not one, so neither side composes.
        let err = apply(
            &mut ctx,
            lhs,
            &Step::here(Rule::SwapNat { g }, Direction::Forward),
        )
        .unwrap_err();
        assert!(matches!(err, Error::Ill(_)), "{}", err);
    }

    /// Three directions cannot be read off a term, and they are the three
    /// that would have to invent what the other side spends.
    #[test]
    fn the_matcher_is_partial_in_exactly_three_places() {
        let mut ctx = Context::new();
        let wire = ctx.id(5);
        let gone = ctx.drop(5);

        assert_eq!(read(&mut ctx, wire, Law::IdFuse, Direction::Backward), None);
        assert_eq!(
            read(&mut ctx, gone, Law::DropSplit, Direction::Forward),
            None
        );
        assert_eq!(
            read(&mut ctx, gone, Law::DropNat, Direction::Backward),
            None
        );

        // Their other directions read fine.
        let fused = {
            let (a, b) = (ctx.id(2), ctx.id(3));
            ctx.par(a, b)
        };
        assert_eq!(
            read(&mut ctx, fused, Law::IdFuse, Direction::Forward),
            Some(Rule::IdFuse { n: 2, m: 3 })
        );

        // And a derivation still spends them — it just has to say what it is
        // spending, which is the whole point of the payload.
        let split = apply(
            &mut ctx,
            gone,
            &Step::here(Rule::DropSplit { n: 2, m: 3 }, Direction::Forward),
        )
        .unwrap();
        assert_eq!(format!("{}", ctx.display(split)), "drop(2) * drop(3)");

        let g = minus(&mut ctx);
        let two = ctx.drop(2);
        let back = apply(
            &mut ctx,
            two,
            &Step::here(Rule::DropNat { g }, Direction::Backward),
        )
        .unwrap();
        assert_eq!(format!("{}", ctx.display(back)), "subtract ; drop(1)");
    }

    // ---- paths, replay, and reversal ----

    /// A step built by reading the law off whatever sits at the path — the
    /// way anything writing a derivation does it.
    fn at_path(ctx: &mut Context, term: TermIndex, path: Path, law: Law, dir: Direction) -> Step {
        let focus = at(ctx, term, &path).unwrap();
        let rule = read(ctx, focus, law, dir)
            .unwrap_or_else(|| panic!("{:?} {:?} does not read here", law, dir));
        Step { path, rule, dir }
    }

    #[test]
    fn a_step_lands_where_its_path_says() {
        let mut ctx = Context::new();
        let (a, b) = (ctx.op(Prim::Swap), ctx.op(Prim::Swap));
        let pair = ctx.compose(a, b).unwrap();
        let n = not(&mut ctx);
        let outer = ctx.par(pair, n);

        let step = Step {
            path: vec![Leg::ParLeft],
            rule: Rule::SwapInvol,
            dir: Direction::Forward,
        };
        let out = apply(&mut ctx, outer, &step).unwrap();
        assert_eq!(format!("{}", ctx.display(out)), "id(2) * not");

        // The same rule one leg over has nothing to match.
        let astray = Step {
            path: vec![Leg::ParRight],
            rule: Rule::SwapInvol,
            dir: Direction::Forward,
        };
        assert!(matches!(
            apply(&mut ctx, outer, &astray).unwrap_err(),
            Error::NotThere { .. }
        ));

        // And a leg the term does not have fails as a path, not as a rule.
        let nowhere = Step {
            path: vec![Leg::ComposeLeft],
            rule: Rule::SwapInvol,
            dir: Direction::Forward,
        };
        assert!(matches!(
            apply(&mut ctx, outer, &nowhere).unwrap_err(),
            Error::NoSuchLeg { at: 0, .. }
        ));
    }

    /// The worked example: two spellings of `not * not` that differ by which
    /// side of the frame each box sits on, related by a derivation that goes
    /// through the unframed form. Six steps, no search.
    #[test]
    fn a_frame_swaps_sides_by_interchange() {
        let mut ctx = Context::new();
        let start = {
            let (one, n) = (ctx.id(1), ctx.op(Prim::Not));
            let left = ctx.par(one, n);
            let (n, one) = (ctx.op(Prim::Not), ctx.id(1));
            let right = ctx.par(n, one);
            ctx.compose(left, right).unwrap()
        };
        assert_eq!(
            format!("{}", ctx.display(start)),
            "id(1) * not ; not * id(1)"
        );

        let plan = [
            (vec![], Law::Interchange, Direction::Backward),
            (vec![Leg::ParLeft], Law::UnitLeft, Direction::Forward),
            (vec![Leg::ParRight], Law::UnitRight, Direction::Forward),
            (vec![Leg::ParLeft], Law::UnitRight, Direction::Backward),
            (vec![Leg::ParRight], Law::UnitLeft, Direction::Backward),
            (vec![], Law::Interchange, Direction::Forward),
        ];
        let mut steps = Vec::new();
        let mut here = start;
        for (path, law, dir) in plan {
            let step = at_path(&mut ctx, here, path, law, dir);
            here = apply(&mut ctx, here, &step).unwrap();
            steps.push(step);
        }

        assert_eq!(
            format!("{}", ctx.display(here)),
            "not * id(1) ; id(1) * not"
        );

        // Halfway through, the frames are gone entirely.
        let middle = replay(&mut ctx, start, &steps[..3]).unwrap();
        assert_eq!(format!("{}", ctx.display(middle)), "not * not");

        // Replaying the whole thing reaches the same place.
        let end = replay(&mut ctx, start, &steps).unwrap();
        assert!(ctx.equal(end, here));

        // And the derivation read backwards returns where it started — which
        // is what closes the valley between two terms.
        let home = replay(&mut ctx, end, &reversed(&steps)).unwrap();
        assert!(ctx.equal(home, start), "{}", ctx.display(home));
    }

    /// Every step is meaning-preserving, so replaying one cannot change what
    /// a term computes — held here against the engine at every intermediate
    /// point, not just at the ends.
    #[test]
    fn replay_preserves_meaning_at_every_step() {
        let mut ctx = Context::new();
        let start = {
            let copy = ctx.copy(1);
            let (one, gone) = (ctx.id(1), ctx.drop(1));
            let framed = ctx.par(one, gone);
            let counit = ctx.compose(copy, framed).unwrap();
            let n = ctx.op(Prim::Not);
            ctx.compose(counit, n).unwrap()
        };
        let first = at_path(
            &mut ctx,
            start,
            vec![Leg::ComposeLeft],
            Law::CopyCounit,
            Direction::Forward,
        );
        let after = apply(&mut ctx, start, &first).unwrap();
        let second = at_path(&mut ctx, after, vec![], Law::UnitLeft, Direction::Forward);
        let steps = [first, second];

        let mut engine = Ctx::default();
        let want = normalize(&mut engine, &ctx, start);
        let mut here = start;
        for (i, step) in steps.iter().enumerate() {
            here = apply(&mut ctx, here, step).unwrap();
            assert_eq!(
                normalize(&mut engine, &ctx, here),
                want,
                "step {} changed what the term means",
                i
            );
        }
        assert_eq!(format!("{}", ctx.display(here)), "not");
    }
}
