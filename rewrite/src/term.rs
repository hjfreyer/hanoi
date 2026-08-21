//! A program written as an algebra rather than a list.
//!
//! A [`bytecode::Sentence`] is a `Vec<Instruction>`, and three things it leaves
//! implicit are the three things an equational account of a program cannot
//! afford to leave implicit:
//!
//! - **Composition is a list, not an operator.** There is nothing to state an
//!   associativity law about, and nowhere for a rewrite to sit.
//! - **Composition is untyped.** `A ; B` is well formed even when `A` leaves
//!   fewer values than `B` takes; the shortfall is drawn from whatever the
//!   caller happened to have underneath, and
//!   [`bytecode::arity::check_arities`] tracks that by growing a sentence's
//!   input requirement *retroactively*. Every law about `A ; B` therefore
//!   carries a side condition about the stack around it.
//! - **`dip` is a special form.** It hides one value and runs a callee below
//!   it — a second, ad-hoc way of putting two programs together that no law
//!   about `;` reaches.
//!
//! A [`Term`] has two operators instead, both total and both arity-exact.
//! [`Compose`][Term::Compose] — printed `;` — demands that the halves meet
//! exactly. [`Par`][Term::Par] — printed `*` — cuts the stack by arity and runs
//! both sides on their own piece. The implicit passing-through becomes an
//! explicit `id(n) * A`, and `dip { A }` becomes `A * id(1)`: what was a side
//! condition is now a subterm, so an equation between terms says everything it
//! needs to say without mentioning the stack it runs on.
//!
//! Terms live in a [`Context`] — an arena of nodes that name their children by
//! [`TermIndex`] rather than owning them — so a term is a `usize` to pass
//! around and a repeated subterm is stored once. Everything that builds or
//! reads a term does it through the context that issued it.
//!
//! Nothing here decides whether two terms are equal. This is the model a rule
//! set will be stated over, and it carries no analysis machinery at all.

use std::collections::{HashMap, HashSet};
use std::fmt;

use bytecode::arity::sentence_arity;
use bytecode::{Instruction, Library, SentenceIndex, Value};
use typed_index_collections::TiVec;

/// What a term takes off the stack and leaves on it.
///
/// Both counts are non-negative, which is the difference from
/// [`bytecode::Arity`] and the reason for a second type: a sentence's arity is
/// inferred and reported as a pair of `i64`, while a term's is built up from
/// its parts and cannot go negative at any step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Arity {
    pub inputs: usize,
    pub outputs: usize,
}

impl Arity {
    pub const fn new(inputs: usize, outputs: usize) -> Self {
        Self { inputs, outputs }
    }

    /// How much deeper the stack is afterwards. Negative if the term eats more
    /// than it leaves.
    pub fn net(&self) -> i64 {
        self.outputs as i64 - self.inputs as i64
    }
}

impl fmt::Display for Arity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.inputs, self.outputs)
    }
}

/// An instruction a term can hold: every [`Instruction`] but the five the model
/// says structurally instead.
///
/// Each exclusion is a thing the algebra already expresses, and keeping both
/// spellings would mean two terms for one function:
///
/// | Instruction | said here as |
/// | --- | --- |
/// | `drop`, `copy` | [`Term::Drop(1)`][Term::Drop], [`Term::Copy(1)`][Term::Copy] |
/// | `jump` | [`Term::Call`] |
/// | `dip` | a [`Par`][Term::Par] against `id(1)` |
/// | `branch` | [`Term::Branch`] |
///
/// A separate enum rather than a validated `Instruction` also gives the rule
/// set somewhere to put facts that are true of the local instructions and of
/// nothing else — [`Instruction::commutative`] and [`Instruction::yields_bool`]
/// are two that already exist — without a call variant coming along that they
/// would have to answer for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prim {
    Push(Value),
    Swap,

    Equal,
    Greater,
    Less,

    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,

    Not,
    Negate,
    And,
    Or,

    Tuple(usize),
    Untuple(usize),

    ConstStringLen,
    ConstStringCharAt,

    IsInt,
    IsBool,
    IsConstString,
    IsSymbol,
    IsTuple,
    TupleLength,

    AsBool,
    AsInt,
    AsTuple(usize),
}

impl Prim {
    /// The instruction as a prim, or `None` for the five the model expresses
    /// structurally.
    ///
    /// The match is **exhaustive on purpose**: a new instruction is a
    /// compilation error here rather than a silent gap, which is the guard
    /// against this enum drifting away from the instruction set it mirrors.
    pub fn from_instruction(inst: &Instruction) -> Option<Self> {
        Some(match inst {
            Instruction::Push(v) => Prim::Push(v.clone()),
            Instruction::Swap => Prim::Swap,
            Instruction::Equal => Prim::Equal,
            Instruction::Greater => Prim::Greater,
            Instruction::Less => Prim::Less,
            Instruction::Add => Prim::Add,
            Instruction::Subtract => Prim::Subtract,
            Instruction::Multiply => Prim::Multiply,
            Instruction::Divide => Prim::Divide,
            Instruction::Modulo => Prim::Modulo,
            Instruction::Not => Prim::Not,
            Instruction::Negate => Prim::Negate,
            Instruction::And => Prim::And,
            Instruction::Or => Prim::Or,
            Instruction::Tuple(n) => Prim::Tuple(*n),
            Instruction::Untuple(n) => Prim::Untuple(*n),
            Instruction::ConstStringLen => Prim::ConstStringLen,
            Instruction::ConstStringCharAt => Prim::ConstStringCharAt,
            Instruction::IsInt => Prim::IsInt,
            Instruction::IsBool => Prim::IsBool,
            Instruction::IsConstString => Prim::IsConstString,
            Instruction::IsSymbol => Prim::IsSymbol,
            Instruction::IsTuple => Prim::IsTuple,
            Instruction::TupleLength => Prim::TupleLength,
            Instruction::AsBool => Prim::AsBool,
            Instruction::AsInt => Prim::AsInt,
            Instruction::AsTuple(n) => Prim::AsTuple(*n),

            // The five with a structural spelling. See the type's docs.
            Instruction::Drop
            | Instruction::Copy
            | Instruction::Jump(_)
            | Instruction::Dip(_)
            | Instruction::Branch(_, _) => return None,
        })
    }

    /// The instruction this stands for.
    pub fn to_instruction(&self) -> Instruction {
        match self {
            Prim::Push(v) => Instruction::Push(v.clone()),
            Prim::Swap => Instruction::Swap,
            Prim::Equal => Instruction::Equal,
            Prim::Greater => Instruction::Greater,
            Prim::Less => Instruction::Less,
            Prim::Add => Instruction::Add,
            Prim::Subtract => Instruction::Subtract,
            Prim::Multiply => Instruction::Multiply,
            Prim::Divide => Instruction::Divide,
            Prim::Modulo => Instruction::Modulo,
            Prim::Not => Instruction::Not,
            Prim::Negate => Instruction::Negate,
            Prim::And => Instruction::And,
            Prim::Or => Instruction::Or,
            Prim::Tuple(n) => Instruction::Tuple(*n),
            Prim::Untuple(n) => Instruction::Untuple(*n),
            Prim::ConstStringLen => Instruction::ConstStringLen,
            Prim::ConstStringCharAt => Instruction::ConstStringCharAt,
            Prim::IsInt => Instruction::IsInt,
            Prim::IsBool => Instruction::IsBool,
            Prim::IsConstString => Instruction::IsConstString,
            Prim::IsSymbol => Instruction::IsSymbol,
            Prim::IsTuple => Instruction::IsTuple,
            Prim::TupleLength => Instruction::TupleLength,
            Prim::AsBool => Instruction::AsBool,
            Prim::AsInt => Instruction::AsInt,
            Prim::AsTuple(n) => Instruction::AsTuple(*n),
        }
    }

    /// What this takes off the stack and leaves on it.
    ///
    /// A second copy of a table that [`bytecode::arity::op_arity`] holds, which is a
    /// hazard rather than a duplication if the two ever disagree — so
    /// `prim_arities_agree_with_the_instruction_set` walks [`Prim::all`] and
    /// holds this to what `op_arity` says.
    pub fn arity(&self) -> Arity {
        match self {
            Prim::Push(_) => Arity::new(0, 1),
            Prim::Swap => Arity::new(2, 2),

            // Everything that reads two values and answers with one. No
            // instruction reports on itself, so an operation off its domain is
            // a slot narrower than it used to be: the junk answer fills the one
            // slot there is.
            Prim::Equal
            | Prim::And
            | Prim::Or
            | Prim::Greater
            | Prim::Less
            | Prim::Add
            | Prim::Subtract
            | Prim::Multiply
            | Prim::Divide
            | Prim::Modulo
            | Prim::ConstStringCharAt => Arity::new(2, 1),

            Prim::Not
            | Prim::Negate
            | Prim::ConstStringLen
            | Prim::TupleLength
            | Prim::IsInt
            | Prim::IsBool
            | Prim::IsConstString
            | Prim::IsSymbol
            | Prim::IsTuple
            | Prim::AsBool
            | Prim::AsInt
            | Prim::AsTuple(_) => Arity::new(1, 1),

            Prim::Tuple(n) => Arity::new(*n, 1),
            Prim::Untuple(n) => Arity::new(1, *n),
        }
    }

    /// One of every variant, for tests that must cover the whole set.
    ///
    /// The parameterized variants get an arbitrary parameter; nothing about an
    /// arity depends on which literal is pushed, and the widths are chosen to
    /// be distinct from each other so a transposed arity shows up.
    pub fn all() -> Vec<Prim> {
        vec![
            Prim::Push(Value::Int(1)),
            Prim::Swap,
            Prim::Equal,
            Prim::Greater,
            Prim::Less,
            Prim::Add,
            Prim::Subtract,
            Prim::Multiply,
            Prim::Divide,
            Prim::Modulo,
            Prim::Not,
            Prim::Negate,
            Prim::And,
            Prim::Or,
            Prim::Tuple(3),
            Prim::Untuple(4),
            Prim::ConstStringLen,
            Prim::ConstStringCharAt,
            Prim::IsInt,
            Prim::IsBool,
            Prim::IsConstString,
            Prim::IsSymbol,
            Prim::IsTuple,
            Prim::TupleLength,
            Prim::AsBool,
            Prim::AsInt,
            Prim::AsTuple(5),
        ]
    }
}

/// Prints the mnemonic the instruction prints, so a term and a trace name the
/// same operation the same way.
impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_instruction())
    }
}

/// Where a term lives in the [`Context`] that built it.
///
/// An index is meaningful only against its own context. Nothing checks that —
/// two contexts' indices are the same `usize` — so a program that has more
/// than one arena in play is responsible for keeping them apart.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermIndex(usize);

impl From<usize> for TermIndex {
    fn from(n: usize) -> Self {
        TermIndex(n)
    }
}

impl From<TermIndex> for usize {
    fn from(idx: TermIndex) -> Self {
        idx.0
    }
}

/// A program, as a node of two operators over a handful of leaves.
///
/// A node names its children by [`TermIndex`] rather than owning them, so a
/// term is only meaningful together with the [`Context`] it was built in; that
/// is where everything you would expect on a tree — [`arity`][Context::arity],
/// [`check`][Context::check], the constructors, the printing — lives.
///
/// The variants are public because a rule set has to match on them. Every way
/// of building one either preserves the arities it was given or is rejected,
/// and the constructors are where that is enforced.
///
/// **The constructors check, they do not normalize.** `ctx.par(zero, a)` where
/// `zero` is `id(0)` builds exactly `Par(Id(0), a)`, and `ctx.drop(0)` stays
/// `Drop(0)` rather than becoming `Id(0)`. The unit laws are among the first
/// things a rule set will want to state, and a constructor that quietly applied
/// them would be deciding equalities that the prover is supposed to derive.
/// [`lower`] avoids emitting units in the first place, which is a different
/// thing: it declines to build them, rather than building and then discarding
/// them.
///
/// Deriving `PartialEq` compares one node against another, which for a node
/// with children compares *where its children sit* rather than what they are:
/// two separately built spellings of one term are unequal as nodes. Structural
/// equality is [`Context::equal`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// `id(n)`: `n` values in, the same `n` out.
    Id(usize),
    /// `drop(n)`: `n` values in, nothing out.
    Drop(usize),
    /// `copy(n)`: `n` values in, those `n` twice over. Block-wise, so
    /// `copy(2)` takes `[a, b]` to `[a, b, a, b]` — not `[a, a, b, b]`.
    Copy(usize),
    /// One instruction, applied to the top of the stack.
    Op(Prim),
    /// A sentence called by name, left unopened.
    ///
    /// The arity is carried rather than looked up, so a term's arity needs no
    /// [`Library`] and a term stays meaningful on its own. It is the callee's
    /// *inferred* arity, which is what the machine consumes; a wider
    /// `#[arity]` annotation is a claim about the sentence, not about what a
    /// call to it does.
    Call { target: SentenceIndex, arity: Arity },
    /// `A ; B`: everything `A` leaves, `B` takes. Requires `A.outputs ==
    /// B.inputs`, which is the whole point — see [`Context::pad_compose`] for
    /// how a sentence's implicit padding is made explicit to get there.
    Compose(TermIndex, TermIndex),
    /// `A * B`: the stack is cut by arity and both sides run on their own
    /// piece.
    ///
    /// **The second argument gets the top.** `B` takes the topmost
    /// `B.inputs` values and `A` takes the `A.inputs` below them, which is
    /// forced by `dip N { X }` being `X * id(N)`: `dip` hides the top of the
    /// stack, so the identity is the one on top. Padding therefore always
    /// reads `id(k) * A`, with the untouched values underneath.
    Par(TermIndex, TermIndex),
    /// The condition on top, then whichever arm it selects.
    ///
    /// The arms are held to the same arity, so the branch has one: with arms
    /// `n -> m` the branch is `n + 1 -> m`, the extra input being the
    /// condition. That is what the machine does — it pops the condition and
    /// enters the arm with the rest of the stack.
    Branch {
        if_true: TermIndex,
        if_false: TermIndex,
    },
}

/// The arena terms are built in and read out of.
///
/// A context is a [`TiVec`] of nodes that point at each other by
/// [`TermIndex`], which buys two things a tree of `Box`es does not:
///
/// - **Sharing costs an index.** The compiler gives every `pick 2` in a
///   program one compiled block; [`lower`] hands each of them that block's
///   index rather than a copy of it. Nothing downstream has to know: a shared
///   subterm reads exactly like a copied one.
/// - **A term is `Copy`.** Handing one to a goal, keeping a list of the parts
///   of a spine, or rebuilding a term around a rewritten piece moves `usize`s
///   around rather than cloning subtrees.
///
/// Nodes are only ever appended, so an index stays valid for the life of the
/// context and every child was built before its parent. That ordering is what
/// lets each node's arity be worked out once, as it is pushed, and read back
/// in constant time afterwards.
#[derive(Debug, Clone, Default)]
pub struct Context {
    terms: TiVec<TermIndex, Term>,
    /// One arity per term, at the same index: worked out from the children's,
    /// which are already in hand when a node is pushed.
    arities: TiVec<TermIndex, Arity>,
}

impl Context {
    pub fn new() -> Self {
        Context::default()
    }

    /// How many nodes have been built.
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// The node at an index.
    pub fn get(&self, idx: TermIndex) -> &Term {
        &self.terms[idx]
    }

    /// Adds a node built by hand, with its children already in this context.
    ///
    /// Unchecked, exactly as the variants are: this is what anything that takes
    /// a term apart and puts it back together uses, and [`Context::check`] is
    /// how such a thing says it did so honestly. Prefer the constructors, which
    /// refuse what they cannot build.
    pub fn push(&mut self, term: Term) -> TermIndex {
        let arity = self.arity_of(&term);
        self.arities.push(arity);
        self.terms.push_and_get_key(term)
    }

    /// A node's arity, from its own shape and its children's arities.
    fn arity_of(&self, term: &Term) -> Arity {
        match term {
            Term::Id(n) => Arity::new(*n, *n),
            Term::Drop(n) => Arity::new(*n, 0),
            Term::Copy(n) => Arity::new(*n, 2 * n),
            Term::Op(prim) => prim.arity(),
            Term::Call { arity, .. } => *arity,
            Term::Compose(left, right) => {
                Arity::new(self.arity(*left).inputs, self.arity(*right).outputs)
            }
            Term::Par(left, right) => {
                let (l, r) = (self.arity(*left), self.arity(*right));
                Arity::new(l.inputs + r.inputs, l.outputs + r.outputs)
            }
            Term::Branch { if_true, .. } => {
                let arm = self.arity(*if_true);
                Arity::new(arm.inputs + 1, arm.outputs)
            }
        }
    }

    // ---- leaves ----

    pub fn id(&mut self, n: usize) -> TermIndex {
        self.push(Term::Id(n))
    }

    pub fn drop(&mut self, n: usize) -> TermIndex {
        self.push(Term::Drop(n))
    }

    pub fn copy(&mut self, n: usize) -> TermIndex {
        self.push(Term::Copy(n))
    }

    pub fn op(&mut self, prim: Prim) -> TermIndex {
        self.push(Term::Op(prim))
    }

    pub fn call(&mut self, target: SentenceIndex, arity: Arity) -> TermIndex {
        self.push(Term::Call { target, arity })
    }

    // ---- operators ----

    /// `left ; right`, which exists only when the halves meet exactly.
    pub fn compose(&mut self, left: TermIndex, right: TermIndex) -> Result<TermIndex, Error> {
        let (l, r) = (self.arity(left), self.arity(right));
        if l.outputs != r.inputs {
            return Err(Error::Mismatch { left: l, right: r });
        }
        Ok(self.push(Term::Compose(left, right)))
    }

    /// `left * right`. Total: any two terms can run side by side.
    pub fn par(&mut self, left: TermIndex, right: TermIndex) -> TermIndex {
        self.push(Term::Par(left, right))
    }

    /// A branch on two arms of the same arity.
    pub fn branch(&mut self, if_true: TermIndex, if_false: TermIndex) -> Result<TermIndex, Error> {
        let (t, f) = (self.arity(if_true), self.arity(if_false));
        if t != f {
            return Err(Error::ArmsDiffer {
                if_true: t,
                if_false: f,
            });
        }
        Ok(self.push(Term::Branch { if_true, if_false }))
    }

    // ---- padding ----

    /// The same term with `n` more values passing underneath, untouched.
    ///
    /// `n == 0` is the term itself rather than `id(0) * A`: there is nothing to
    /// pass through, and building the unit only to have a rule remove it again
    /// helps nobody.
    pub fn under(&mut self, term: TermIndex, n: usize) -> TermIndex {
        if n == 0 {
            term
        } else {
            let id = self.id(n);
            self.par(id, term)
        }
    }

    /// `left ; right`, widening whichever side is narrower so that they meet.
    ///
    /// This is where a sentence's implicit stack passing becomes explicit, and
    /// it is total for the same reason the implicit version always worked: if
    /// `left` leaves too few values, the missing ones were going to come from
    /// underneath, so `id(k) * left` says so; if it leaves too many, the extra
    /// ones were going to sit untouched beneath `right`, so `id(k) * right`
    /// says that.
    ///
    /// Widening `left` deepens the whole prefix, which is exactly what
    /// [`bytecode::arity::check_arities`] does when a later instruction turns
    /// out to want more than the sentence has asked for so far.
    pub fn pad_compose(&mut self, left: TermIndex, right: TermIndex) -> TermIndex {
        let (l, r) = (self.arity(left).outputs, self.arity(right).inputs);
        let (left, right) = if l < r {
            (self.under(left, r - l), right)
        } else {
            (left, self.under(right, l - r))
        };
        self.compose(left, right)
            .expect("padding is what makes the halves meet")
    }

    /// A branch on two arms padded to a common arity.
    ///
    /// Only the *net* change has to agree; the arms may ask for different
    /// depths, and the shallower one is widened to the deeper one's demand.
    /// That is the same rule the arity checker applies — a branch requires
    /// whatever the hungrier arm requires — and an arm that passes a value
    /// through where the other consumes one is a real program, not a mistake.
    ///
    /// Arms whose nets differ are refused: no amount of padding can bring them
    /// together, since padding adds the same amount to both sides of an arity.
    pub fn pad_branch(
        &mut self,
        if_true: TermIndex,
        if_false: TermIndex,
    ) -> Result<TermIndex, Error> {
        let (t, f) = (self.arity(if_true), self.arity(if_false));
        if t.net() != f.net() {
            return Err(Error::ArmsDiffer {
                if_true: t,
                if_false: f,
            });
        }
        let (if_true, if_false) = if t.inputs < f.inputs {
            (self.under(if_true, f.inputs - t.inputs), if_false)
        } else {
            (if_true, self.under(if_false, t.inputs - f.inputs))
        };
        self.branch(if_true, if_false)
    }

    // ---- reading a term ----

    /// What this takes off the stack and leaves on it.
    ///
    /// Constant time: a node's arity was worked out when it was pushed, from
    /// children that were already there. [`Term::Call`] is the one that could
    /// not have been worked out locally at all, which is why it carries its
    /// own.
    pub fn arity(&self, idx: TermIndex) -> Arity {
        self.arities[idx]
    }

    /// Whether the two terms are the same program written the same way.
    ///
    /// Structural, since two contexts' — or one context's — separately built
    /// spellings of one term sit at different indices. Identical indices are
    /// the same term and answer immediately, which is what makes this cheap on
    /// the shared subterms an arena is full of.
    pub fn equal(&self, a: TermIndex, b: TermIndex) -> bool {
        if a == b {
            return true;
        }
        match (self.get(a), self.get(b)) {
            (Term::Compose(a1, a2), Term::Compose(b1, b2))
            | (Term::Par(a1, a2), Term::Par(b1, b2)) => {
                self.equal(*a1, *b1) && self.equal(*a2, *b2)
            }
            (
                Term::Branch {
                    if_true: t1,
                    if_false: f1,
                },
                Term::Branch {
                    if_true: t2,
                    if_false: f2,
                },
            ) => self.equal(*t1, *t2) && self.equal(*f1, *f2),
            (x, y) => x == y,
        }
    }

    /// Whether every node in the term obeys the invariants its constructor
    /// enforces.
    ///
    /// Nothing needs this when a term was built through the constructors, which
    /// is the point of them. It is here for tests, and for anything that builds
    /// a term by taking one apart and putting it back together with
    /// [`push`][Context::push].
    pub fn check(&self, idx: TermIndex) -> Result<(), Error> {
        // A subterm that is shared is a subterm already checked: an arena is a
        // graph, and walking it as a tree would pay for the sharing twice.
        // A worklist rather than the recursion this reads like: a term is as
        // deep as it is long, and a `;` chain of a few thousand steps — which
        // is what reading a whole graph back leaves — is enough to overflow a
        // thread's stack in an unoptimised build.
        let mut seen = HashSet::new();
        let mut work = vec![idx];
        while let Some(idx) = work.pop() {
            if !seen.insert(idx) {
                continue;
            }
            match self.get(idx) {
                Term::Id(_) | Term::Drop(_) | Term::Copy(_) | Term::Op(_) | Term::Call { .. } => {}
                Term::Compose(left, right) => {
                    let (l, r) = (self.arity(*left), self.arity(*right));
                    if l.outputs != r.inputs {
                        return Err(Error::Mismatch { left: l, right: r });
                    }
                    work.push(*left);
                    work.push(*right);
                }
                Term::Par(left, right) => {
                    work.push(*left);
                    work.push(*right);
                }
                Term::Branch { if_true, if_false } => {
                    let (t, f) = (self.arity(*if_true), self.arity(*if_false));
                    if t != f {
                        return Err(Error::ArmsDiffer {
                            if_true: t,
                            if_false: f,
                        });
                    }
                    work.push(*if_true);
                    work.push(*if_false);
                }
            }
        }
        Ok(())
    }
}
/// How tightly a term's spelling binds, for deciding where parentheses go.
///
/// `*` binds tighter than `;`, the usual convention for a tensor against a
/// composition, which leaves the shape that lowering produces most often —
/// `A ; id(k) * B ; C` — free of parentheses entirely.
const PREC_COMPOSE: u8 = 1;
const PREC_PAR: u8 = 2;
const PREC_ATOM: u8 = 3;

/// A term printed on one line, through the context that holds it.
///
/// What [`Display`](fmt::Display) used to be on an owning tree: a node names
/// its children by index, so printing needs the arena and a term cannot print
/// itself.
pub struct Show<'c> {
    ctx: &'c Context,
    term: TermIndex,
    names: Names<'c>,
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.write(f, self.term, 0, self.names)
    }
}

impl<'c> Show<'c> {
    /// The same spelling, with calls printed by the name the library keys them
    /// under rather than by index.
    pub fn named(self, library: &'c Library) -> Self {
        Show {
            names: Names(Some(&library.names)),
            ..self
        }
    }
}

/// A term laid out over as many lines as it needs: a composition one factor
/// per line, a branch's arms indented inside their braces, and anything that
/// still fits in the width left exactly as [`Show`] writes it.
///
/// Same spelling, different line breaks — the parentheses are the ones `Show`
/// puts in, so the printed form still says which tree it came from. A residual
/// is the deliverable of a failed run and is read by a human; everything that
/// goes on one line of a report (a proof summary, a `solve`'s fills) keeps
/// using `Show`.
pub struct Pretty<'c> {
    ctx: &'c Context,
    term: TermIndex,
    width: usize,
    names: Names<'c>,
}

impl fmt::Display for Pretty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.lay(f, self.term, 0, 0, self.width, self.names)
    }
}

impl<'c> Pretty<'c> {
    /// The same layout, with calls printed by the name the library keys them
    /// under rather than by index.
    pub fn named(self, library: &'c Library) -> Self {
        Pretty {
            names: Names(Some(&library.names)),
            ..self
        }
    }
}

/// Where a printed call gets its name, when it has one to get.
///
/// A [`Term`] carries an index rather than a name, so printing can only write
/// `call #3`. Anything printed for a human to *answer* — a residual, whose
/// answer is a `via` waypoint naming the same sentence — is printed with the
/// library at hand instead, and says `call types_test::number`.
#[derive(Copy, Clone, Default)]
struct Names<'l>(Option<&'l TiVec<SentenceIndex, String>>);

impl Names<'_> {
    fn of(&self, idx: SentenceIndex) -> Option<&str> {
        self.0?.get(idx).map(String::as_str)
    }
}

impl Context {
    /// This term on one line. See [`Show`].
    pub fn display(&self, term: TermIndex) -> Show<'_> {
        Show {
            ctx: self,
            term,
            names: Names::default(),
        }
    }

    /// This term laid out to read in `width` columns. See [`Pretty`].
    pub fn pretty(&self, term: TermIndex, width: usize) -> Pretty<'_> {
        Pretty {
            ctx: self,
            term,
            width,
            names: Names::default(),
        }
    }

    fn precedence(&self, term: TermIndex) -> u8 {
        match self.get(term) {
            Term::Compose(_, _) => PREC_COMPOSE,
            Term::Par(_, _) => PREC_PAR,
            _ => PREC_ATOM,
        }
    }

    /// Writes the term, parenthesized if it binds more loosely than the place
    /// it is being written into.
    ///
    /// Both operators print left-associatively: a child on the left is written
    /// at its parent's own precedence, and one on the right a step above it. So
    /// `(a ; b) ; c` prints flat and `a ; (b ; c)` keeps its parentheses, which
    /// is what makes the printed form say which tree it came from.
    fn write(
        &self,
        f: &mut fmt::Formatter<'_>,
        term: TermIndex,
        context: u8,
        names: Names<'_>,
    ) -> fmt::Result {
        if self.precedence(term) < context {
            write!(f, "(")?;
            self.write(f, term, 0, names)?;
            return write!(f, ")");
        }
        match self.get(term) {
            Term::Id(n) => write!(f, "id({})", n),
            Term::Drop(n) => write!(f, "drop({})", n),
            Term::Copy(n) => write!(f, "copy({})", n),
            Term::Op(prim) => write!(f, "{}", prim),
            Term::Call { target, .. } => match names.of(*target) {
                Some(name) => write!(f, "call {}", name),
                None => write!(f, "call #{}", usize::from(*target)),
            },
            Term::Compose(left, right) => {
                self.write(f, *left, PREC_COMPOSE, names)?;
                write!(f, " ; ")?;
                self.write(f, *right, PREC_COMPOSE + 1, names)
            }
            Term::Par(left, right) => {
                self.write(f, *left, PREC_PAR, names)?;
                write!(f, " * ")?;
                self.write(f, *right, PREC_PAR + 1, names)
            }
            Term::Branch { if_true, if_false } => {
                write!(f, "branch {{ ")?;
                self.write(f, *if_true, 0, names)?;
                write!(f, " }} {{ ")?;
                self.write(f, *if_false, 0, names)?;
                write!(f, " }}")
            }
        }
    }

    /// The one-line spelling, when it is short enough to keep.
    fn flat_within(
        &self,
        term: TermIndex,
        context: u8,
        budget: usize,
        names: Names<'_>,
    ) -> Option<String> {
        struct Flat<'c>(&'c Context, TermIndex, u8, Names<'c>);
        impl fmt::Display for Flat<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.write(f, self.1, self.2, self.3)
            }
        }
        let flat = Flat(self, term, context, names).to_string();
        (flat.chars().count() <= budget).then_some(flat)
    }

    /// Writes the term broken over lines, with continuation lines starting at
    /// column `indent` — which the caller has already left the cursor at.
    fn lay(
        &self,
        f: &mut fmt::Formatter<'_>,
        term: TermIndex,
        indent: usize,
        context: u8,
        width: usize,
        names: Names<'_>,
    ) -> fmt::Result {
        // What fits stays put: breaking a short factor helps nobody.
        if let Some(flat) = self.flat_within(term, context, width.saturating_sub(indent), names) {
            return f.write_str(&flat);
        }
        // A group that has to break is a group whose parentheses are worth
        // seeing, and they are where its extra column of indent comes from:
        // the lines inside line up under the paren.
        if self.precedence(term) < context {
            f.write_str("(")?;
            self.lay(f, term, indent + 1, 0, width, names)?;
            return f.write_str(")");
        }
        let newline = |f: &mut fmt::Formatter<'_>, indent: usize| write!(f, "\n{:1$}", "", indent);
        match self.get(term) {
            Term::Compose(left, right) => {
                self.lay(f, *left, indent, PREC_COMPOSE, width, names)?;
                f.write_str(" ;")?;
                newline(f, indent)?;
                self.lay(f, *right, indent, PREC_COMPOSE + 1, width, names)
            }
            Term::Par(left, right) => {
                self.lay(f, *left, indent, PREC_PAR, width, names)?;
                f.write_str(" *")?;
                newline(f, indent)?;
                self.lay(f, *right, indent, PREC_PAR + 1, width, names)
            }
            Term::Branch { if_true, if_false } => {
                f.write_str("branch ")?;
                for (arm, close) in [(if_true, "} "), (if_false, "}")] {
                    f.write_str("{")?;
                    newline(f, indent + 2)?;
                    self.lay(f, *arm, indent + 2, 0, width, names)?;
                    newline(f, indent)?;
                    f.write_str(close)?;
                }
                Ok(())
            }
            // A leaf has no break to make, however long it is.
            _ => self.write(f, term, context, names),
        }
    }
}

/// A term that could not be built, or a sentence that could not be read as one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Two halves of a composition that do not meet.
    Mismatch { left: Arity, right: Arity },
    /// Two branch arms that cannot be brought to a common arity.
    ArmsDiffer { if_true: Arity, if_false: Arity },
    /// A sentence whose stack effect could not be worked out. A library that
    /// compiled has none of these: inference is what refuses recursion, so a
    /// sentence with no arity never got this far.
    NoArity(SentenceIndex),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Mismatch { left, right } => write!(
                f,
                "cannot compose {} with {}: the first leaves {} values and the second takes {}",
                left, right, left.outputs, right.inputs
            ),
            Error::ArmsDiffer { if_true, if_false } => write!(
                f,
                "branch arms {} and {} leave the stack differently ({} against {})",
                if_true,
                if_false,
                if_true.net(),
                if_false.net()
            ),
            Error::NoArity(idx) => write!(f, "sentence {:?} has no stack effect", idx),
        }
    }
}

impl std::error::Error for Error {}

/// The name phase 4 gives a block that was written inline rather than called.
///
/// Both branch arms and `dip { ... }` bodies get a [`SentenceIndex`] only
/// because the compiler needs somewhere to put them, as do the shared
/// expansions of `pick`, `roll` and a deep `drop`. Nothing can reach one by
/// name, so they are spliced into the term rather than becoming calls: a
/// `Call` to one would name a compiler artifact, and every rule that wanted to
/// look inside a dip body would have to open a call first.
const INLINE_BLOCK: &str = "<inline>";

/// The term a sentence stands for, built in `ctx`.
pub fn lower(
    ctx: &mut Context,
    library: &Library,
    sentence: SentenceIndex,
) -> Result<TermIndex, Error> {
    Lowering::new(library).sentence(ctx, sentence)
}

/// Every sentence in the library, lowered into one context, sharing the work
/// between them.
///
/// Inline blocks appear twice over: spliced into whatever wrote them, and again
/// as an entry of their own. A caller normally wants the entries for named
/// sentences, which are the ones anything can reach.
pub fn lower_all(
    ctx: &mut Context,
    library: &Library,
) -> Result<TiVec<SentenceIndex, TermIndex>, Error> {
    let mut lowering = Lowering::new(library);
    let mut terms = TiVec::with_capacity(library.sentences.len());
    for idx in library.sentences.keys() {
        terms.push(lowering.sentence(ctx, idx)?);
    }
    Ok(terms)
}

/// One pass over a library, remembering what it has already worked out.
///
/// The memos are not an optimization of a slow thing but of a repeated one: the
/// compiler shares a single block between every `pick 2` in the program, and a
/// callee's arity is re-derived from scratch by every [`sentence_arity`] call.
/// A block memo is an index, so a block that ten sentences dip into is one
/// subterm ten parents point at rather than ten copies of it.
struct Lowering<'a> {
    library: &'a Library,
    arities: HashMap<SentenceIndex, Arity>,
    blocks: HashMap<SentenceIndex, TermIndex>,
}

impl<'a> Lowering<'a> {
    fn new(library: &'a Library) -> Self {
        Self {
            library,
            arities: HashMap::new(),
            blocks: HashMap::new(),
        }
    }

    /// A sentence's instructions, folded left with padding at each step.
    ///
    /// Left, because that is the order the requirement grows in: when the
    /// prefix built so far leaves less than the next instruction wants, the
    /// whole prefix is widened, which is the same retroactive growth
    /// `infer_arity_of_instructions` performs on a sentence's input count.
    ///
    /// This terminates because recursion is forbidden — `check_arities`
    /// refuses a sentence that reaches itself, so the call graph of a library
    /// that compiled is acyclic and splicing inline blocks bottoms out.
    fn sentence(&mut self, ctx: &mut Context, idx: SentenceIndex) -> Result<TermIndex, Error> {
        // Detached from `self` so the loop can hold it while the body borrows
        // the memos mutably; the library outlives both.
        let library = self.library;
        let mut acc: Option<TermIndex> = None;
        for inst in &library.sentences[idx] {
            let next = self.instruction(ctx, inst)?;
            acc = Some(match acc {
                None => next,
                Some(prefix) => ctx.pad_compose(prefix, next),
            });
        }
        // An empty sentence is the identity on nothing, which is the unit of
        // composition and the honest reading of a program that does nothing.
        Ok(match acc {
            Some(term) => term,
            None => ctx.id(0),
        })
    }

    fn instruction(&mut self, ctx: &mut Context, inst: &Instruction) -> Result<TermIndex, Error> {
        Ok(match inst {
            Instruction::Jump(target) => self.target(ctx, *target)?,
            // The hidden value is the top of the stack, so the identity is the
            // one on the right: `dip { A }` is `A * id(1)`.
            Instruction::Dip(target) => {
                let body = self.target(ctx, *target)?;
                let one = ctx.id(1);
                ctx.par(body, one)
            }
            Instruction::Branch(if_true, if_false) => {
                let if_true = self.target(ctx, *if_true)?;
                let if_false = self.target(ctx, *if_false)?;
                ctx.pad_branch(if_true, if_false)?
            }
            Instruction::Drop => ctx.drop(1),
            Instruction::Copy => ctx.copy(1),
            local => ctx.op(Prim::from_instruction(local)
                .expect("the instructions without a prim are matched above")),
        })
    }

    /// A called sentence: spliced in if it is a block, named if it is not.
    fn target(&mut self, ctx: &mut Context, idx: SentenceIndex) -> Result<TermIndex, Error> {
        if self.library.names[idx] != INLINE_BLOCK {
            let arity = self.arity_of(idx)?;
            return Ok(ctx.call(idx, arity));
        }
        // Splicing a block twice hands out the index built the first time: the
        // arena is what makes sharing the block and copying it the same thing
        // to everything downstream.
        if let Some(term) = self.blocks.get(&idx) {
            return Ok(*term);
        }
        let term = self.sentence(ctx, idx)?;
        self.blocks.insert(idx, term);
        Ok(term)
    }

    fn arity_of(&mut self, idx: SentenceIndex) -> Result<Arity, Error> {
        if let Some(arity) = self.arities.get(&idx) {
            return Ok(*arity);
        }
        let arity = call_arity(self.library, idx)?;
        self.arities.insert(idx, arity);
        Ok(arity)
    }
}

/// What a call to this sentence does to the stack: its *inferred* arity, which
/// is what the machine consumes and what a [`Term::Call`] carries.
pub fn call_arity(library: &Library, idx: SentenceIndex) -> Result<Arity, Error> {
    let inferred = sentence_arity(library, idx).ok_or(Error::NoArity(idx))?;
    Ok(Arity::new(
        usize::try_from(inferred.inputs).expect("an inferred arity counts up from zero"),
        usize::try_from(inferred.outputs).expect("an inferred arity counts up from zero"),
    ))
}
#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::arity::op_arity;
    use bytecode::assemble;

    fn sentence_named(library: &Library, name: &str) -> SentenceIndex {
        library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == name)
            .map(|(idx, _)| idx)
            .unwrap_or_else(|| panic!("no sentence named {}", name))
    }

    /// The term a named sentence lowers to, printed.
    fn lowered(code: &str, name: &str) -> String {
        let library = assemble(code).unwrap();
        let idx = sentence_named(&library, name);
        let mut ctx = Context::new();
        let term = lower(&mut ctx, &library, idx).unwrap();
        ctx.check(term).unwrap();
        format!("{}", ctx.display(term))
    }

    // ---- prims ----

    #[test]
    fn prim_arities_agree_with_the_instruction_set() {
        for prim in Prim::all() {
            let inst = prim.to_instruction();
            let (inputs, outputs) = op_arity(&inst).expect("a prim is a local instruction");
            assert_eq!(
                prim.arity(),
                Arity::new(inputs as usize, outputs as usize),
                "{} disagrees with op_arity",
                prim
            );
        }
    }

    #[test]
    fn every_prim_round_trips_through_its_instruction() {
        for prim in Prim::all() {
            assert_eq!(Prim::from_instruction(&prim.to_instruction()), Some(prim));
        }
    }

    #[test]
    fn the_structural_instructions_have_no_prim() {
        for inst in [
            Instruction::Drop,
            Instruction::Copy,
            Instruction::Jump(SentenceIndex::from(0)),
            Instruction::Dip(SentenceIndex::from(0)),
            Instruction::Branch(SentenceIndex::from(0), SentenceIndex::from(1)),
        ] {
            assert_eq!(Prim::from_instruction(&inst), None, "{}", inst);
        }
    }

    // ---- the arena ----

    #[test]
    fn a_subterm_used_twice_is_stored_once() {
        let mut ctx = Context::new();
        let leaf = ctx.id(1);
        let before = ctx.len();
        let doubled = ctx.par(leaf, leaf);
        // One new node: the par. Both children are the same place.
        assert_eq!(ctx.len(), before + 1);
        assert_eq!(*ctx.get(doubled), Term::Par(leaf, leaf));
        assert_eq!(format!("{}", ctx.display(doubled)), "id(1) * id(1)");
        assert_eq!(ctx.arity(doubled), Arity::new(2, 2));
    }

    #[test]
    fn equality_is_structural_where_node_equality_is_not() {
        let mut ctx = Context::new();
        let (a, b) = (ctx.id(1), ctx.id(1));
        let left = ctx.par(a, b);
        let right = ctx.par(b, a);
        // Two spellings of `id(1) * id(1)` at two places: equal as terms…
        assert!(ctx.equal(left, right));
        assert!(ctx.equal(a, b));
        // …and not as nodes, which compare where their children sit.
        assert_ne!(ctx.get(left), ctx.get(right));
        assert_ne!(left, right);

        let other = ctx.id(2);
        assert!(!ctx.equal(a, other));
    }

    #[test]
    fn a_lowered_library_shares_the_block_the_compiler_shared() {
        // Both `pick 1`s dip into one compiled block, so lowering points both
        // at one subterm rather than building it twice.
        let library = assemble("sentence probe { pick 1 } sentence again { pick 1 }").unwrap();
        let mut ctx = Context::new();
        let terms = lower_all(&mut ctx, &library).unwrap();
        // `pick 1` is `dip { copy } ; swap`; the dip's *body* is the block the
        // compiler shares — the frame around it is built where it is written.
        let block_of = |term: TermIndex| {
            let Term::Compose(front, _) = ctx.get(term) else {
                panic!("a pick lowers to a composition");
            };
            let Term::Par(body, _) = ctx.get(*front) else {
                panic!("a dip lowers to a par against the identity");
            };
            *body
        };
        let probe = block_of(terms[sentence_named(&library, "probe")]);
        let again = block_of(terms[sentence_named(&library, "again")]);
        assert_eq!(probe, again);
    }

    // ---- arity ----

    #[test]
    fn the_block_operators_have_the_arities_they_are_named_for() {
        let mut ctx = Context::new();
        let three = ctx.id(3);
        assert_eq!(ctx.arity(three), Arity::new(3, 3));
        let dropped = ctx.drop(3);
        assert_eq!(ctx.arity(dropped), Arity::new(3, 0));
        let copied = ctx.copy(3);
        assert_eq!(ctx.arity(copied), Arity::new(3, 6));
        let nothing = ctx.id(0);
        assert_eq!(ctx.arity(nothing), Arity::new(0, 0));
    }

    #[test]
    fn par_adds_both_sides_and_compose_takes_the_ends() {
        let mut ctx = Context::new();
        // 2 -> 1 beside 3 -> 3.
        let (equal, three) = (ctx.op(Prim::Equal), ctx.id(3));
        let par = ctx.par(equal, three);
        assert_eq!(ctx.arity(par), Arity::new(5, 4));

        // 1 -> 2 into 2 -> 1.
        let copy = ctx.copy(1);
        let composed = ctx.compose(copy, equal).unwrap();
        assert_eq!(ctx.arity(composed), Arity::new(1, 1));
    }

    #[test]
    fn a_branch_takes_its_arms_arity_plus_the_condition() {
        let mut ctx = Context::new();
        let two = ctx.drop(2);
        let nothing = ctx.id(0);
        let composed = ctx.compose(two, nothing).unwrap();
        let branch = ctx.branch(two, composed).unwrap();
        assert_eq!(ctx.arity(branch), Arity::new(3, 0));
    }

    // ---- constructors ----

    #[test]
    fn compose_refuses_halves_that_do_not_meet() {
        let mut ctx = Context::new();
        let (one, add) = (ctx.id(1), ctx.op(Prim::Add));
        let err = ctx.compose(one, add).unwrap_err();
        assert_eq!(
            err,
            Error::Mismatch {
                left: Arity::new(1, 1),
                right: Arity::new(2, 1),
            }
        );
    }

    #[test]
    fn branch_refuses_arms_of_different_arity() {
        let mut ctx = Context::new();
        let (one, two) = (ctx.drop(1), ctx.drop(2));
        assert!(ctx.branch(one, two).is_err());
    }

    #[test]
    fn pad_compose_widens_whichever_side_is_narrower() {
        let mut ctx = Context::new();
        // The prefix leaves one value where the next term wants two, so the
        // prefix is the one that grows.
        let (push, add) = (ctx.op(Prim::Push(Value::Int(1))), ctx.op(Prim::Add));
        let short_left = ctx.pad_compose(push, add);
        assert_eq!(
            format!("{}", ctx.display(short_left)),
            "id(1) * push 1 ; add"
        );
        assert_eq!(ctx.arity(short_left), Arity::new(1, 1));

        // The prefix leaves two values where the next term wants one, so the
        // spare value passes under the next term instead.
        let (copy, not) = (ctx.copy(1), ctx.op(Prim::Not));
        let short_right = ctx.pad_compose(copy, not);
        assert_eq!(
            format!("{}", ctx.display(short_right)),
            "copy(1) ; id(1) * not"
        );
        assert_eq!(ctx.arity(short_right), Arity::new(1, 2));
    }

    #[test]
    fn padding_by_nothing_builds_nothing() {
        let mut ctx = Context::new();
        let two = ctx.id(2);
        assert_eq!(ctx.under(two, 0), two);
        let (copy, equal) = (ctx.copy(1), ctx.op(Prim::Equal));
        let met = ctx.pad_compose(copy, equal);
        assert_eq!(format!("{}", ctx.display(met)), "copy(1) ; equal");
    }

    #[test]
    fn pad_branch_widens_the_shallower_arm() {
        // Both arms leave one value fewer than they take, but the first asks
        // for two where the second asks for one, so the second is widened.
        let mut ctx = Context::new();
        let (equal, drop) = (ctx.op(Prim::Equal), ctx.drop(1));
        let branch = ctx.pad_branch(equal, drop).unwrap();
        assert_eq!(ctx.arity(branch), Arity::new(3, 1));
        assert_eq!(
            format!("{}", ctx.display(branch)),
            "branch { equal } { id(1) * drop(1) }"
        );
    }

    #[test]
    fn pad_branch_refuses_arms_that_leave_the_stack_differently() {
        let mut ctx = Context::new();
        let (drop, id) = (ctx.drop(1), ctx.id(1));
        let err = ctx.pad_branch(drop, id).unwrap_err();
        assert_eq!(
            err,
            Error::ArmsDiffer {
                if_true: Arity::new(1, 0),
                if_false: Arity::new(1, 1),
            }
        );
    }

    #[test]
    fn the_constructors_do_not_normalize() {
        let mut ctx = Context::new();
        let (zero, two) = (ctx.id(0), ctx.id(2));
        let par = ctx.par(zero, two);
        assert_eq!(*ctx.get(par), Term::Par(zero, two));
        let nothing = ctx.drop(0);
        assert_eq!(*ctx.get(nothing), Term::Drop(0));
    }

    // ---- printing ----

    #[test]
    fn par_binds_tighter_than_compose() {
        let mut ctx = Context::new();
        let a = ctx.id(1);
        // (a * a) ; a needs no parentheses.
        let (par, two) = (ctx.par(a, a), ctx.id(2));
        let tight = ctx.compose(par, two).unwrap();
        assert_eq!(format!("{}", ctx.display(tight)), "id(1) * id(1) ; id(2)");
        // (a ; a) * a does.
        let composed = ctx.compose(a, a).unwrap();
        let loose = ctx.par(composed, a);
        assert_eq!(format!("{}", ctx.display(loose)), "(id(1) ; id(1)) * id(1)");
    }

    #[test]
    fn both_operators_print_left_associatively() {
        let mut ctx = Context::new();
        let a = ctx.id(1);
        let inner = ctx.compose(a, a).unwrap();
        let left = ctx.compose(inner, a).unwrap();
        assert_eq!(format!("{}", ctx.display(left)), "id(1) ; id(1) ; id(1)");
        let right = ctx.compose(a, inner).unwrap();
        assert_eq!(format!("{}", ctx.display(right)), "id(1) ; (id(1) ; id(1))");

        let inner = ctx.par(a, a);
        let left = ctx.par(inner, a);
        assert_eq!(format!("{}", ctx.display(left)), "id(1) * id(1) * id(1)");
        let right = ctx.par(a, inner);
        assert_eq!(format!("{}", ctx.display(right)), "id(1) * (id(1) * id(1))");
    }

    #[test]
    fn what_fits_the_width_is_left_on_one_line() {
        let mut ctx = Context::new();
        let (copy, equal, drop) = (ctx.copy(1), ctx.op(Prim::Equal), ctx.drop(1));
        let front = ctx.pad_compose(copy, equal);
        let spine = ctx.pad_compose(front, drop);
        assert_eq!(
            format!("{}", ctx.pretty(spine, 40)),
            "copy(1) ; equal ; drop(1)"
        );
        // The same term with nowhere to put it breaks at every `;` of its
        // spine, and at no other place.
        assert_eq!(
            format!("{}", ctx.pretty(spine, 10)),
            "copy(1) ;\nequal ;\ndrop(1)"
        );
    }

    #[test]
    fn a_broken_branch_indents_its_arms() {
        let mut ctx = Context::new();
        let mut arm = |v| {
            let (drop, push) = (ctx.drop(1), ctx.op(Prim::Push(Value::Int(v))));
            ctx.pad_compose(drop, push)
        };
        let (then, otherwise) = (arm(1), arm(2));
        let branch = ctx.branch(then, otherwise).unwrap();
        let copy = ctx.copy(1);
        let whole = ctx.pad_compose(copy, branch);
        assert_eq!(
            format!("{}", ctx.pretty(whole, 20)),
            "copy(1) ;\nbranch {\n  drop(1) ; push 1\n} {\n  drop(1) ; push 2\n}"
        );
    }

    #[test]
    fn a_group_that_breaks_lines_up_inside_its_parenthesis() {
        // The parentheses are the one-line spelling's, so the broken form still
        // says the compose leans right; the lines inside sit under the open
        // paren.
        let mut ctx = Context::new();
        let (copy, equal, not) = (ctx.copy(1), ctx.op(Prim::Equal), ctx.op(Prim::Not));
        let front = ctx.pad_compose(copy, equal);
        let group = ctx.compose(front, not).unwrap();
        let right = ctx.compose(not, group).unwrap();
        assert_eq!(
            format!("{}", ctx.display(right)),
            "not ; (copy(1) ; equal ; not)"
        );
        assert_eq!(
            format!("{}", ctx.pretty(right, 20)),
            "not ;\n(copy(1) ; equal ;\n not)"
        );
    }

    #[test]
    fn a_call_prints_by_name_when_the_library_is_at_hand() {
        let library =
            assemble("mod inner { #[arity(1,1)] sentence twice { pick 0 add } }").unwrap();
        let target = sentence_named(&library, "inner::twice");
        let mut ctx = Context::new();
        let call = ctx.call(target, call_arity(&library, target).unwrap());
        assert_eq!(
            format!("{}", ctx.display(call)),
            format!("call #{}", usize::from(target))
        );
        assert_eq!(
            format!("{}", ctx.display(call).named(&library)),
            "call inner::twice"
        );
    }

    // ---- lowering ----

    #[test]
    fn an_empty_sentence_is_the_identity_on_nothing() {
        assert_eq!(lowered("sentence probe { }", "probe"), "id(0)");
    }

    #[test]
    fn a_sequence_pads_as_it_goes() {
        assert_eq!(
            lowered("sentence probe { push 1 push 2 add }", "probe"),
            "push 1 ; id(1) * push 2 ; add"
        );
    }

    #[test]
    fn dip_becomes_a_par_against_the_identity() {
        assert_eq!(
            lowered("sentence probe { dip { add } }", "probe"),
            "add * id(1)"
        );
    }

    #[test]
    fn a_deep_dip_is_that_many_pars() {
        // Three one-deep frames, since the instruction set has no width: the
        // nest is what a depth used to be, and `X * id(3)` is a theorem about
        // this, not the way it lowers.
        assert_eq!(
            lowered("sentence probe { dip 3 { add } }", "probe"),
            "add * id(1) * id(1) * id(1)"
        );
    }

    #[test]
    fn a_named_call_stays_closed_and_a_block_is_opened() {
        let library = assemble(
            r#"
            sentence helper { add }
            sentence probe { jump crate::helper dip { jump crate::helper } dip { drop 0 } }
        "#,
        )
        .unwrap();
        let helper = sentence_named(&library, "helper");
        let probe = sentence_named(&library, "probe");
        let mut ctx = Context::new();
        let term = lower(&mut ctx, &library, probe).unwrap();
        ctx.check(term).unwrap();
        // The dip needs three values where the jump before it left one, so the
        // prefix is widened by two; the frames after it meet what is there.
        assert_eq!(
            format!("{}", ctx.display(term)),
            format!(
                "id(2) * call #{h} ; call #{h} * id(1) ; drop(1) * id(1)",
                h = usize::from(helper)
            )
        );
    }

    #[test]
    fn a_reach_expands_into_the_frames_it_compiles_to() {
        // `pick 1` is `dip { copy } ; swap`, and the block it dips into is
        // shared with every other `pick 1` in the program.
        assert_eq!(
            lowered("sentence probe { pick 1 }", "probe"),
            "copy(1) * id(1) ; id(1) * swap"
        );
    }

    #[test]
    fn a_branch_lowers_with_the_condition_on_top() {
        let library = assemble("sentence probe { branch { push 1 } { push 2 } }").unwrap();
        let probe = sentence_named(&library, "probe");
        let mut ctx = Context::new();
        let term = lower(&mut ctx, &library, probe).unwrap();
        ctx.check(term).unwrap();
        assert_eq!(
            format!("{}", ctx.display(term)),
            "branch { push 1 } { push 2 }"
        );
        assert_eq!(ctx.arity(term), Arity::new(1, 1));
    }

    /// Every sentence the integration suite compiles, lowered.
    ///
    /// A smoke test rather than a proof: it says that lowering survives real
    /// programs and agrees with the arity checker about all of them, which is
    /// the most a model can be held to before there is a rule set to run
    /// against it.
    #[test]
    fn the_whole_corpus_lowers() {
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
        let terms = lower_all(&mut ctx, &library).unwrap();
        assert!(terms.len() > 100, "the corpus should be a real one");
        for (idx, term) in terms.iter_enumerated() {
            ctx.check(*term).unwrap();
            let inferred = sentence_arity(&library, idx).expect("the corpus compiled");
            assert_eq!(
                ctx.arity(*term),
                Arity::new(inferred.inputs as usize, inferred.outputs as usize),
                "sentence {:?} ({})",
                idx,
                library.names[idx]
            );
        }
    }

    #[test]
    fn a_lowered_sentence_has_the_arity_the_checker_inferred() {
        let library = assemble(
            r#"
            sentence helper { add drop 0 }
            sentence probe {
                push 1
                copy
                jump crate::helper
                dip 2 { swap }
                // Both arms leave one more than they take, but the else arm
                // asks for a value where the then arm asks for none, so
                // lowering has to widen one of them.
                branch { push 1 } { copy }
            }
        "#,
        )
        .unwrap();
        let mut ctx = Context::new();
        for (idx, _) in library.sentences.iter_enumerated() {
            let term = lower(&mut ctx, &library, idx).unwrap();
            ctx.check(term).unwrap();
            let inferred = sentence_arity(&library, idx).unwrap();
            assert_eq!(
                ctx.arity(term),
                Arity::new(inferred.inputs as usize, inferred.outputs as usize),
                "sentence {:?} ({}) lowered to {}",
                idx,
                library.names[idx],
                ctx.display(term)
            );
        }
    }
}
