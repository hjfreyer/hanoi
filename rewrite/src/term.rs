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
//! Nothing here decides whether two terms are equal. This is the model a rule
//! set will be stated over, and it carries no analysis machinery at all.

use std::collections::HashMap;
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

            Prim::Equal | Prim::And | Prim::Or => Arity::new(2, 1),

            Prim::Not
            | Prim::IsInt
            | Prim::IsBool
            | Prim::IsConstString
            | Prim::IsSymbol
            | Prim::IsTuple
            // The coercions, which report nothing and so stay one wide.
            | Prim::AsBool
            | Prim::AsInt
            | Prim::AsTuple(_) => Arity::new(1, 1),

            // The fallible ones, each a slot wider than the value it computes
            // because the extra slot carries the success flag.
            Prim::Greater
            | Prim::Less
            | Prim::Add
            | Prim::Subtract
            | Prim::Multiply
            | Prim::Divide
            | Prim::Modulo
            | Prim::ConstStringCharAt => Arity::new(2, 2),
            Prim::Negate | Prim::ConstStringLen | Prim::TupleLength => Arity::new(1, 2),

            Prim::Tuple(n) => Arity::new(*n, 1),
            Prim::Untuple(n) => Arity::new(1, *n + 1),
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

/// A program, as a tree of two operators over a handful of leaves.
///
/// Every term has an [`arity`][Term::arity], and every way of building one
/// either preserves the arities it was given or is rejected. The constructors
/// are where that is enforced; the variants are public because a rule set has
/// to match on them.
///
/// **The constructors check, they do not normalize.** `Term::par(Term::id(0),
/// a)` builds exactly `Par(Id(0), a)`, and `Term::drop(0)` stays `Drop(0)`
/// rather than becoming `Id(0)`. The unit laws are among the first things a
/// rule set will want to state, and a constructor that quietly applied them
/// would be deciding equalities that the prover is supposed to derive.
/// [`lower`] avoids emitting units in the first place, which is a different
/// thing: it declines to build them, rather than building and then discarding
/// them.
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
    /// The arity is carried rather than looked up, so [`Term::arity`] needs no
    /// [`Library`] and a term stays meaningful on its own. It is the callee's
    /// *inferred* arity, which is what the machine consumes; a wider
    /// `#[arity]` annotation is a claim about the sentence, not about what a
    /// call to it does.
    Call { target: SentenceIndex, arity: Arity },
    /// `A ; B`: everything `A` leaves, `B` takes. Requires `A.outputs ==
    /// B.inputs`, which is the whole point — see [`Term::pad_compose`] for how
    /// a sentence's implicit padding is made explicit to get there.
    Compose(Box<Term>, Box<Term>),
    /// `A * B`: the stack is cut by arity and both sides run on their own
    /// piece.
    ///
    /// **The second argument gets the top.** `B` takes the topmost
    /// `B.inputs` values and `A` takes the `A.inputs` below them, which is
    /// forced by `dip N { X }` being `X * id(N)`: `dip` hides the top of the
    /// stack, so the identity is the one on top. Padding therefore always
    /// reads `id(k) * A`, with the untouched values underneath.
    Par(Box<Term>, Box<Term>),
    /// The condition on top, then whichever arm it selects.
    ///
    /// The arms are held to the same arity, so the branch has one: with arms
    /// `n -> m` the branch is `n + 1 -> m`, the extra input being the
    /// condition. That is what the machine does — it pops the condition and
    /// enters the arm with the rest of the stack.
    Branch {
        if_true: Box<Term>,
        if_false: Box<Term>,
    },
}

impl Term {
    // ---- leaves ----

    pub fn id(n: usize) -> Term {
        Term::Id(n)
    }

    pub fn drop(n: usize) -> Term {
        Term::Drop(n)
    }

    pub fn copy(n: usize) -> Term {
        Term::Copy(n)
    }

    pub fn op(prim: Prim) -> Term {
        Term::Op(prim)
    }

    pub fn call(target: SentenceIndex, arity: Arity) -> Term {
        Term::Call { target, arity }
    }

    // ---- operators ----

    /// `left ; right`, which exists only when the halves meet exactly.
    pub fn compose(left: Term, right: Term) -> Result<Term, Error> {
        let (l, r) = (left.arity(), right.arity());
        if l.outputs != r.inputs {
            return Err(Error::Mismatch { left: l, right: r });
        }
        Ok(Term::Compose(Box::new(left), Box::new(right)))
    }

    /// `left * right`. Total: any two terms can run side by side.
    pub fn par(left: Term, right: Term) -> Term {
        Term::Par(Box::new(left), Box::new(right))
    }

    /// A branch on two arms of the same arity.
    pub fn branch(if_true: Term, if_false: Term) -> Result<Term, Error> {
        let (t, f) = (if_true.arity(), if_false.arity());
        if t != f {
            return Err(Error::ArmsDiffer {
                if_true: t,
                if_false: f,
            });
        }
        Ok(Term::Branch {
            if_true: Box::new(if_true),
            if_false: Box::new(if_false),
        })
    }

    // ---- padding ----

    /// The same term with `n` more values passing underneath, untouched.
    ///
    /// `n == 0` is the term itself rather than `id(0) * A`: there is nothing to
    /// pass through, and building the unit only to have a rule remove it again
    /// helps nobody.
    pub fn under(self, n: usize) -> Term {
        if n == 0 {
            self
        } else {
            Term::par(Term::id(n), self)
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
    pub fn pad_compose(left: Term, right: Term) -> Term {
        let (l, r) = (left.arity().outputs, right.arity().inputs);
        let (left, right) = if l < r {
            (left.under(r - l), right)
        } else {
            (left, right.under(l - r))
        };
        Term::compose(left, right).expect("padding is what makes the halves meet")
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
    pub fn pad_branch(if_true: Term, if_false: Term) -> Result<Term, Error> {
        let (t, f) = (if_true.arity(), if_false.arity());
        if t.net() != f.net() {
            return Err(Error::ArmsDiffer {
                if_true: t,
                if_false: f,
            });
        }
        let (if_true, if_false) = if t.inputs < f.inputs {
            (if_true.under(f.inputs - t.inputs), if_false)
        } else {
            (if_true, if_false.under(t.inputs - f.inputs))
        };
        Term::branch(if_true, if_false)
    }

    // ---- reading a term ----

    /// What this takes off the stack and leaves on it.
    ///
    /// Structural, and linear in the size of the term: no node caches its
    /// answer, and [`Term::Call`] is the one that could not be worked out
    /// locally, which is why it carries its own. Caching is an easy change to
    /// make when something measures it as worth making.
    pub fn arity(&self) -> Arity {
        match self {
            Term::Id(n) => Arity::new(*n, *n),
            Term::Drop(n) => Arity::new(*n, 0),
            Term::Copy(n) => Arity::new(*n, 2 * n),
            Term::Op(prim) => prim.arity(),
            Term::Call { arity, .. } => *arity,
            Term::Compose(left, right) => Arity::new(left.arity().inputs, right.arity().outputs),
            Term::Par(left, right) => {
                let (l, r) = (left.arity(), right.arity());
                Arity::new(l.inputs + r.inputs, l.outputs + r.outputs)
            }
            Term::Branch { if_true, .. } => {
                let arm = if_true.arity();
                Arity::new(arm.inputs + 1, arm.outputs)
            }
        }
    }

    /// Whether every node in the term obeys the invariants its constructor
    /// enforces.
    ///
    /// Nothing needs this when a term was built through the constructors, which
    /// is the point of them. It is here for tests, and for anything that builds
    /// a term by taking one apart and putting it back together.
    pub fn check(&self) -> Result<(), Error> {
        match self {
            Term::Id(_) | Term::Drop(_) | Term::Copy(_) | Term::Op(_) | Term::Call { .. } => Ok(()),
            Term::Compose(left, right) => {
                left.check()?;
                right.check()?;
                let (l, r) = (left.arity(), right.arity());
                if l.outputs != r.inputs {
                    return Err(Error::Mismatch { left: l, right: r });
                }
                Ok(())
            }
            Term::Par(left, right) => {
                left.check()?;
                right.check()
            }
            Term::Branch { if_true, if_false } => {
                if_true.check()?;
                if_false.check()?;
                let (t, f) = (if_true.arity(), if_false.arity());
                if t != f {
                    return Err(Error::ArmsDiffer {
                        if_true: t,
                        if_false: f,
                    });
                }
                Ok(())
            }
        }
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

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write(f, 0)
    }
}

impl Term {
    fn precedence(&self) -> u8 {
        match self {
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
    fn write(&self, f: &mut fmt::Formatter<'_>, context: u8) -> fmt::Result {
        if self.precedence() < context {
            write!(f, "(")?;
            self.write(f, 0)?;
            return write!(f, ")");
        }
        match self {
            Term::Id(n) => write!(f, "id({})", n),
            Term::Drop(n) => write!(f, "drop({})", n),
            Term::Copy(n) => write!(f, "copy({})", n),
            Term::Op(prim) => write!(f, "{}", prim),
            Term::Call { target, .. } => write!(f, "call #{}", usize::from(*target)),
            Term::Compose(left, right) => {
                left.write(f, PREC_COMPOSE)?;
                write!(f, " ; ")?;
                right.write(f, PREC_COMPOSE + 1)
            }
            Term::Par(left, right) => {
                left.write(f, PREC_PAR)?;
                write!(f, " * ")?;
                right.write(f, PREC_PAR + 1)
            }
            Term::Branch { if_true, if_false } => {
                write!(f, "branch {{ ")?;
                if_true.write(f, 0)?;
                write!(f, " }} {{ ")?;
                if_false.write(f, 0)?;
                write!(f, " }}")
            }
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

/// The term a sentence stands for.
pub fn lower(library: &Library, sentence: SentenceIndex) -> Result<Term, Error> {
    Lowering::new(library).sentence(sentence)
}

/// Every sentence in the library, lowered, sharing the work between them.
///
/// Inline blocks appear twice over: spliced into whatever wrote them, and again
/// as an entry of their own. A caller normally wants the entries for named
/// sentences, which are the ones anything can reach.
pub fn lower_all(library: &Library) -> Result<TiVec<SentenceIndex, Term>, Error> {
    let mut lowering = Lowering::new(library);
    let mut terms = TiVec::with_capacity(library.sentences.len());
    for idx in library.sentences.keys() {
        terms.push(lowering.sentence(idx)?);
    }
    Ok(terms)
}

/// One pass over a library, remembering what it has already worked out.
///
/// The memos are not an optimization of a slow thing but of a repeated one: the
/// compiler shares a single block between every `pick 2` in the program, and a
/// callee's arity is re-derived from scratch by every [`sentence_arity`] call.
struct Lowering<'a> {
    library: &'a Library,
    arities: HashMap<SentenceIndex, Arity>,
    blocks: HashMap<SentenceIndex, Term>,
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
    fn sentence(&mut self, idx: SentenceIndex) -> Result<Term, Error> {
        // Detached from `self` so the loop can hold it while the body borrows
        // the memos mutably; the library outlives both.
        let library = self.library;
        let mut acc: Option<Term> = None;
        for inst in &library.sentences[idx] {
            let next = self.instruction(inst)?;
            acc = Some(match acc {
                None => next,
                Some(prefix) => Term::pad_compose(prefix, next),
            });
        }
        // An empty sentence is the identity on nothing, which is the unit of
        // composition and the honest reading of a program that does nothing.
        Ok(acc.unwrap_or_else(|| Term::id(0)))
    }

    fn instruction(&mut self, inst: &Instruction) -> Result<Term, Error> {
        Ok(match inst {
            Instruction::Jump(target) => self.target(*target)?,
            // The hidden value is the top of the stack, so the identity is the
            // one on the right: `dip { A }` is `A * id(1)`.
            Instruction::Dip(target) => Term::par(self.target(*target)?, Term::id(1)),
            Instruction::Branch(if_true, if_false) => {
                let if_true = self.target(*if_true)?;
                let if_false = self.target(*if_false)?;
                Term::pad_branch(if_true, if_false)?
            }
            Instruction::Drop => Term::drop(1),
            Instruction::Copy => Term::copy(1),
            local => Term::op(
                Prim::from_instruction(local)
                    .expect("the instructions without a prim are matched above"),
            ),
        })
    }

    /// A called sentence: spliced in if it is a block, named if it is not.
    fn target(&mut self, idx: SentenceIndex) -> Result<Term, Error> {
        if self.library.names[idx] != INLINE_BLOCK {
            let arity = self.arity_of(idx)?;
            return Ok(Term::call(idx, arity));
        }
        if let Some(term) = self.blocks.get(&idx) {
            return Ok(term.clone());
        }
        let term = self.sentence(idx)?;
        self.blocks.insert(idx, term.clone());
        Ok(term)
    }

    fn arity_of(&mut self, idx: SentenceIndex) -> Result<Arity, Error> {
        if let Some(arity) = self.arities.get(&idx) {
            return Ok(*arity);
        }
        let inferred = sentence_arity(self.library, idx).ok_or(Error::NoArity(idx))?;
        let arity = Arity::new(
            usize::try_from(inferred.inputs).expect("an inferred arity counts up from zero"),
            usize::try_from(inferred.outputs).expect("an inferred arity counts up from zero"),
        );
        self.arities.insert(idx, arity);
        Ok(arity)
    }
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
        let term = lower(&library, idx).unwrap();
        term.check().unwrap();
        format!("{}", term)
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

    // ---- arity ----

    #[test]
    fn the_block_operators_have_the_arities_they_are_named_for() {
        assert_eq!(Term::id(3).arity(), Arity::new(3, 3));
        assert_eq!(Term::drop(3).arity(), Arity::new(3, 0));
        assert_eq!(Term::copy(3).arity(), Arity::new(3, 6));
        assert_eq!(Term::id(0).arity(), Arity::new(0, 0));
    }

    #[test]
    fn par_adds_both_sides_and_compose_takes_the_ends() {
        // 2 -> 1 beside 3 -> 3.
        let par = Term::par(Term::op(Prim::Equal), Term::id(3));
        assert_eq!(par.arity(), Arity::new(5, 4));

        // 1 -> 2 into 2 -> 1.
        let composed = Term::compose(Term::copy(1), Term::op(Prim::Equal)).unwrap();
        assert_eq!(composed.arity(), Arity::new(1, 1));
    }

    #[test]
    fn a_branch_takes_its_arms_arity_plus_the_condition() {
        let branch = Term::branch(
            Term::drop(2),
            Term::compose(Term::drop(2), Term::id(0)).unwrap(),
        )
        .unwrap();
        assert_eq!(branch.arity(), Arity::new(3, 0));
    }

    // ---- constructors ----

    #[test]
    fn compose_refuses_halves_that_do_not_meet() {
        let err = Term::compose(Term::id(1), Term::op(Prim::Add)).unwrap_err();
        assert_eq!(
            err,
            Error::Mismatch {
                left: Arity::new(1, 1),
                right: Arity::new(2, 2),
            }
        );
    }

    #[test]
    fn branch_refuses_arms_of_different_arity() {
        assert!(Term::branch(Term::drop(1), Term::drop(2)).is_err());
    }

    #[test]
    fn pad_compose_widens_whichever_side_is_narrower() {
        // The prefix leaves one value where the next term wants two, so the
        // prefix is the one that grows.
        let short_left =
            Term::pad_compose(Term::op(Prim::Push(Value::Int(1))), Term::op(Prim::Add));
        assert_eq!(format!("{}", short_left), "id(1) * push 1 ; add");
        assert_eq!(short_left.arity(), Arity::new(1, 2));

        // The prefix leaves two values where the next term wants one, so the
        // spare value passes under the next term instead.
        let short_right = Term::pad_compose(Term::op(Prim::Add), Term::op(Prim::Not));
        assert_eq!(format!("{}", short_right), "add ; id(1) * not");
        assert_eq!(short_right.arity(), Arity::new(2, 2));
    }

    #[test]
    fn padding_by_nothing_builds_nothing() {
        assert_eq!(Term::id(2).under(0), Term::id(2));
        let met = Term::pad_compose(Term::copy(1), Term::op(Prim::Equal));
        assert_eq!(format!("{}", met), "copy(1) ; equal");
    }

    #[test]
    fn pad_branch_widens_the_shallower_arm() {
        // Both arms leave one value fewer than they take, but the first asks
        // for two where the second asks for one, so the second is widened.
        let branch = Term::pad_branch(Term::op(Prim::Equal), Term::drop(1)).unwrap();
        assert_eq!(branch.arity(), Arity::new(3, 1));
        assert_eq!(
            format!("{}", branch),
            "branch { equal } { id(1) * drop(1) }"
        );
    }

    #[test]
    fn pad_branch_refuses_arms_that_leave_the_stack_differently() {
        let err = Term::pad_branch(Term::drop(1), Term::id(1)).unwrap_err();
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
        assert_eq!(
            Term::par(Term::id(0), Term::id(2)),
            Term::Par(Box::new(Term::Id(0)), Box::new(Term::Id(2)))
        );
        assert_eq!(Term::drop(0), Term::Drop(0));
    }

    // ---- printing ----

    #[test]
    fn par_binds_tighter_than_compose() {
        let a = || Term::id(1);
        // (a * a) ; a needs no parentheses.
        let tight = Term::compose(Term::par(a(), a()), Term::id(2)).unwrap();
        assert_eq!(format!("{}", tight), "id(1) * id(1) ; id(2)");
        // (a ; a) * a does.
        let loose = Term::par(Term::compose(a(), a()).unwrap(), a());
        assert_eq!(format!("{}", loose), "(id(1) ; id(1)) * id(1)");
    }

    #[test]
    fn both_operators_print_left_associatively() {
        let a = || Term::id(1);
        let left = Term::compose(Term::compose(a(), a()).unwrap(), a()).unwrap();
        assert_eq!(format!("{}", left), "id(1) ; id(1) ; id(1)");
        let right = Term::compose(a(), Term::compose(a(), a()).unwrap()).unwrap();
        assert_eq!(format!("{}", right), "id(1) ; (id(1) ; id(1))");

        let left = Term::par(Term::par(a(), a()), a());
        assert_eq!(format!("{}", left), "id(1) * id(1) * id(1)");
        let right = Term::par(a(), Term::par(a(), a()));
        assert_eq!(format!("{}", right), "id(1) * (id(1) * id(1))");
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
        let term = lower(&library, probe).unwrap();
        term.check().unwrap();
        // The dip needs three values where the jump before it left two, so the
        // prefix is widened; the dip after it leaves one fewer than the prefix
        // has, so the spare value passes underneath instead.
        assert_eq!(
            format!("{}", term),
            format!(
                "id(1) * call #{h} ; call #{h} * id(1) ; id(1) * (drop(1) * id(1))",
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
        let term = lower(&library, probe).unwrap();
        term.check().unwrap();
        assert_eq!(format!("{}", term), "branch { push 1 } { push 2 }");
        assert_eq!(term.arity(), Arity::new(1, 1));
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

        let terms = lower_all(&library).unwrap();
        assert!(terms.len() > 100, "the corpus should be a real one");
        for (idx, term) in terms.iter_enumerated() {
            term.check().unwrap();
            let inferred = sentence_arity(&library, idx).expect("the corpus compiled");
            assert_eq!(
                term.arity(),
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
        for (idx, _) in library.sentences.iter_enumerated() {
            let term = lower(&library, idx).unwrap();
            term.check().unwrap();
            let inferred = sentence_arity(&library, idx).unwrap();
            assert_eq!(
                term.arity(),
                Arity::new(inferred.inputs as usize, inferred.outputs as usize),
                "sentence {:?} ({}) lowered to {}",
                idx,
                library.names[idx],
                term
            );
        }
    }
}
