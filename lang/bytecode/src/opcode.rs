use crate::library::SentenceIndex;
use crate::value::Value;

/// A structured representation of a single bytecode instruction in the conceptual ISA.
///
/// # Moving values
///
/// Four instructions move values, and none of them takes a depth: [`Drop`],
/// [`Copy`], [`Swap`] and [`Dip`], the last hiding exactly one value. Every
/// deeper reach is written in terms of them, by a recursion the compiler
/// performs and nothing here records:
///
/// ```text
/// drop 0 = drop            pick 0 = copy               roll 0 = ε
/// drop d = dip { drop (d-1) }
/// pick d = dip { pick (d-1) } ; swap
/// roll d = dip { roll (d-1) } ; swap
/// ```
///
/// `pick` and `roll` are one recursion with two base cases, which is the whole
/// of the difference between copying a value up and moving it up.
///
/// The surface language still spells all three, and `docs/hana.md` documents
/// them; what is gone is the *indexed instruction*. A depth in an instruction
/// is a pointer into the stack, and every law about one is an infinite family
/// indexed by that pointer, with arithmetic in its side conditions — an
/// equational account of the ISA needed five separate axioms only to say
/// things about `pick d` and `roll d` that `copy`, `swap` and one-deep `dip`
/// say in a single equation each. A frame's width was the same kind of index,
/// and nesting is what replaces it.
///
/// See `docs/compilation.md` for what phase 4 emits, and `docs/movement.md` for
/// why the trade is worth taking.
///
/// # Every instruction answers, and none of them reports
///
/// A data instruction leaves exactly what it computed and nothing about how it
/// got there. `add` on two symbols has no sum to give, so it gives `Int 0`;
/// `untuple 3` of a symbol has no three parts to give, so it gives three `()`s.
/// Neither leaves a `bool` saying which happened, because **the question is the
/// caller's and the caller can ask it**: `is_int` and `pick 0 ; pick 0 ;
/// as_tuple n ; equal` are the two shapes of it, and each leaves the value
/// itself underneath the answer. A flag on top of the answer asked the question
/// for every caller whether or not any of them wanted it, and cost every site
/// that did not a `drop` to say so.
///
/// What is left is that each instruction has a **codomain**: `add` leaves an
/// `Int` on every pair of values, `less` a `Bool`, `untuple n` exactly `n`
/// values. See [`yields_bool`] for why that is the one fact an equational
/// account cannot discover for itself, and `docs/totality.md` for the table.
///
/// # Coercions
///
/// [`AsBool`], [`AsInt`] and [`AsTuple`] force a value to a type: each is the
/// identity where the value is already of that type, and hands back a default
/// where it is not. They are the codomain named on its own, for a value nothing
/// is being computed from — and they are what the junk answers above are
/// defined through, `untuple n` being `as_tuple n` followed by taking a tuple
/// of the right width apart. Code that wants the question asked rather than the
/// answer forced has `is_int`, and can `copy` first.
///
/// Case-splitting a value on whether it is an Int leaves it opaque in the arm
/// where it is not, so no rewrite can conclude that what came out is an Int;
/// after `as_int`, it is one by construction. Hence `as_int ; as_int` =
/// `as_int`, and `as_int ; is_int` = `drop ; push true`.
///
/// [`Drop`]: Instruction::Drop
/// [`Copy`]: Instruction::Copy
/// [`Swap`]: Instruction::Swap
/// [`Dip`]: Instruction::Dip
/// [`AsBool`]: Instruction::AsBool
/// [`AsInt`]: Instruction::AsInt
/// [`AsTuple`]: Instruction::AsTuple
/// [`yields_bool`]: Instruction::yields_bool
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// Push a constant value onto the stack.
    Push(Value),
    /// Discards the value at the top of the stack.
    Drop,
    /// Pushes a second copy of the value on top of the stack.
    Copy,
    /// Exchanges the top two values of the stack.
    Swap,

    /// Compare the top two values on the stack for equality.
    Equal,
    /// Check if the second-to-top value is greater than the top value.
    Greater,
    /// Check if the second-to-top value is less than the top value.
    Less,

    /// Add the top two values on the stack.
    Add,
    /// Subtract the top value from the second-to-top value on the stack.
    Subtract,
    /// Multiply the top two values on the stack.
    Multiply,
    /// Divide the second-to-top value by the top value on the stack.
    Divide,
    /// Calculate modulo: second-to-top value % top value.
    Modulo,

    /// Logically negate the top value on the stack.
    Not,
    /// Negate the numeric top value on the stack.
    Negate,

    /// Call the sentence at the target.
    Jump(SentenceIndex),
    /// Hide the top value, call the sentence at the target, then restore the
    /// hidden value on top of its results.
    ///
    /// **One value, never more.** `dip 3 { A }` is three of these nested, which
    /// is what makes the width a *shape* rather than a number: no equation
    /// about a frame does arithmetic on it, and no analysis has a depth to get
    /// wrong. The hidden value is inaccessible to the callee, so it may be
    /// treated as unchanged across the call.
    ///
    /// The two call instructions are the only ones, and [`Self::callee`] is how
    /// a traversal reaches both — writing them as two variants is what makes
    /// the hidden value part of the shape, and the accessor is what keeps a
    /// walk from handling one and silently missing the other.
    Dip(SentenceIndex),
    /// Conditionally branch: if the top value on the stack is truthy, jump to the first SentenceIndex;
    /// otherwise, jump to the second SentenceIndex.
    Branch(SentenceIndex, SentenceIndex),

    /// Pops the top N values off the stack and packages them into a single
    /// Tuple, keeping the order they were in on the stack: the deepest of them
    /// is element 0 and the topmost is the last, so `push 1 ; push 2 ; tuple 2`
    /// is `(1, 2)`.
    Tuple(usize),
    /// Pops a value off the stack and pushes `N` values back, element 0 first —
    /// undoing [`Instruction::Tuple`] slot for slot.
    ///
    /// This is [`AsTuple(n)`][Instruction::AsTuple] and then the taking apart:
    /// a value that is not a tuple of exactly `N` elements has no `N` parts to
    /// give, so what comes back is `N` `()`s. Nothing says which of the two
    /// happened, and a caller that needs to know asks first — `pick 0 ; pick 0
    /// ; as_tuple n ; equal` is the question, and it is the one the `type` sugar
    /// and `?` both write.
    Untuple(usize),

    /// Pop the top two values on the stack, evaluate logical AND on their truthiness, and push the result.
    And,
    /// Pop the top two values on the stack, evaluate logical OR on their truthiness, and push the result.
    Or,

    /// Pop a value off the stack and push its character length as an Int: the
    /// count of a ConstString, and `0` for anything with no characters to count.
    ConstStringLen,
    /// Pop an index (Int) and a ConstString off the stack, and push the Unicode
    /// code point of the character at that index as an Int. An index out of
    /// range reads no code point, and answers `0` — as does an operand of the
    /// wrong type.
    ConstStringCharAt,

    /// Pop the top value and push true if it is an Int, else false.
    IsInt,
    /// Pop the top value and push true if it is a Bool, else false.
    IsBool,
    /// Pop the top value and push true if it is a ConstString, else false.
    IsConstString,
    /// Pop the top value and push true if it is a Symbol, else false.
    IsSymbol,
    /// Pop the top value and push true if it is a Tuple, else false — and,
    /// with a width, true only if it is a Tuple of exactly that many
    /// elements.
    ///
    /// The width is **optional** here and required on
    /// [`AsTuple`][Instruction::AsTuple], and the asymmetry is the
    /// difference between asking and forcing. "A tuple of some length" is a
    /// question with an answer, so `is_tuple` alone means it; it is not a
    /// coercion anything could perform, so `as_tuple` alone means nothing
    /// and is refused.
    ///
    /// `is_tuple n` is the guard the rest of the language is written
    /// against, because the width is part of the type in exactly the sense
    /// [`Untuple`][Instruction::Untuple] means it: a tuple of the wrong
    /// length is as much a mismatch as a symbol, being precisely the values
    /// `untuple n` could not take apart. Asking it in pieces — `is_tuple ;
    /// tuple_length ; push n ; equal` — states the same domain in four
    /// instructions and three stack slots, and the pieces can drift.
    IsTuple(Option<usize>),
    /// Pop the top value and push its length as an Int: the element count of a
    /// Tuple, and `0` for anything else, which has no length to count.
    TupleLength,

    /// Pop the top value and push its truthiness as a Bool.
    ///
    /// This is [`Value::truthy`][crate::value::Value::truthy] made into an
    /// instruction, so it is the identity on a `Bool` for the same reason
    /// `truthy(Bool(p)) = p`. Every boolean-shaped operation already applies
    /// that coercion per operand, which makes this the one coercion that
    /// discards nothing a later instruction would have read: `as_bool ; branch`
    /// is `branch`, `as_bool ; not` is `not`, and the same for `and` and `or`
    /// on either operand.
    AsBool,
    /// Pop the top value and push it back if it is an Int, or `Int(0)` if it is
    /// not.
    AsInt,
    /// Pop the top value and push it back if it is a Tuple of exactly `n`
    /// elements, or a tuple of `n` empty tuples if it is not.
    ///
    /// The width is part of the type coerced to, as it is in
    /// [`Untuple`][Instruction::Untuple]: a tuple of the wrong length is as
    /// much a mismatch as a symbol, since it is exactly the values `untuple n`
    /// could not take apart. So `as_tuple n ; untuple n` never reports failure.
    AsTuple(usize),
}

impl Instruction {
    /// The sentence this calls, if it calls one.
    ///
    /// The two call instructions differ in whether a value is hidden, and in
    /// nothing else. A traversal that asks this reaches both; one that matches
    /// on [`Instruction::Jump`] alone silently walks past every `dip`, and
    /// arity inference — which is what refuses recursion — is one of the walks
    /// that must not.
    pub fn callee(&self) -> Option<SentenceIndex> {
        match self {
            Instruction::Jump(s) | Instruction::Dip(s) => Some(*s),
            _ => None,
        }
    }

    /// How many values this hides from the sentence it calls.
    ///
    /// `None` for anything that is not a call. `Some(0)` and `Some(1)` are the
    /// only answers, which is the point: a frame is one value deep, and the
    /// depth an old `Dip(n, _)` carried is now the number of these nested.
    pub fn hidden(&self) -> Option<usize> {
        match self {
            Instruction::Jump(_) => Some(0),
            Instruction::Dip(_) => Some(1),
            _ => None,
        }
    }

    /// Whether this takes two operands and answers the same either way round.
    ///
    /// `swap` exchanges the top two values, so for these — and only these —
    /// `swap ; op` is `op`. It lives here rather than in whatever wants to use
    /// it, because it is a fact about the instruction set, the same way
    /// [`crate::arity::op_arity`] is; a second copy of the list would be a
    /// silent hazard rather than a duplication.
    ///
    /// The junk answer is symmetric too: `add` on a symbol and an int has no
    /// sum to give whichever order they arrive in, and answers `0` both ways.
    ///
    pub fn commutative(&self) -> bool {
        matches!(
            self,
            Instruction::Add
                | Instruction::Multiply
                | Instruction::And
                | Instruction::Or
                | Instruction::Equal
        )
    }

    /// Whether doing this twice is doing it once.
    ///
    /// A fact about the instruction set for the same reason
    /// [`commutative`] is, and read the same way: `op ; op` is `op` for
    /// these and for nothing else, so a rewriter may collapse a repeat
    /// without asking what the operand was. `vm` measures it, running
    /// every candidate once and twice on every shape of operand.
    ///
    /// The list is the three coercions, and that is not a coincidence: a
    /// coercion's whole content is its **codomain**, so what it leaves is
    /// already of the type it forces, and forcing it again is asking a
    /// question that has been answered. Nothing else on the list of
    /// one-operand instructions is idempotent — `not` and `negate` are
    /// their own inverses rather than their own answer, `tuple 1` wraps
    /// again, and each `is_` test asked of its own answer is asking
    /// something about a `Bool`.
    ///
    /// The width in [`AsTuple`][Instruction::AsTuple] rides along, as it
    /// does everywhere else: `as_tuple n ; as_tuple n` is the identity on
    /// the second coercion, while `as_tuple 2 ; as_tuple 3` is two
    /// different questions and is no instance of this at all.
    ///
    /// [`commutative`]: Instruction::commutative
    pub fn idempotent(&self) -> bool {
        matches!(
            self,
            Instruction::AsBool | Instruction::AsInt | Instruction::AsTuple(_)
        )
    }

    /// Whether what this leaves on top of the stack is always a `Bool`.
    ///
    /// Folding `op ; is_bool` to `op ; drop ; push true` rests on this, so a
    /// wrong entry is a soundness bug rather than an inaccurate comment — and
    /// `vm` measures it, running every candidate on every shape of operand and
    /// holding the list to what it finds.
    ///
    /// The list is the predicates and the boolean connectives, which is what is
    /// left once no instruction reports on itself: an operation that answers
    /// with a `bool` is one that was *asked* something. `add` leaves an `Int`
    /// on every pair of values, junk included, so it is not here — the codomain
    /// it does have is a fact of the same kind with nowhere to be said.
    ///
    /// The exclusions worth naming:
    ///
    /// - `tuple n` builds a tuple, and is the negative case the sweep needs to
    ///   stay honest about being a measurement.
    /// - `drop`, `copy` and `swap` leave a value that came off the stack rather
    ///   than one they computed, so nothing about the instruction decides it.
    /// - `push` leaves exactly its literal, so the answer is known *better*
    ///   than this: evaluation folds `push c ; is_bool` to the literal it
    ///   really is, where this would only say that it is one.
    ///
    /// A **codomain is not something a rewrite can discover.** Case-splitting
    /// a value on whether it is a boolean leaves the value opaque in the case
    /// where it is not, and every equation over the instruction set is true of
    /// an `is_bool` that answered `42` for `true` — truthiness is all a branch
    /// can observe, and `false` is the only falsy value. So this fact has to be
    /// stated about the instruction and measured against the machine.
    pub fn yields_bool(&self) -> bool {
        matches!(
            self,
            Instruction::Equal
                | Instruction::Greater
                | Instruction::Less
                | Instruction::Not
                | Instruction::And
                | Instruction::Or
                | Instruction::IsInt
                | Instruction::IsBool
                | Instruction::IsConstString
                | Instruction::IsSymbol
                | Instruction::IsTuple(_)
                // A coercion's whole point is its codomain, and this one's is
                // `Bool`. The other two leave an Int and a Tuple, which is the
                // same fact about a different type and has nowhere to be said.
                | Instruction::AsBool
        )
    }
}

/// Renders an instruction in source mnemonic form, for traces and dumps.
impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Push(v) => write!(f, "push {}", v),
            Instruction::Drop => write!(f, "drop"),
            Instruction::Copy => write!(f, "copy"),
            Instruction::Swap => write!(f, "swap"),
            Instruction::Equal => write!(f, "equal"),
            Instruction::Greater => write!(f, "greater"),
            Instruction::Less => write!(f, "less"),
            Instruction::Add => write!(f, "add"),
            Instruction::Subtract => write!(f, "subtract"),
            Instruction::Multiply => write!(f, "multiply"),
            Instruction::Divide => write!(f, "divide"),
            Instruction::Modulo => write!(f, "modulo"),
            Instruction::Not => write!(f, "not"),
            Instruction::Negate => write!(f, "negate"),
            Instruction::Jump(s) => write!(f, "jump {:?}", s),
            Instruction::Dip(s) => write!(f, "dip {:?}", s),
            Instruction::Branch(t, e) => write!(f, "branch {:?} {:?}", t, e),
            Instruction::Tuple(n) => write!(f, "tuple {}", n),
            Instruction::Untuple(n) => write!(f, "untuple {}", n),
            Instruction::And => write!(f, "and"),
            Instruction::Or => write!(f, "or"),
            Instruction::ConstStringLen => write!(f, "const_string_len"),
            Instruction::ConstStringCharAt => write!(f, "const_string_char_at"),
            Instruction::IsInt => write!(f, "is_int"),
            Instruction::IsBool => write!(f, "is_bool"),
            Instruction::IsConstString => write!(f, "is_const_string"),
            Instruction::IsSymbol => write!(f, "is_symbol"),
            Instruction::IsTuple(None) => write!(f, "is_tuple"),
            Instruction::IsTuple(Some(n)) => write!(f, "is_tuple {}", n),
            Instruction::TupleLength => write!(f, "tuple_length"),
            Instruction::AsBool => write!(f, "as_bool"),
            Instruction::AsInt => write!(f, "as_int"),
            Instruction::AsTuple(n) => write!(f, "as_tuple {}", n),
        }
    }
}
