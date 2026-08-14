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
/// [`Drop`]: Instruction::Drop
/// [`Copy`]: Instruction::Copy
/// [`Swap`]: Instruction::Swap
/// [`Dip`]: Instruction::Dip
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
    /// Pops a Tuple off the stack, checks that it contains exactly N elements,
    /// and pushes each of those elements back onto the stack, element 0 first —
    /// undoing [`Instruction::Tuple`] slot for slot.
    Untuple(usize),

    /// Pop the top two values on the stack, evaluate logical AND on their truthiness, and push the result.
    And,
    /// Pop the top two values on the stack, evaluate logical OR on their truthiness, and push the result.
    Or,

    /// Pop a ConstString off the stack, and push its character length as an Int.
    ConstStringLen,
    /// Pop an index (Int) and a ConstString off the stack, and push the Unicode code point of the character at that index as an Int.
    ConstStringCharAt,

    /// Pop the top value and push true if it is an Int, else false.
    IsInt,
    /// Pop the top value and push true if it is a Bool, else false.
    IsBool,
    /// Pop the top value and push true if it is a ConstString, else false.
    IsConstString,
    /// Pop the top value and push true if it is a Symbol, else false.
    IsSymbol,
    /// Pop the top value and push true if it is a Tuple, else false.
    IsTuple,
    /// Pop the top value (must be a Tuple) and push its length as an Int.
    TupleLength,
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
    /// The flag a fallible one leaves is symmetric too: `add` on a symbol and an
    /// int fails whichever order they arrive in, answering `0, false` both ways.
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

    /// Whether what this leaves on top of the stack is always a `Bool`.
    ///
    /// Folding `op ; is_bool` to `op ; drop ; push true` rests on this, so a
    /// wrong entry is a soundness bug rather than an inaccurate comment — and
    /// `vm` measures it, running every candidate on every shape of operand and
    /// holding the list to what it finds.
    ///
    /// It is a wide list because a **flag** is a boolean: every fallible
    /// operation reports with one, and reports it on top. `add` leaves a sum
    /// and a flag, and it is the flag `is_bool` would be asking about.
    ///
    /// The three exclusions are all deliberate:
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
                | Instruction::Add
                | Instruction::Subtract
                | Instruction::Multiply
                | Instruction::Divide
                | Instruction::Modulo
                | Instruction::Not
                | Instruction::Negate
                | Instruction::And
                | Instruction::Or
                | Instruction::ConstStringLen
                | Instruction::ConstStringCharAt
                | Instruction::IsInt
                | Instruction::IsBool
                | Instruction::IsConstString
                | Instruction::IsSymbol
                | Instruction::IsTuple
                | Instruction::TupleLength
                | Instruction::Untuple(_)
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
            Instruction::IsTuple => write!(f, "is_tuple"),
            Instruction::TupleLength => write!(f, "tuple_length"),
        }
    }
}
