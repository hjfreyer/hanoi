use crate::library::SentenceIndex;
use crate::value::Value;

/// A structured representation of a single bytecode instruction in the conceptual ISA.
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// Push a constant value onto the stack.
    Push(Value),
    /// Discards the value at the top of the stack.
    ///
    /// The surface language's `drop <depth>` reaches deeper than this; phase 4
    /// expands it into a `Dip` around this instruction, so that nothing in the
    /// ISA but `Pick` and `Roll` addresses below the top of the stack.
    Drop,
    /// Copies a value at the given depth from the top (0-indexed) of the stack and pushes it to the top.
    /// (e.g., depth=0 is equivalent to Dup, depth=1 is equivalent to Over).
    Pick(usize),
    /// Moves a value at the given depth from the top (0-indexed) to the top of the stack,
    /// shifting all intermediate values down.
    /// (e.g., depth=1 is equivalent to Swap).
    Roll(usize),

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

    /// Hide the top `depth` values, call the sentence at the target SentenceIndex,
    /// then restore the hidden values on top of its results.
    ///
    /// This is the only call instruction: a plain `jump` is `Dip(0, s)`, whose
    /// hidden region is empty. The hidden values are inaccessible to the
    /// callee, so analyses may treat them as unchanged across the call.
    Dip(usize, SentenceIndex),
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

/// Renders an instruction in source mnemonic form, for traces and dumps.
///
/// A zero-width dip prints as `jump`, which is how it was written and how it
/// behaves; the derived `Debug` is still available where the distinction
/// between the two spellings matters.
impl Instruction {
    /// Whether this takes two operands and answers the same either way round.
    ///
    /// `roll 1` swaps the top two values, so for these — and only these —
    /// `roll 1 ; op` is `op`. That is what `bin/rewrite`'s `comm` law rests on,
    /// and it lives here rather than in the rewriter because it is a fact about
    /// the instruction set, the same way [`crate::arity::op_arity`] is; a second
    /// copy of the list would be a silent hazard rather than a duplication.
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
    /// `bin/rewrite` folds `op ; is_bool` to `op ; drop ; push true` on the
    /// strength of this, so a wrong entry is a soundness bug rather than an
    /// inaccurate comment — and `vm` measures it, running every candidate on
    /// every shape of operand and holding the list to what it finds.
    ///
    /// It is a wide list because a **flag** is a boolean: every fallible
    /// operation reports with one, and reports it on top. `add` leaves a sum
    /// and a flag, and it is the flag `is_bool` would be asking about.
    ///
    /// The three exclusions are all deliberate:
    ///
    /// - `tuple n` builds a tuple, and is the negative case the sweep needs to
    ///   stay honest about being a measurement.
    /// - `drop`, `pick` and `roll` leave a value that came off the stack rather
    ///   than one they computed, so nothing about the instruction decides it.
    /// - `push` leaves exactly its literal, so the answer is known *better*
    ///   than this: `eval` folds `push c ; is_bool` to the literal it really
    ///   is, where this would only say that it is one.
    ///
    /// A **codomain is not something a rewrite can discover.** `split_bool`
    /// splits a value into the cases where it is a boolean, but the case where
    /// it is not leaves the value opaque, and every equation the tool has is
    /// true of an `is_bool` that answered `42` for `true` — truthiness is all a
    /// branch can observe, and `false` is the only falsy value. So this fact
    /// has to be stated about the instruction and measured against the machine.
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

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Push(v) => write!(f, "push {}", v),
            Instruction::Drop => write!(f, "drop"),
            Instruction::Pick(d) => write!(f, "pick {}", d),
            Instruction::Roll(d) => write!(f, "roll {}", d),
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
            Instruction::Dip(0, s) => write!(f, "jump {:?}", s),
            Instruction::Dip(d, s) => write!(f, "dip {} {:?}", d, s),
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
