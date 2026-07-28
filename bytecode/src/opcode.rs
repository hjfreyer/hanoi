use crate::library::SentenceIndex;
use crate::value::Value;

/// A structured representation of a single bytecode instruction in the conceptual ISA.
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// Push a constant value onto the stack.
    Push(Value),
    /// Discards a value at the given depth from the top (0-indexed) of the stack.
    /// (e.g., depth=0 is equivalent to Pop).
    Drop(usize),
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
    
    /// Print the top value on the stack (useful for debugging/IO).
    Print,
    
    /// Unconditionally jump to the start of the sentence at the target SentenceIndex.
    Jump(SentenceIndex),
    /// Conditionally branch: if the top value on the stack is truthy, jump to the first SentenceIndex;
    /// otherwise, jump to the second SentenceIndex.
    Branch(SentenceIndex, SentenceIndex),
    
    /// Abort execution immediately.
    Panic,
    /// Pop the top value off the stack and panic if it is falsey.
    Assert,
    /// Pop the top two values off the stack and panic if they are not equal.
    AssertEqual,
    
    /// Pops the top N values off the stack and packages them into a single Tuple.
    Tuple(usize),
    /// Pops a Tuple off the stack, checks that it contains exactly N elements,
    /// and pushes each of those elements back onto the stack in order.
    Untuple(usize),
    
    /// Pop the top two values on the stack, evaluate logical AND on their truthiness, and push the result.
    And,
    /// Pop the top two values on the stack, evaluate logical OR on their truthiness, and push the result.
    Or,
    
    /// Pop a Symbol off the stack, and push its character length as an Int.
    SymbolLen,
    /// Pop an index (Int) and a Symbol off the stack, and push the Unicode code point of the character at that index as an Int.
    SymbolCharAt,
    
    /// Pop the top value and push true if it is an Int, else false.
    IsInt,
    /// Pop the top value and push true if it is a Bool, else false.
    IsBool,
    /// Pop the top value and push true if it is a Float, else false.
    IsFloat,
    /// Pop the top value and push true if it is a Symbol, else false.
    IsSymbol,
    /// Pop the top value and push true if it is a Tuple, else false.
    IsTuple,
    /// Pop the top value (must be a Tuple) and push its length as an Int.
    TupleLength,
}
