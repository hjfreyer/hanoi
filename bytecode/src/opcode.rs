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
    
    /// Pop a ValueSet and a Value off the stack, check if the value is in the set, and push a Bool.
    SetContains,
    /// Pop two ValueSets off the stack, and push their union ValueSet.
    SetUnion,
    /// Pop two ValueSets off the stack, and push their intersection ValueSet.
    SetIntersection,
    /// Pop two ValueSets off the stack, and push their difference ValueSet.
    SetDifference,
    /// Pop a ValueSet off the stack, and push its complement ValueSet.
    SetComplement,
    /// Pop a Value off the stack, and push its singleton ValueSet.
    SetSingleton,
    /// Pop N ValueSets off the stack, and push a set tuple of those N sets.
    SetTuple(usize),
    /// Pop a ValueSet off the stack, select an arbitrary element, and push a tuple (has_element: bool, element: any).
    SetChoose,
}
