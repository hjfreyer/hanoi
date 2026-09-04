//! What a box computes, and how many values it reads and answers with.
//!
//! Two types with no graph in them, kept apart from [`graph`](super::graph)
//! because they are the vocabulary a graph is written in rather than part of
//! its structure. [`Prim`] mirrors the instruction set minus the five things
//! a graph says by naming; [`Arity`] is the pair of counts every box and
//! every graph has.
//!
//! Nothing here knows what a program is. A [`Prim`] is one operation and
//! answers only for itself.

use std::fmt;

use bytecode::{Instruction, Value};

/// How many values a box reads and how many it answers with.
///
/// Both counts are non-negative, which is the difference from
/// [`bytecode::Arity`] and the reason for a second type: a sentence's arity is
/// *inferred* and reported as a pair of `i64`, since the checker discovers a
/// requirement it did not know it had and grows one side to meet it. By the
/// time there is a box to state an arity of, the question is settled: a port
/// exists or it does not, and neither count can go negative.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Arity {
    pub inputs: usize,
    pub outputs: usize,
}

impl Arity {
    pub const fn new(inputs: usize, outputs: usize) -> Self {
        Self { inputs, outputs }
    }

    /// How much deeper the stack is afterwards. Negative if this eats more
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

/// An operation a box can be: every [`Instruction`] but the five a graph says
/// by naming instead.
///
/// Each exclusion is a thing the representation already says, and keeping a
/// box for it would mean two graphs for one program:
///
/// | Instruction | said in a graph as |
/// | --- | --- |
/// | `copy` | one source named twice |
/// | `drop` | a source named nowhere |
/// | `jump` | [`NodeKind::Call`](super::graph::NodeKind::Call) |
/// | `dip` | the hidden value simply not handed to the callee |
/// | `branch` | a [`Select`](super::graph::NodeKind::Select) per answer |
///
/// A separate enum rather than a validated `Instruction` also gives the rule
/// set somewhere to put facts that are true of the local instructions and of
/// nothing else — [`Instruction::commutative`] and [`Instruction::codomain`]
/// are two that already exist — without a call variant coming along that they
/// would have to answer for.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    IsTuple(Option<usize>),
    TupleLength,

    AsBool,
    AsInt,
    AsTuple(usize),
}

impl Prim {
    /// The instruction as a prim, or `None` for the five a graph expresses by
    /// naming.
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
            Instruction::IsTuple(n) => Prim::IsTuple(*n),
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
            Prim::IsTuple(n) => Instruction::IsTuple(*n),
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
            | Prim::IsTuple(_)
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
            // Both readings, since they are two questions and a walk that
            // handled one and missed the other is the bug `all` is for.
            Prim::IsTuple(None),
            Prim::IsTuple(Some(2)),
            Prim::TupleLength,
            Prim::AsBool,
            Prim::AsInt,
            Prim::AsTuple(5),
        ]
    }
}

/// Prints the mnemonic the instruction prints, so a listing and a trace name
/// the same operation the same way.
impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_instruction())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytecode::SentenceIndex;
    use bytecode::arity::op_arity;

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
}
