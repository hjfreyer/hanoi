use crate::opcode::Instruction;
use crate::value::Value;
use std::collections::{HashMap, HashSet};
use derive_more::{From, Into};
use typed_index_collections::TiVec;

/// A type-safe index wrapper for indexing a `Sentence` in a `Library`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
pub struct SentenceIndex(usize);

/// A Sentence is a sequence of instructions.
pub type Sentence = Vec<Instruction>;

/// A declaration annotation, parameterized by how it names another sentence.
///
/// The AST uses `Annotation<Path>`, since names are all it has. Resolution turns
/// those into `Annotation<SentenceIndex>` for the library, the same
/// names-to-indices erasure the instructions undergo.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Annotation<Ref> {
    Arity(i64, i64),
    Recursive,
    Precondition(Ref),
    Postcondition(Ref),
    Total,
    /// This sentence sees the success flags of fallible instructions.
    ///
    /// Without it `assemble` drops each flag as it emits the instruction, so
    /// source written against the old arities keeps working and junk still
    /// propagates silently. With it, `untuple 3` really does leave four values,
    /// and the sentence is expected to say what happens on failure.
    Flags,
    /// This sentence may fail: it panics, asserts, or calls something that
    /// does.
    ///
    /// Checked, not inferred — see [`crate::arity::check_partiality`]. The
    /// annotation propagates up the call graph the way [`Annotation::Recursive`]
    /// does, so its *absence* on a sentence is a proof that the sentence
    /// terminates normally on every input it accepts.
    Partial,
}

/// An annotation as it appears in a compiled [`Library`].
pub type SentenceAnnotation = Annotation<SentenceIndex>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Arity {
    Normal { inputs: i64, outputs: i64 },
    Panic { inputs: i64 },
}

impl Arity {
    pub fn inputs(&self) -> i64 {
        match *self {
            Arity::Normal { inputs, .. } => inputs,
            Arity::Panic { inputs } => inputs,
        }
    }

    pub fn outputs(&self) -> Option<i64> {
        match *self {
            Arity::Normal { outputs, .. } => Some(outputs),
            Arity::Panic { .. } => None,
        }
    }
}

/// A Library contains a collection of sentences indexed type-safely using `SentenceIndex`.
#[derive(Debug, Clone, PartialEq)]
pub struct Library {
    pub sentences: TiVec<SentenceIndex, Sentence>,
    pub exports: HashMap<String, SentenceIndex>,
    pub symbols: HashMap<String, Value>,
    pub tests: HashMap<String, SentenceIndex>,
    pub test_machines: HashSet<String>,
    pub annotations: TiVec<SentenceIndex, Vec<SentenceAnnotation>>,
    pub names: TiVec<SentenceIndex, String>,
    pub instruction_arities: TiVec<SentenceIndex, Option<Vec<Arity>>>,
}

impl Library {
    /// Creates a new, empty Library.
    pub fn new() -> Self {
        Self {
            sentences: TiVec::new(),
            exports: HashMap::new(),
            symbols: HashMap::new(),
            tests: HashMap::new(),
            test_machines: HashSet::new(),
            annotations: TiVec::new(),
            names: TiVec::new(),
            instruction_arities: TiVec::new(),
        }
    }
}

impl Default for Library {
    fn default() -> Self {
        Self::new()
    }
}
