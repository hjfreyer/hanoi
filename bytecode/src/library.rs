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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Annotation {
    Arity(i64, i64),
}

/// A Library contains a collection of sentences indexed type-safely using `SentenceIndex`.
#[derive(Debug, Clone, PartialEq)]
pub struct Library {
    pub sentences: TiVec<SentenceIndex, Sentence>,
    pub exports: HashMap<String, SentenceIndex>,
    pub symbols: HashMap<String, Value>,
    pub tests: HashMap<String, SentenceIndex>,
    pub test_machines: HashSet<String>,
    pub annotations: TiVec<SentenceIndex, Vec<Annotation>>,
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
        }
    }
}

impl Default for Library {
    fn default() -> Self {
        Self::new()
    }
}
