use crate::opcode::Instruction;
use derive_more::{From, Into};
use typed_index_collections::TiVec;

/// A type-safe index wrapper for indexing a `Sentence` in a `Library`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
pub struct SentenceIndex(usize);

/// A Sentence is a sequence of instructions.
pub type Sentence = Vec<Instruction>;

/// A Library contains a collection of sentences indexed type-safely using `SentenceIndex`.
#[derive(Debug, Clone, PartialEq)]
pub struct Library {
    pub sentences: TiVec<SentenceIndex, Sentence>,
}

impl Library {
    /// Creates a new, empty Library.
    pub fn new() -> Self {
        Self {
            sentences: TiVec::new(),
        }
    }
}

impl Default for Library {
    fn default() -> Self {
        Self::new()
    }
}
