use crate::opcode::Instruction;
use crate::source::{FileId, Span};
use crate::value::Value;
use derive_more::{From, Into};
use std::collections::{HashMap, HashSet};
use typed_index_collections::TiVec;

/// A type-safe index wrapper for indexing a `Sentence` in a `Library`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
pub struct SentenceIndex(usize);

/// A Sentence is a sequence of instructions.
pub type Sentence = Vec<Instruction>;

/// A type-safe index wrapper for indexing an `Identity` in a `Library`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
pub struct IdentityIndex(usize);

/// A claim that two programs are interchangeable, as `identity name { A } = { B };`
/// states it.
///
/// The two sides are ordinary sentences in the library rather than trees in a
/// side table, and that is the load-bearing choice here. When an identity
/// becomes something a derivation may cite, the applier will regenerate both
/// sides from the library on every application — exactly as it already
/// regenerates an unfolded body — so no copy of a program ever travels inside a
/// script, and a script written against a library that has since changed fails
/// at the step that stopped fitting rather than rewriting by a stale claim.
///
/// Nothing here says whether the claim is *true*. That is
/// [`bin/prove`](../../rewrite)'s job, and it deliberately lives outside the
/// compiler: a proof depends on the rewriter's rule set, which is not part of
/// the language.
#[derive(Debug, Clone, PartialEq)]
pub struct Identity {
    /// Fully qualified, e.g. `identities::a_value_tested_twice`.
    pub name: String,
    pub lhs: SentenceIndex,
    pub rhs: SentenceIndex,
    /// Where the name was written. `span.file` is what pairs the identity with
    /// the `.hant` that must prove it.
    pub span: Span,
}

/// A declaration annotation, parameterized by how it names another sentence.
///
/// The AST uses `Annotation<Path>`, since names are all it has. Resolution turns
/// those into `Annotation<SentenceIndex>` for the library, the same
/// names-to-indices erasure the instructions undergo.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Annotation<Ref> {
    Arity(i64, i64),
    Precondition(Ref),
    Postcondition(Ref),
}

/// An annotation as it appears in a compiled [`Library`].
pub type SentenceAnnotation = Annotation<SentenceIndex>;

/// What a sentence, or one instruction of one, takes off the stack and leaves
/// on it.
///
/// A pair, with nothing to say about a program that does not answer: no
/// instruction can end a run any more, so every sentence has both numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Arity {
    pub inputs: i64,
    pub outputs: i64,
}

impl Arity {
    pub fn net(&self) -> i64 {
        self.outputs - self.inputs
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
    /// The stack depth reached at each instruction of each sentence. Every
    /// sentence has one: inference answers for all of them, since a sentence
    /// whose arity could not be worked out does not compile.
    pub instruction_arities: TiVec<SentenceIndex, Vec<Arity>>,
    /// In declaration order, which is what makes a checker's output
    /// deterministic.
    pub identities: TiVec<IdentityIndex, Identity>,
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
            identities: TiVec::new(),
        }
    }

    /// An identity by exact fully qualified name, or by an unambiguous trailing
    /// part of one — the reading a sentence and a symbol both get.
    pub fn identity_by_name(&self, ident: &str) -> Result<IdentityIndex, String> {
        let exact: Vec<IdentityIndex> = self
            .identities
            .iter_enumerated()
            .filter(|(_, id)| id.name == ident)
            .map(|(idx, _)| idx)
            .collect();
        if let [only] = exact[..] {
            return Ok(only);
        }

        let suffix = format!("::{}", ident);
        let matches: Vec<IdentityIndex> = self
            .identities
            .iter_enumerated()
            .filter(|(_, id)| id.name.ends_with(&suffix))
            .map(|(idx, _)| idx)
            .collect();
        match matches[..] {
            [only] => Ok(only),
            [] => Err(format!("no identity matching '{}'", ident)),
            _ => {
                let named: Vec<&str> = matches
                    .iter()
                    .map(|i| self.identities[*i].name.as_str())
                    .collect();
                Err(format!("'{}' is ambiguous: {}", ident, named.join(", ")))
            }
        }
    }

    /// The identities stated in one file, in declaration order.
    pub fn identities_in(&self, file: FileId) -> Vec<IdentityIndex> {
        self.identities
            .iter_enumerated()
            .filter(|(_, id)| id.span.file == file)
            .map(|(idx, _)| idx)
            .collect()
    }
}

impl Default for Library {
    fn default() -> Self {
        Self::new()
    }
}
