//! The syntax trees the compiler passes through.
//!
//! [`sugar`] is the full surface language as parsed. [`core`] is the subset that
//! cannot be expressed in terms of other surface constructs — the test being
//! "could a user have written this by hand in `.hana`?". Lowering (`crate::lower`)
//! turns the former into the latter.
//!
//! Only the top-level item enum and the module declaration differ between the
//! two; sentences, symbols, instructions, values, paths and annotations are all
//! shared by composition. See `docs/compilation.md`.

use crate::library::Annotation;
use crate::resolve::Path;

/// An annotation as written in source: it names its target by path.
pub type SourceAnnotation = Annotation<Path>;

/// A value as written in source. References to declared constants — symbols and
/// const strings alike — are still paths here; they become
/// [`crate::value::Value`]s only once resolution has run.
#[derive(Debug, Clone)]
pub enum ParsedValue {
    Bool(bool),
    Int(i64),
    Float(f64),
    ConstString(String),
    Tuple(Vec<ParsedValue>),
    Ref(Path),
}

#[derive(Debug, Clone)]
pub struct ParsedSentence {
    pub instructions: Vec<ParsedInstruction>,
}

/// Where a `jump`, `dip` or `branch` goes: a named sentence, or an anonymous block.
///
/// Inline blocks survive lowering and are flattened into their own sentences
/// during resolution, where sentence indices are already being allocated.
#[derive(Debug, Clone)]
pub enum Target {
    Label(Path),
    Inline(ParsedSentence),
}

/// An instruction before resolution.
///
/// Shared between sugar and core. `TypeCheckPath` is the one variant a user
/// cannot write — it is only ever produced by lowering a [`TypeSpec`] — but
/// duplicating a 32-variant enum to express that is not worth the churn.
#[derive(Debug, Clone)]
pub enum ParsedInstruction {
    Push(ParsedValue),
    Drop(usize),
    Pick(usize),
    Roll(usize),
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
    Jump(Target),
    /// Run the target with the top `usize` values of the stack hidden from it.
    Dip(usize, Target),
    Branch(Target, Target),
    Panic,
    Assert,
    AssertEqual,
    Tuple(usize),
    Untuple(usize),
    And,
    Or,
    ConstStringLen,
    ConstStringCharAt,
    IsInt,
    IsBool,
    IsFloat,
    IsConstString,
    IsSymbol,
    IsTuple,
    TupleLength,
    /// Check the top of stack against the predicate or symbol `Path` names.
    TypeCheckPath(Path),
}

/// A symbol declaration. Shared between sugar and core.
///
/// A symbol carries no text: the name it is declared under is the whole
/// declaration, and the fully qualified form of it is what the value prints as.
#[derive(Debug, Clone)]
pub struct SymbolDecl {
    pub name: String,
}

/// A const string declaration. Shared between sugar and core.
#[derive(Debug, Clone)]
pub struct ConstStringDecl {
    pub name: String,
    pub text: String,
}

/// A sentence declaration. Shared between sugar and core.
///
/// The `function` keyword is not a separate item kind: it lowers to a sentence
/// carrying an extra `Arity(1, 1)` annotation.
#[derive(Debug, Clone)]
pub struct SentenceDecl {
    pub name: String,
    pub body: ParsedSentence,
    pub annotations: Vec<SourceAnnotation>,
    pub is_exported: bool,
    pub is_test: bool,
}

/// A type specification. Sugar only — it never survives lowering.
#[derive(Debug, Clone)]
pub enum TypeSpec {
    Primitive(PrimitiveType),
    Literal(ParsedValue),
    Path(Path),
    Tuple(Vec<TypeSpec>),
    Union(Vec<TypeSpec>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    Int,
    Bool,
    Float,
    ConstString,
    Symbol,
    Tuple,
}

impl std::fmt::Display for ParsedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParsedValue::Bool(b) => write!(f, "{}", b),
            ParsedValue::Int(i) => write!(f, "{}", i),
            ParsedValue::Float(fl) => write!(f, "{}", fl),
            // Quoted, because composer templates are rendered as text and
            // re-parsed: what this prints has to lex back to the same literal.
            ParsedValue::ConstString(s) => write!(f, "{:?}", s),
            ParsedValue::Tuple(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                if elements.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            ParsedValue::Ref(path) => write!(f, "{}", path),
        }
    }
}

/// The surface language, as parsed. No desugaring has happened yet.
pub mod sugar {
    use super::{
        ConstStringDecl, ParsedValue, SentenceDecl, SourceAnnotation, SymbolDecl, TypeSpec,
    };
    use crate::resolve::Path;

    #[derive(Debug, Clone)]
    pub enum Item {
        Symbol(SymbolDecl),
        ConstString(ConstStringDecl),
        Sentence(SentenceDecl),
        Mod(ModDecl),
        Type(TypeDecl),
        Enum(EnumDecl),
        Compose(ComposeDecl),
    }

    #[derive(Debug, Clone)]
    pub struct ModDecl {
        pub name: String,
        pub items: Vec<Item>,
        pub is_test: bool,
    }

    #[derive(Debug, Clone)]
    pub struct TypeDecl {
        pub name: String,
        pub spec: TypeSpec,
        pub annotations: Vec<SourceAnnotation>,
    }

    #[derive(Debug, Clone)]
    pub struct EnumDecl {
        pub name: String,
        pub variants: Vec<EnumVariant>,
        pub annotations: Vec<SourceAnnotation>,
    }

    #[derive(Debug, Clone)]
    pub struct EnumVariant {
        pub name: String,
        /// The payload element specs, as written between the parentheses.
        pub elements: Vec<TypeSpec>,
    }

    #[derive(Debug, Clone)]
    pub struct ComposeDecl {
        pub name: String,
        pub composer: Composer,
        pub args: Vec<ModuleExpr>,
        pub is_test: bool,
    }

    /// An argument to a composer: a module path, a nested composition, or a
    /// literal value.
    #[derive(Debug, Clone)]
    pub enum ModuleExpr {
        Named(Path),
        Composed {
            composer: Composer,
            args: Vec<ModuleExpr>,
        },
        Value(ParsedValue),
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Composer {
        Concurrent,
        Hidden,
        Prefix,
        RenamePrefix,
        StaticClosure,
        Done,
        Emit,
        EmitStatic,
        Accept,
        AcceptStatic,
    }

    impl Composer {
        pub fn from_name(name: &str) -> Option<Self> {
            match name {
                "compose_concurrent" => Some(Composer::Concurrent),
                "compose_hidden" => Some(Composer::Hidden),
                "compose_prefix" => Some(Composer::Prefix),
                "compose_rename_prefix" => Some(Composer::RenamePrefix),
                "compose_static_closure" => Some(Composer::StaticClosure),
                "compose_done" => Some(Composer::Done),
                "compose_emit" => Some(Composer::Emit),
                "compose_emit_static" => Some(Composer::EmitStatic),
                "compose_accept" => Some(Composer::Accept),
                "compose_accept_static" => Some(Composer::AcceptStatic),
                _ => None,
            }
        }

        pub fn name(&self) -> &'static str {
            match self {
                Composer::Concurrent => "compose_concurrent",
                Composer::Hidden => "compose_hidden",
                Composer::Prefix => "compose_prefix",
                Composer::RenamePrefix => "compose_rename_prefix",
                Composer::StaticClosure => "compose_static_closure",
                Composer::Done => "compose_done",
                Composer::Emit => "compose_emit",
                Composer::EmitStatic => "compose_emit_static",
                Composer::Accept => "compose_accept",
                Composer::AcceptStatic => "compose_accept_static",
            }
        }
    }
}

/// The irreducible subset of the language. Everything here corresponds to
/// something a user could have written by hand.
pub mod core {
    use super::{ConstStringDecl, SentenceDecl, SymbolDecl};

    #[derive(Debug, Clone)]
    pub enum Item {
        Symbol(SymbolDecl),
        ConstString(ConstStringDecl),
        Sentence(SentenceDecl),
        Mod(ModDecl),
    }

    #[derive(Debug, Clone)]
    pub struct ModDecl {
        pub name: String,
        pub items: Vec<Item>,
        pub is_test: bool,
        /// Set for modules generated by a composer, whose bodies carry no
        /// `export` markers of their own.
        pub exports_machine_sentences: bool,
    }
}
