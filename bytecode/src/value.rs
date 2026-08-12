use std::fmt;

/// A unique identity, and nothing else.
///
/// A symbol is equal to itself and to no other value: `id` is the whole of it,
/// and two declarations reading the same are still two symbols. `path` is the
/// fully qualified name it was declared under, carried for printing only — it
/// takes no part in equality, and nothing in the language can read it.
///
/// Text that a program is meant to *look at* is a [`Value::ConstString`]. The
/// two were one thing until the string a symbol carried was doing double duty
/// as its description and as data, which made `symbol_len` a question about a
/// value that was supposed to be opaque.
#[derive(Debug, Clone, Eq)]
pub struct Symbol {
    pub id: usize,
    pub path: String,
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

/// Represents any value that can be operated on or stored by the VM.
///
/// Equality here is structural **identity**: two values compare equal exactly
/// when nothing in the language can tell them apart. That is what makes `Eq`
/// derivable, and it is what [`crate::opcode::Instruction::Equal`] means.
/// Floats were the one exception — `0.0 == -0.0` on two values that stay
/// distinguishable — and they are gone.
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    /// A boolean value (true or false).
    Bool(bool),
    /// A signed 64-bit integer.
    Int(i64),
    /// An immutable string of characters.
    ///
    /// Unlike a [`Symbol`], it is exactly its text: two const strings reading
    /// the same are the same value, and `const_string_len` and
    /// `const_string_char_at` read it.
    ConstString(String),
    /// A conceptual tuple containing multiple values.
    Tuple(Vec<Value>),
    /// A unique symbol value.
    Symbol(Symbol),
}

impl Value {
    /// Whether this value counts as true: everything except `Bool(false)`.
    ///
    /// **`false` is the unique falsy value.** A number, a symbol, a tuple —
    /// anything that is not literally `false` — is true, so `branch` takes the
    /// then arm on junk and `not junk` is `false`.
    ///
    /// Every boolean-shaped instruction — `not`, `and`, `or`, `branch`,
    /// `assert` — is defined through this, applied **per operand**. That, and
    /// not the choice of which pole is unique, is what makes De Morgan hold on
    /// all values rather than only on booleans: the derivation needs only
    /// `truthy(Bool(p)) = p`, which holds either way round. See
    /// `docs/totality.md`.
    ///
    /// The consequence worth knowing is about `assert`, which fails exactly
    /// when its operand is falsy: it now passes on junk, and only a literal
    /// `false` fails it. An assertion here checks that something did not
    /// definitely go wrong, rather than that it definitely went right.
    ///
    /// It lives here rather than in the VM because `bin/rewrite` folds the
    /// same operators and has to agree with the interpreter exactly; a second
    /// copy of the definition would be a silent hazard rather than a
    /// duplication, in the same way [`crate::arity::op_arity`] is shared.
    pub fn truthy(&self) -> bool {
        *self != Value::Bool(false)
    }

    /// The empty tuple, which is the junk the untupling instructions hand
    /// back.
    pub fn unit() -> Value {
        Value::Tuple(Vec::new())
    }
}

/// Compares two values numerically.
///
/// `None` says there is no ordering, which since `Int` is the only number is
/// exactly the case where an operand is not a number at all: `greater` and
/// `less` answer `false` and fail there.
pub fn numeric_cmp(a: &Value, b: &Value) -> Option<std::cmp::Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Some(x.cmp(y)),
        _ => None,
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Tuple(elements) => {
                write!(f, "(")?;
                for (idx, elem) in elements.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                // Single-element tuples print with a trailing comma to distinguish them
                if elements.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            Value::ConstString(s) => write!(f, "{:?}", s),
            // A symbol has no text of its own, so it shows where it was
            // declared: `crate::io::stdout::putch` prints as `io::stdout::putch`,
            // the same fully qualified name the library keys it under.
            Value::Symbol(sym) => write!(f, "{}", sym.path),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}
