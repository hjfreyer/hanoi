use std::fmt;

/// Represents a unique identifier with a debugging description name.
#[derive(Debug, Clone, Eq)]
pub struct Symbol {
    pub id: usize,
    pub name: String,
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

/// Represents any value that can be operated on or stored by the VM.
#[derive(Clone, PartialEq)]
pub enum Value {
    /// A boolean value (true or false).
    Bool(bool),
    /// A signed 64-bit integer.
    Int(i64),
    /// A 64-bit floating-point number.
    Float(f64),
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

/// Compares two values numerically, promoting a mixed `Int`/`Float` pair.
///
/// `None` covers both reasons an ordering may not exist — an operand that is
/// not a number at all, and a NaN — because `greater` and `less` answer
/// `false` in either case and have no need to tell them apart.
pub fn numeric_cmp(a: &Value, b: &Value) -> Option<std::cmp::Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Some(x.cmp(y)),
        (Value::Float(x), Value::Float(y)) => x.partial_cmp(y),
        (Value::Int(x), Value::Float(y)) => (*x as f64).partial_cmp(y),
        (Value::Float(x), Value::Int(y)) => x.partial_cmp(&(*y as f64)),
        _ => None,
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(val) => write!(f, "{}", val),
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
            Value::Symbol(sym) => write!(f, "symbol({})", sym.name),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}
