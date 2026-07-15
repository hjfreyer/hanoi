use std::fmt;

/// Represents any value that can be operated on or stored by the VM.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A representation of no value.
    Nil,
    /// A boolean value (true or false).
    Bool(bool),
    /// A signed 64-bit integer.
    Int(i64),
    /// A 64-bit floating-point number.
    Float(f64),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(val) => write!(f, "{}", val),
        }
    }
}
