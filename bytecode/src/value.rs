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
#[derive(Debug, Clone, PartialEq)]
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
    /// A set of values.
    Set(ValueSet),
}

/// Represents a mathematical set of values.
#[derive(Debug, Clone, PartialEq)]
pub enum ValueSet {
    Empty,
    Universal,
    Singleton(Box<Value>),
    Union(Box<ValueSet>, Box<ValueSet>),
    Intersection(Box<ValueSet>, Box<ValueSet>),
    Difference(Box<ValueSet>, Box<ValueSet>),
    Tuple(Vec<ValueSet>),
}

impl ValueSet {
    /// Check if a value is contained in the set.
    pub fn contains(&self, val: &Value) -> bool {
        match self {
            ValueSet::Empty => false,
            ValueSet::Universal => true,
            ValueSet::Singleton(v) => *v.as_ref() == *val,
            ValueSet::Union(a, b) => a.contains(val) || b.contains(val),
            ValueSet::Intersection(a, b) => a.contains(val) && b.contains(val),
            ValueSet::Difference(a, b) => a.contains(val) && !b.contains(val),
            ValueSet::Tuple(sets) => {
                if let Value::Tuple(elements) = val {
                    if sets.len() != elements.len() {
                        false
                    } else {
                        sets.iter().zip(elements.iter()).all(|(set, elem)| set.contains(elem))
                    }
                } else {
                    false
                }
            }
        }
    }

    /// Return all elements in the set if it is finite, otherwise None.
    pub fn elements(&self) -> Option<Vec<Value>> {
        match self {
            ValueSet::Empty => Some(vec![]),
            ValueSet::Universal => None,
            ValueSet::Singleton(v) => Some(vec![*v.clone()]),
            ValueSet::Union(a, b) => {
                let ea = a.elements()?;
                let eb = b.elements()?;
                let mut res = ea;
                for v in eb {
                    if !res.contains(&v) {
                        res.push(v);
                    }
                }
                Some(res)
            }
            ValueSet::Intersection(a, b) => {
                if let Some(ea) = a.elements() {
                    Some(ea.into_iter().filter(|v| b.contains(v)).collect())
                } else if let Some(eb) = b.elements() {
                    Some(eb.into_iter().filter(|v| a.contains(v)).collect())
                } else {
                    None
                }
            }
            ValueSet::Tuple(sets) => {
                let mut current = vec![Value::Tuple(vec![])];
                for set in sets {
                    let elems = set.elements()?;
                    let mut next = Vec::new();
                    for cur in current {
                        if let Value::Tuple(cv) = cur {
                            for e in &elems {
                                let mut new_cv = cv.clone();
                                new_cv.push(e.clone());
                                next.push(Value::Tuple(new_cv));
                            }
                        }
                    }
                    current = next;
                }
                Some(current)
            }
            ValueSet::Difference(a, b) => {
                let ea = a.elements()?;
                Some(ea.into_iter().filter(|v| !b.contains(v)).collect())
            }
        }
    }

    /// Choose an arbitrary element from the set, if one exists.
    pub fn choose(&self) -> Option<Value> {
        if let Some(elems) = self.elements() {
            return elems.first().cloned();
        }
        match self {
            ValueSet::Universal => Some(Value::Tuple(vec![])),
            ValueSet::Difference(_, _) => panic!("Cannot choose from a difference set with an infinite LHS"),
            ValueSet::Union(a, b) => a.choose().or_else(|| b.choose()),
            ValueSet::Intersection(a, b) => choose_intersection(a, b),
            ValueSet::Tuple(sets) => {
                let mut elements = Vec::new();
                for set in sets {
                    if let Some(elem) = set.choose() {
                        elements.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(Value::Tuple(elements))
            }
            _ => None,
        }
    }
}

fn choose_intersection(a: &ValueSet, b: &ValueSet) -> Option<Value> {
    match (a, b) {
        (ValueSet::Empty, _) | (_, ValueSet::Empty) => None,
        (ValueSet::Universal, other) => other.choose(),
        (_, ValueSet::Universal) => a.choose(),
        (ValueSet::Singleton(v), other) => {
            if other.contains(v) {
                Some(*v.clone())
            } else {
                None
            }
        }
        (other, ValueSet::Singleton(v)) => {
            if other.contains(v) {
                Some(*v.clone())
            } else {
                None
            }
        }
        (ValueSet::Union(a1, a2), other) => {
            choose_intersection(a1, other).or_else(|| choose_intersection(a2, other))
        }
        (other, ValueSet::Union(b1, b2)) => {
            choose_intersection(other, b1).or_else(|| choose_intersection(other, b2))
        }
        (ValueSet::Intersection(a1, a2), other) => {
            choose_intersection(a1, &ValueSet::Intersection(a2.clone(), Box::new(other.clone())))
        }
        (other, ValueSet::Intersection(b1, b2)) => {
            choose_intersection(other, &ValueSet::Intersection(b1.clone(), b2.clone()))
        }
        (ValueSet::Tuple(sets_a), ValueSet::Tuple(sets_b)) => {
            if sets_a.len() != sets_b.len() {
                None
            } else {
                let mut elements = Vec::new();
                for (sa, sb) in sets_a.iter().zip(sets_b.iter()) {
                    if let Some(elem) = choose_intersection(sa, sb) {
                        elements.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(Value::Tuple(elements))
            }
        }
        (ValueSet::Difference(a1, a2), other) => {
            let intersection = ValueSet::Intersection(a1.clone(), Box::new(other.clone()));
            ValueSet::Difference(Box::new(intersection), a2.clone()).choose()
        }
        (other, ValueSet::Difference(b1, b2)) => {
            let intersection = ValueSet::Intersection(Box::new(other.clone()), b1.clone());
            ValueSet::Difference(Box::new(intersection), b2.clone()).choose()
        }
    }
}

impl fmt::Display for ValueSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueSet::Empty => write!(f, "empty_set"),
            ValueSet::Universal => write!(f, "universal_set"),
            ValueSet::Singleton(v) => write!(f, "singleton({})", v),
            ValueSet::Union(a, b) => write!(f, "union({}, {})", a, b),
            ValueSet::Intersection(a, b) => write!(f, "intersection({}, {})", a, b),
            ValueSet::Difference(a, b) => write!(f, "difference({}, {})", a, b),
            ValueSet::Tuple(elements) => {
                write!(f, "set_tuple(")?;
                for (idx, elem) in elements.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
        }
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
            Value::Set(set) => write!(f, "{}", set),
        }
    }
}

