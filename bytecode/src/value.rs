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
    /// A set of values.
    Set(ValueSet),
}

/// Represents the result of attempting to choose an element from a set.
#[derive(Debug, Clone, PartialEq)]
pub enum ChooseResult {
    /// The set is empty, so no element can be chosen.
    Empty,
    /// An element was successfully chosen.
    Found(Value),
    /// The set is non-empty, but we cannot determine/choose an element (e.g., it is infinite or complement).
    Unknown,
}

/// Represents a mathematical set of values.
#[derive(Clone, PartialEq)]
pub enum ValueSet {
    Empty,
    Universal,
    Singleton(Box<Value>),
    Union(Box<ValueSet>, Box<ValueSet>),
    Intersection(Box<ValueSet>, Box<ValueSet>),
    Complement(Box<ValueSet>),
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
            ValueSet::Complement(a) => !a.contains(val),
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

    /// Replace occurrences of `from` symbol as the last path component of events (pairs) with `to` symbol.
    pub fn rename_prefix(&self, from: &Symbol, to: &Symbol) -> ValueSet {
        match self {
            ValueSet::Empty => ValueSet::Empty,
            ValueSet::Universal => ValueSet::Universal,
            ValueSet::Singleton(v) => {
                match v.as_ref() {
                    Value::Tuple(elems) => {
                        if !elems.is_empty() {
                            if let Value::Symbol(s) = &elems[0] {
                                if s == from {
                                    let mut new_elems = elems.clone();
                                    new_elems[0] = Value::Symbol(to.clone());
                                    return ValueSet::Singleton(Box::new(Value::Tuple(new_elems)));
                                }
                            }
                        }
                        ValueSet::Singleton(v.clone())
                    }
                    _ => ValueSet::Singleton(v.clone()),
                }
            }
            ValueSet::Union(a, b) => ValueSet::Union(
                Box::new(a.rename_prefix(from, to)),
                Box::new(b.rename_prefix(from, to)),
            ),
            ValueSet::Intersection(a, b) => ValueSet::Intersection(
                Box::new(a.rename_prefix(from, to)),
                Box::new(b.rename_prefix(from, to)),
            ),
            ValueSet::Complement(a) => ValueSet::Complement(Box::new(a.rename_prefix(from, to))),
            ValueSet::Tuple(sets) => {
                if !sets.is_empty() {
                    let mut new_sets = sets.clone();
                    new_sets[0] = Self::replace_symbol(&new_sets[0], from, to);
                    ValueSet::Tuple(new_sets)
                } else {
                    ValueSet::Tuple(sets.clone())
                }
            }
        }
    }

    fn replace_symbol(set: &ValueSet, from: &Symbol, to: &Symbol) -> ValueSet {
        match set {
            ValueSet::Singleton(v) => {
                if let Value::Symbol(s) = v.as_ref() {
                    if s == from {
                        return ValueSet::Singleton(Box::new(Value::Symbol(to.clone())));
                    }
                }
                ValueSet::Singleton(v.clone())
            }
            ValueSet::Union(a, b) => ValueSet::Union(
                Box::new(Self::replace_symbol(a, from, to)),
                Box::new(Self::replace_symbol(b, from, to)),
            ),
            ValueSet::Intersection(a, b) => ValueSet::Intersection(
                Box::new(Self::replace_symbol(a, from, to)),
                Box::new(Self::replace_symbol(b, from, to)),
            ),
            ValueSet::Complement(a) => ValueSet::Complement(Box::new(Self::replace_symbol(a, from, to))),
            other => other.clone(),
        }
    }

    /// Convert the ValueSet into Disjunctive Normal Form (DNF).
    ///
    /// The resulting ValueSet is guaranteed to satisfy the following structural properties:
    /// 1. **Unions at the Top Level**: `Union` nodes are pulled to the top level of the AST and
    ///    never nested inside `Intersection`, `Complement`, or `Tuple` nodes.
    /// 2. **Simplification of Singletons**: Any `Singleton` containing a tuple value is rewritten
    ///    to a `Tuple` of singletons. Intersections involving `Singleton` are fully evaluated to
    ///    either `Singleton` or `Empty`.
    /// 3. **Tuple-Tuple/Complement Simplification**: Intersections between `Tuple` and `Tuple`
    ///    are merged element-wise. Intersections between `Tuple` and `Complement(Tuple)` are
    ///    distributed into a union of tuples.
    /// 4. **No Complex Intersections**: Any remaining `Intersection` node can only consist of
    ///    `Complement` sets of atomic values (which are infinite and yield `ChooseResult::Unknown`).
    /// 5. **Empty and Universal Boundaries**: Set operations involving `Empty` or `Universal` are
    ///    fully simplified (e.g. union with `Empty`, intersection with `Universal`, or any `Tuple`
    ///    containing `Empty` simplifies to `Empty`).
    pub fn to_dnf(&self) -> ValueSet {
        match self {
            ValueSet::Empty => ValueSet::Empty,
            ValueSet::Universal => ValueSet::Universal,
            ValueSet::Singleton(v) => {
                match v.as_ref() {
                    Value::Tuple(elements) => {
                        // Rewrite Singleton of Tuple to Tuple of Singletons
                        ValueSet::Tuple(
                            elements.iter().map(|e| {
                                ValueSet::Singleton(Box::new(e.clone()))
                            }).collect()
                        ).to_dnf()
                    }
                    _ => ValueSet::Singleton(v.clone())
                }
            }
            ValueSet::Complement(a) => {
                match a.as_ref() {
                    ValueSet::Empty => ValueSet::Universal,
                    ValueSet::Universal => ValueSet::Empty,
                    ValueSet::Complement(x) => x.to_dnf(),
                    ValueSet::Union(x, y) => {
                        // De Morgan: (X U Y)^c = X^c n Y^c
                        ValueSet::Intersection(
                            Box::new(ValueSet::Complement(x.clone())),
                            Box::new(ValueSet::Complement(y.clone()))
                        ).to_dnf()
                    }
                    ValueSet::Intersection(x, y) => {
                        // De Morgan: (X n Y)^c = X^c U Y^c
                        ValueSet::Union(
                            Box::new(ValueSet::Complement(x.clone())),
                            Box::new(ValueSet::Complement(y.clone()))
                        ).to_dnf()
                    }
                    _ => {
                        let a_dnf = a.to_dnf();
                        if a_dnf != **a {
                            ValueSet::Complement(Box::new(a_dnf)).to_dnf()
                        } else {
                            ValueSet::Complement(Box::new(a_dnf))
                        }
                    }
                }
            }
            ValueSet::Union(a, b) => {
                let a_dnf = a.to_dnf();
                let b_dnf = b.to_dnf();
                match (&a_dnf, &b_dnf) {
                    (ValueSet::Empty, other) => other.clone(),
                    (other, ValueSet::Empty) => other.clone(),
                    (ValueSet::Universal, _) | (_, ValueSet::Universal) => ValueSet::Universal,
                    _ => ValueSet::Union(Box::new(a_dnf), Box::new(b_dnf)),
                }
            }
            ValueSet::Intersection(a, b) => {
                let a_dnf = a.to_dnf();
                let b_dnf = b.to_dnf();
                match (&a_dnf, &b_dnf) {
                    (ValueSet::Empty, _) | (_, ValueSet::Empty) => ValueSet::Empty,
                    (ValueSet::Universal, other) => other.clone(),
                    (other, ValueSet::Universal) => other.clone(),
                    (ValueSet::Union(x, y), _) => {
                        // (X U Y) n B = (X n B) U (Y n B)
                        ValueSet::Union(
                            Box::new(ValueSet::Intersection(x.clone(), Box::new(b_dnf.clone()))),
                            Box::new(ValueSet::Intersection(y.clone(), Box::new(b_dnf.clone())))
                        ).to_dnf()
                    }
                    (_, ValueSet::Union(x, y)) => {
                        // A n (X U Y) = (A n X) U (A n Y)
                        ValueSet::Union(
                            Box::new(ValueSet::Intersection(Box::new(a_dnf.clone()), x.clone())),
                            Box::new(ValueSet::Intersection(Box::new(a_dnf.clone()), y.clone()))
                        ).to_dnf()
                    }
                    (ValueSet::Singleton(v), other) => {
                        if other.contains(v) {
                            ValueSet::Singleton(v.clone())
                        } else {
                            ValueSet::Empty
                        }
                    }
                    (other, ValueSet::Singleton(v)) => {
                        if other.contains(v) {
                            ValueSet::Singleton(v.clone())
                        } else {
                            ValueSet::Empty
                        }
                    }
                    (ValueSet::Tuple(sets_a), ValueSet::Tuple(sets_b)) => {
                        if sets_a.len() != sets_b.len() {
                            ValueSet::Empty
                        } else {
                            let merged: Vec<ValueSet> = sets_a.iter().zip(sets_b.iter()).map(|(sa, sb)| {
                                ValueSet::Intersection(Box::new(sa.clone()), Box::new(sb.clone()))
                            }).collect();
                            ValueSet::Tuple(merged).to_dnf()
                        }
                    }
                    (ValueSet::Tuple(sets_t), ValueSet::Complement(inner)) => {
                        match inner.as_ref() {
                            ValueSet::Tuple(sets_c) => {
                                if sets_t.len() != sets_c.len() {
                                    a_dnf.clone()
                                } else {
                                    let k = sets_t.len();
                                    let mut union_res = ValueSet::Empty;
                                    for i in 0..k {
                                        let mut new_sets = sets_t.clone();
                                        new_sets[i] = ValueSet::Intersection(
                                            Box::new(sets_t[i].clone()),
                                            Box::new(ValueSet::Complement(Box::new(sets_c[i].clone())))
                                        );
                                        let term = ValueSet::Tuple(new_sets);
                                        if union_res == ValueSet::Empty {
                                            union_res = term;
                                        } else {
                                            union_res = ValueSet::Union(Box::new(union_res), Box::new(term));
                                        }
                                    }
                                    union_res.to_dnf()
                                }
                            }
                            _ => a_dnf.clone(),
                        }
                    }
                    (ValueSet::Complement(inner), ValueSet::Tuple(sets_t)) => {
                        match inner.as_ref() {
                            ValueSet::Tuple(sets_c) => {
                                if sets_t.len() != sets_c.len() {
                                    b_dnf.clone()
                                } else {
                                    let k = sets_t.len();
                                    let mut union_res = ValueSet::Empty;
                                    for i in 0..k {
                                        let mut new_sets = sets_t.clone();
                                        new_sets[i] = ValueSet::Intersection(
                                            Box::new(sets_t[i].clone()),
                                            Box::new(ValueSet::Complement(Box::new(sets_c[i].clone())))
                                        );
                                        let term = ValueSet::Tuple(new_sets);
                                        if union_res == ValueSet::Empty {
                                            union_res = term;
                                        } else {
                                            union_res = ValueSet::Union(Box::new(union_res), Box::new(term));
                                        }
                                    }
                                    union_res.to_dnf()
                                }
                            }
                            _ => b_dnf.clone(),
                        }
                    }
                    (ValueSet::Tuple(_), ValueSet::Intersection(x, y)) => {
                        ValueSet::Intersection(
                            Box::new(ValueSet::Intersection(Box::new(a_dnf.clone()), x.clone()).to_dnf()),
                            y.clone()
                        ).to_dnf()
                    }
                    (ValueSet::Intersection(x, y), ValueSet::Tuple(_)) => {
                        ValueSet::Intersection(
                            Box::new(ValueSet::Intersection(x.clone(), Box::new(b_dnf.clone())).to_dnf()),
                            y.clone()
                        ).to_dnf()
                    }
                    _ => ValueSet::Intersection(Box::new(a_dnf), Box::new(b_dnf)),
                }
            }
            ValueSet::Tuple(sets) => {
                let sets_dnf: Vec<ValueSet> = sets.iter().map(|s| s.to_dnf()).collect();
                if sets_dnf.iter().any(|s| matches!(s, ValueSet::Empty)) {
                    ValueSet::Empty
                } else {
                    ValueSet::Tuple(sets_dnf)
                }
            }
        }
    }

    /// Choose an arbitrary element from the set, if one exists.
    pub fn choose(&self) -> ChooseResult {
        let dnf = self.to_dnf();
        dnf.choose_dnf()
    }

    fn choose_dnf(&self) -> ChooseResult {
        // Note: We must ensure that we never return ChooseResult::Empty on a non-empty set.
        // If the set could be non-empty but we are unable to determine an element (e.g. because it is infinite or complex),
        // we must return ChooseResult::Unknown.
        match self {
            ValueSet::Empty => ChooseResult::Empty,
            ValueSet::Universal => ChooseResult::Found(Value::Tuple(vec![])),
            ValueSet::Singleton(v) => ChooseResult::Found(*v.clone()),
            ValueSet::Complement(_) => ChooseResult::Unknown,
            ValueSet::Union(a, b) => {
                match a.choose_dnf() {
                    ChooseResult::Found(v) => ChooseResult::Found(v),
                    ChooseResult::Unknown => {
                        match b.choose_dnf() {
                            ChooseResult::Found(v) => ChooseResult::Found(v),
                            _ => ChooseResult::Unknown,
                        }
                    }
                    ChooseResult::Empty => b.choose_dnf(),
                }
            }
            ValueSet::Intersection(_, _) => ChooseResult::Unknown,
            ValueSet::Tuple(sets) => {
                let mut elements = Vec::new();
                for set in sets {
                    match set.choose_dnf() {
                        ChooseResult::Found(elem) => elements.push(elem),
                        ChooseResult::Unknown => return ChooseResult::Unknown,
                        ChooseResult::Empty => return ChooseResult::Empty,
                    }
                }
                ChooseResult::Found(Value::Tuple(elements))
            }
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
            ValueSet::Complement(a) => write!(f, "complement({})", a),
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

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Debug for ValueSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

