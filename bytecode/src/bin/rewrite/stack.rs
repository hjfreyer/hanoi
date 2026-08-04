//! A symbolic view of the stack, for the listing.
//!
//! The rules deliberately know nothing about values. Reading a derivation by
//! hand is a different job: the whole question is which slots hold the same
//! value and which hold a known one, and a column of depths cannot say.
//!
//! This is an abstract interpretation that gives every slot a **term**, with
//! structural equality standing for "provably the same value". Two slots
//! showing the same label hold the same value; a slot showing a literal holds
//! that literal. Nothing here is consulted by a rule — it runs after the
//! rewriting is done and only decides what to print, which is why it is allowed
//! to be as clever as it likes without touching the governing invariant.
//!
//! Being an over-approximation in one direction is fine and being one in the
//! other is not: two slots that *are* equal may show different labels, because
//! the interpretation lost track. Two slots showing the same label are equal.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

use bytecode::{Instruction, Value};

use crate::arity::node_arity;
use crate::ir::Node;
use crate::program::Program;

/// What a stack slot holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Term {
    /// A literal.
    Const(ConstKey),
    /// One of the sentence's own inputs, counted from the top of the stack.
    In(usize),
    /// A value nothing here can see into: a call's result, or a slot where two
    /// branch arms disagreed.
    Opaque(usize),
    /// Element `i` of a tuple that was never built here.
    Proj(usize, Rc<Term>),
    /// A tuple built here. Index 0 first.
    Tup(Vec<Rc<Term>>),
    /// The result of an operator, by name.
    App(&'static str, Vec<Rc<Term>>),
}

/// `Value` is not `Hash`/`Eq` (floats), so terms key on its rendering instead.
/// Two constants are the same term exactly when they print the same, which for
/// everything but floats is the same as being the same value — and floats are
/// where equality is not identity anyway.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ConstKey(String, bool);

impl ConstKey {
    fn new(v: &Value) -> Self {
        ConstKey(render_value(v), is_float_free(v))
    }
    /// Whether substituting this constant for an equal one is invisible.
    fn exact(&self) -> bool {
        self.1
    }
}

fn is_float_free(v: &Value) -> bool {
    match v {
        Value::Float(_) => false,
        Value::Tuple(es) => es.iter().all(is_float_free),
        _ => true,
    }
}

fn render_value(v: &Value) -> String {
    match v {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Float(f) => format!("{}", f),
        Value::Symbol(s) => format!("'{}", short_symbol(&s.name)),
        Value::Tuple(es) => {
            let mut out = String::from("(");
            for (i, e) in es.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let _ = write!(out, "{}", render_value(e));
            }
            out.push(')');
            out
        }
    }
}

/// Symbol descriptions are sentences ("Customer is idle"); a listing needs a
/// word. The last one is the distinguishing one in every case in the corpus.
fn short_symbol(name: &str) -> String {
    let tail = name.rsplit("::").next().unwrap_or(name);
    match tail.rsplit(' ').next() {
        Some(w) if !w.is_empty() => w.to_string(),
        _ => tail.to_string(),
    }
}

/// The stack, or `None` where it stopped being knowable.
pub(crate) type Stack = Option<Vec<Rc<Term>>>;

/// Hands out `Opaque` identities for values this interpretation cannot see.
pub(crate) struct Fresh(usize);

impl Fresh {
    pub(crate) fn new() -> Self {
        Fresh(0)
    }
    fn next(&mut self) -> Rc<Term> {
        self.0 += 1;
        Rc::new(Term::Opaque(self.0))
    }
}

/// The entry stack of a sentence taking `inputs` values, top last.
///
/// Numbered from the top, so `in0` is the argument of a `1 -> 1` function.
pub(crate) fn entry(inputs: i64, _fresh: &mut Fresh) -> Stack {
    let n = usize::try_from(inputs).ok()?;
    Some((0..n).rev().map(|i| Rc::new(Term::In(i))).collect())
}

fn constant(v: &Value) -> Rc<Term> {
    Rc::new(Term::Const(ConstKey::new(v)))
}

fn as_const(t: &Term) -> Option<&ConstKey> {
    match t {
        Term::Const(k) => Some(k),
        _ => None,
    }
}

/// Runs one node, returning the stack after it.
pub(crate) fn step(prog: &Program, stack: Stack, node: &Node, fresh: &mut Fresh) -> Stack {
    let mut s = stack?;
    match node {
        Node::Op(inst) => op(inst, &mut s, fresh).then_some(s),
        Node::Dip { depth, body, .. } => {
            if *depth > s.len() {
                return None;
            }
            let hidden = s.split_off(s.len() - depth);
            let mut lower = run(prog, Some(s), body, fresh)?;
            lower.extend(hidden);
            Some(lower)
        }
        // Where the arms disagree, the depth still follows from the arity but
        // the identities do not, so the slots become fresh rather than wrong.
        Node::Branch { .. } | Node::Call { .. } => {
            let (n, m) = node_arity(prog, node)?;
            let n = usize::try_from(n).ok()?;
            let m = usize::try_from(m).ok()?;
            if n > s.len() {
                return None;
            }
            s.truncate(s.len() - n);
            s.extend((0..m).map(|_| fresh.next()));
            Some(s)
        }
    }
}

/// Runs a whole sequence.
pub(crate) fn run(prog: &Program, stack: Stack, nodes: &[Node], fresh: &mut Fresh) -> Stack {
    let mut s = stack;
    for node in nodes {
        s = step(prog, s, node, fresh);
        s.as_ref()?;
    }
    s
}

/// Applies one instruction. Returns false where the effect is not knowable.
fn op(inst: &Instruction, s: &mut Vec<Rc<Term>>, fresh: &mut Fresh) -> bool {
    macro_rules! pop {
        () => {
            match s.pop() {
                Some(t) => t,
                None => return false,
            }
        };
    }

    match inst {
        Instruction::Push(v) => s.push(constant(v)),
        Instruction::Drop => {
            pop!();
        }
        Instruction::Pick(d) => {
            if *d >= s.len() {
                return false;
            }
            s.push(s[s.len() - 1 - d].clone());
        }
        Instruction::Roll(d) => {
            if *d >= s.len() {
                return false;
            }
            let t = s.remove(s.len() - 1 - d);
            s.push(t);
        }
        Instruction::Tuple(n) => {
            if *n > s.len() {
                return false;
            }
            // `tuple n` makes the top element index 0.
            let mut es: Vec<_> = s.split_off(s.len() - n);
            es.reverse();
            s.push(Rc::new(Term::Tup(es)));
        }
        Instruction::Untuple(n) => {
            let t = pop!();
            match &*t {
                Term::Tup(es) if es.len() == *n => {
                    // Index 0 ends on top, so push in reverse.
                    for e in es.iter().rev() {
                        s.push(e.clone());
                    }
                    // A tuple this wide always comes apart, and the view knows
                    // it, so the flag is a literal rather than an opaque slot.
                    s.push(Rc::new(Term::Const(ConstKey::new(&Value::Bool(true)))));
                }
                _ => {
                    for i in (0..*n).rev() {
                        s.push(Rc::new(Term::Proj(i, t.clone())));
                    }
                    s.push(fresh.next());
                }
            }
        }
        Instruction::Equal => {
            let b = pop!();
            let a = pop!();
            s.push(equality(&a, &b));
        }
        Instruction::Not
        | Instruction::IsInt
        | Instruction::IsBool
        | Instruction::IsFloat
        | Instruction::IsSymbol
        | Instruction::IsTuple => {
            let a = pop!();
            s.push(unary(inst, &a));
        }
        Instruction::Negate | Instruction::TupleLength | Instruction::SymbolLen => {
            let a = pop!();
            s.push(unary(inst, &a));
            s.push(fresh.next());
        }
        Instruction::And | Instruction::Or => {
            let b = pop!();
            let a = pop!();
            s.push(Rc::new(Term::App(op_name(inst), vec![a, b])));
        }
        Instruction::Greater
        | Instruction::Less
        | Instruction::Add
        | Instruction::Subtract
        | Instruction::Multiply
        | Instruction::Divide
        | Instruction::Modulo
        | Instruction::SymbolCharAt => {
            let b = pop!();
            let a = pop!();
            s.push(Rc::new(Term::App(op_name(inst), vec![a, b])));
            // Whether it succeeded is not something the view tracks, so the
            // flag is a fresh opaque slot rather than a claim.
            s.push(fresh.next());
        }
        Instruction::Print => {
            let a = pop!();
            s.push(a);
        }
        Instruction::Assert => {
            pop!();
        }
        Instruction::AssertEqual => {
            pop!();
            pop!();
        }
        // Panic ends the run; Dip/Branch never reach here.
        _ => {
            let _ = fresh;
            return false;
        }
    }
    true
}

/// `equal` is where the whole point of this view lives: two slots holding the
/// same term hold the same value, so the comparison is already decided.
fn equality(a: &Rc<Term>, b: &Rc<Term>) -> Rc<Term> {
    let decided = |v: bool| Rc::new(Term::Const(ConstKey::new(&Value::Bool(v))));
    match (as_const(a), as_const(b)) {
        (Some(x), Some(y)) if x.exact() && y.exact() => return decided(x == y),
        _ => {}
    }
    // Same term, so the same value — unless it is a float, where equality is
    // not identity and the term says nothing about which.
    if a == b && exact(a) {
        return decided(true);
    }
    Rc::new(Term::App("==", vec![a.clone(), b.clone()]))
}

/// Whether a term's identity pins its value, floats being the exception.
fn exact(t: &Term) -> bool {
    match t {
        Term::Const(k) => k.exact(),
        Term::Tup(es) => es.iter().all(|e| exact(e)),
        // An input, an opaque value or a projection could be a float, but it is *the same*
        // float on both sides, and `equal` on one value with itself is true for
        // every value the VM has. NaN would break this; the VM has no way to
        // make one.
        _ => true,
    }
}

fn unary(inst: &Instruction, a: &Rc<Term>) -> Rc<Term> {
    let name = op_name(inst);
    if let Some(k) = as_const(a) {
        if let Some(v) = fold_unary(inst, k) {
            return Rc::new(Term::Const(ConstKey::new(&v)));
        }
    }
    // A tuple built here answers `is_tuple` and `tuple_length` on sight.
    if let Term::Tup(es) = &**a {
        match inst {
            Instruction::IsTuple => return Rc::new(Term::Const(ConstKey::new(&Value::Bool(true)))),
            Instruction::TupleLength => {
                return Rc::new(Term::Const(ConstKey::new(&Value::Int(es.len() as i64))))
            }
            Instruction::IsInt
            | Instruction::IsBool
            | Instruction::IsFloat
            | Instruction::IsSymbol => {
                return Rc::new(Term::Const(ConstKey::new(&Value::Bool(false))))
            }
            _ => {}
        }
    }
    Rc::new(Term::App(name, vec![a.clone()]))
}

fn fold_unary(inst: &Instruction, k: &ConstKey) -> Option<Value> {
    // The rendering is the key, so read the shape back off it. Cheap and
    // enough for a listing: only the `is_*` family is asked.
    let r = &k.0;
    let is = |b: bool| Some(Value::Bool(b));
    let bool_lit = r == "true" || r == "false";
    let sym = r.starts_with('\'');
    let tup = r.starts_with('(');
    let float = !k.exact();
    let int = !bool_lit && !sym && !tup && !float && r.parse::<i64>().is_ok();
    match inst {
        Instruction::IsBool => is(bool_lit),
        Instruction::IsInt => is(int),
        Instruction::IsFloat => is(float),
        Instruction::IsSymbol => is(sym),
        Instruction::IsTuple => is(tup),
        Instruction::Not if bool_lit => is(r == "false"),
        _ => None,
    }
}

fn op_name(inst: &Instruction) -> &'static str {
    match inst {
        Instruction::Not => "not",
        Instruction::Negate => "neg",
        Instruction::IsInt => "is_int",
        Instruction::IsBool => "is_bool",
        Instruction::IsFloat => "is_float",
        Instruction::IsSymbol => "is_symbol",
        Instruction::IsTuple => "is_tuple",
        Instruction::TupleLength => "len",
        Instruction::SymbolLen => "sym_len",
        Instruction::Greater => ">",
        Instruction::Less => "<",
        Instruction::Add => "+",
        Instruction::Subtract => "-",
        Instruction::Multiply => "*",
        Instruction::Divide => "/",
        Instruction::Modulo => "%",
        Instruction::And => "&&",
        Instruction::Or => "||",
        Instruction::SymbolCharAt => "char_at",
        _ => "?",
    }
}

// ---------------------------------------------------------------------------
// Naming
// ---------------------------------------------------------------------------

/// Gives every term a short, stable label.
///
/// Stability across the whole listing is the point: a slot that keeps its
/// letter from one line to the next is a slot that kept its value, and that is
/// exactly what a reader is trying to follow.
pub(crate) struct Names {
    labels: HashMap<Rc<Term>, String>,
    next: usize,
    /// Label, then what it stands for, in the order the labels were handed out.
    legend: Vec<(String, String)>,
}

impl Names {
    pub(crate) fn new() -> Self {
        Names {
            labels: HashMap::new(),
            next: 0,
            legend: Vec::new(),
        }
    }

    /// A literal shows itself; anything else gets a letter.
    pub(crate) fn label(&mut self, t: &Rc<Term>) -> String {
        if let Term::Const(k) = &**t {
            return k.0.clone();
        }
        if let Some(l) = self.labels.get(t) {
            return l.clone();
        }
        let l = letter(self.next);
        self.next += 1;
        self.labels.insert(t.clone(), l.clone());
        let desc = self.describe(t);
        self.legend.push((l.clone(), desc));
        l
    }

    /// One level deep, in terms of the labels of the parts. Deeper than that
    /// and the legend stops being readable — the parts have their own entries.
    fn describe(&mut self, t: &Rc<Term>) -> String {
        match &**t {
            Term::In(i) => format!("input {}", i),
            Term::Opaque(_) => "?".to_string(),
            Term::Const(k) => k.0.clone(),
            Term::Proj(i, inner) => format!("{}.{}", self.label(inner), i),
            Term::Tup(es) => {
                let parts: Vec<_> = es.iter().map(|e| self.label(e)).collect();
                format!("({})", parts.join(", "))
            }
            Term::App(name, args) => {
                let parts: Vec<_> = args.iter().map(|a| self.label(a)).collect();
                if args.len() == 2 && !name.chars().next().is_some_and(char::is_alphabetic) {
                    format!("{} {} {}", parts[0], name, parts[1])
                } else {
                    format!("{}({})", name, parts.join(", "))
                }
            }
        }
    }

    pub(crate) fn legend(&self) -> &[(String, String)] {
        &self.legend
    }

    /// Renders a stack bottom-to-top, so the top sits next to the instruction.
    pub(crate) fn render(&mut self, stack: &Stack, width: usize) -> String {
        let Some(s) = stack else {
            return "?".to_string();
        };
        if s.is_empty() {
            return "·".to_string();
        }
        let labels: Vec<_> = s.iter().map(|t| self.label(t)).collect();
        let mut out = labels.join(" ");
        if out.chars().count() > width {
            // Keep the top, which is the end.
            let keep: String = out.chars().rev().take(width - 2).collect();
            out = format!("…{}", keep.chars().rev().collect::<String>());
        }
        out
    }
}

fn letter(n: usize) -> String {
    let a = (b'a' + (n % 26) as u8) as char;
    if n < 26 {
        a.to_string()
    } else {
        format!("{}{}", a, n / 26)
    }
}
