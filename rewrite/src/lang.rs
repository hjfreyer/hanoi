//! The Rust the engine's program calls into, and the terms that go in and out.
//!
//! [`rules.egg`](../rules.egg) is the engine: the datatype, the facts, and
//! every law, written out. This module is everything that cannot be said
//! there, and nothing else — no schema is generated here, so the two are read
//! side by side rather than one reconstructed from the other.
//!
//! Three things:
//!
//! - [`Session`] interns the two kinds of leaf data an e-node cannot carry —
//!   pushed [`Value`]s and called sentences — so every node is a constructor
//!   over `i64`.
//! - [`vocabulary`] gives the engine the `Lits` sort and the handful of
//!   primitives the rules call: the session's leaf data, and the interpreter
//!   itself for `vm-eval`. It runs before the program is read, because a rule
//!   cannot mention what does not exist yet.
//! - The conversions: a [`Term`] into the s-expression the engine reads, a
//!   template into the pattern `solve` matches, and an extracted term back
//!   into a [`Term`]. [`node_name`] and [`prim_of`] are the two halves of the
//!   one table those need, and the tests below hold that table — and the
//!   arities, codomains and opcodes `rules.egg` states — to the instruction
//!   set they mirror.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::{Arc, Mutex};

use bytecode::{Instruction, Library, SentenceIndex, Value};
use egglog::ast::Expr;
use egglog::prelude::{RustSpan, Span, span};
use egglog::sort::{Presort, S, VecContainer, VecSort};
use egglog::{EGraph, TermDag, TermId, add_primitive};

use crate::term::{Arity, Prim, Term};

/// The sort every program node has.
pub const SORT: &str = "Hana";

/// The sort of a run of interned values — `rules.egg` uses it but does not
/// declare it, because [`vm-eval`](vocabulary) has to name it before the
/// program is read.
const LITS: &str = "Lits";

/// The program the engine runs.
pub fn program() -> &'static str {
    include_str!("rules.egg")
}

// ---- the session ------------------------------------------------------------

/// The leaf data an e-node cannot carry: pushed values and called sentences.
///
/// A [`Value`] is neither `Ord` nor `Hash`, and a call's arity is a fact about
/// the library rather than about the node, so both are interned here and the
/// nodes carry indices. One session per proving run, shared with the
/// primitives the rules call — `vm-eval` interns the values a fold answers
/// with, so the table grows during saturation and every reader must see the
/// same one.
#[derive(Debug, Clone)]
pub struct Session(Arc<Mutex<Interned>>);

#[derive(Debug, Default)]
struct Interned {
    values: Vec<Value>,
    /// Keyed by debug rendering, `Value` not being hashable. Two values with
    /// one rendering are one value: `Debug` shows ids and text in full.
    value_keys: HashMap<String, usize>,
    calls: Vec<(SentenceIndex, Arity)>,
    call_keys: HashMap<SentenceIndex, usize>,
}

/// The index of `()`, which `eval-nothing` pushes.
pub const UNIT_VALUE: usize = 0;
/// The index of `true`, which `bool-result` pushes.
pub const TRUE_VALUE: usize = 1;

impl Default for Session {
    /// A session with the two constants `rules.egg` names already interned.
    ///
    /// The rule file writes them as `(let $unit-value 0)` and `(let
    /// $true-value 1)` — a static file cannot ask what a table will answer —
    /// so interning them first is what makes those indices right.
    fn default() -> Self {
        let session = Session(Arc::new(Mutex::new(Interned::default())));
        session.value(&Value::unit());
        session.value(&Value::Bool(true));
        session
    }
}

impl Session {
    /// Interns a value, answering the index that names it.
    pub fn value(&self, v: &Value) -> usize {
        let mut inner = self.0.lock().expect("the session is never poisoned");
        let key = format!("{:?}", v);
        if let Some(&i) = inner.value_keys.get(&key) {
            return i;
        }
        let i = inner.values.len();
        inner.values.push(v.clone());
        inner.value_keys.insert(key, i);
        i
    }

    /// The value a `(Push i)` leaf pushes.
    pub fn value_of(&self, i: usize) -> Value {
        self.0.lock().expect("the session is never poisoned").values[i].clone()
    }

    /// Interns a call, answering the index that names it.
    pub fn call(&self, target: SentenceIndex, arity: Arity) -> usize {
        let mut inner = self.0.lock().expect("the session is never poisoned");
        if let Some(&i) = inner.call_keys.get(&target) {
            return i;
        }
        let i = inner.calls.len();
        inner.calls.push((target, arity));
        inner.call_keys.insert(target, i);
        i
    }

    /// The sentence a `(Call i)` leaf calls, and its arity.
    pub fn call_of(&self, i: usize) -> (SentenceIndex, Arity) {
        self.0.lock().expect("the session is never poisoned").calls[i]
    }
}

// ---- the node table ---------------------------------------------------------

/// The node a prim is spelled with in `rules.egg`.
///
/// The other half of this table is the `datatype` at the top of that file, and
/// `the_program_declares_every_node` holds the two together.
pub fn node_name(prim: &Prim) -> &'static str {
    match prim {
        Prim::Push(_) => "Push",
        Prim::Swap => "Swap",
        Prim::Equal => "Equal",
        Prim::Greater => "Greater",
        Prim::Less => "Less",
        Prim::Add => "Add",
        Prim::Subtract => "Subtract",
        Prim::Multiply => "Multiply",
        Prim::Divide => "Divide",
        Prim::Modulo => "Modulo",
        Prim::Not => "Not",
        Prim::Negate => "Negate",
        Prim::And => "And",
        Prim::Or => "Or",
        Prim::Tuple(_) => "Tuple",
        Prim::Untuple(_) => "Untuple",
        Prim::ConstStringLen => "ConstStringLen",
        Prim::ConstStringCharAt => "ConstStringCharAt",
        Prim::IsInt => "IsInt",
        Prim::IsBool => "IsBool",
        Prim::IsConstString => "IsConstString",
        Prim::IsSymbol => "IsSymbol",
        Prim::IsTuple => "IsTuple",
        Prim::TupleLength => "TupleLength",
        Prim::AsBool => "AsBool",
        Prim::AsInt => "AsInt",
        Prim::AsTuple(_) => "AsTuple",
    }
}

/// The prim a node stands for, given the width it carries — `0` where it
/// carries none.
///
/// `Push` is absent on purpose: its leaf names a value rather than a width, so
/// the two readers that meet one ([`term_of`] and `vm-eval`) handle it before
/// asking here.
pub fn prim_of(node: &str, width: usize) -> Option<Prim> {
    Some(match node {
        "Swap" => Prim::Swap,
        "Equal" => Prim::Equal,
        "Greater" => Prim::Greater,
        "Less" => Prim::Less,
        "Add" => Prim::Add,
        "Subtract" => Prim::Subtract,
        "Multiply" => Prim::Multiply,
        "Divide" => Prim::Divide,
        "Modulo" => Prim::Modulo,
        "Not" => Prim::Not,
        "Negate" => Prim::Negate,
        "And" => Prim::And,
        "Or" => Prim::Or,
        "Tuple" => Prim::Tuple(width),
        "Untuple" => Prim::Untuple(width),
        "ConstStringLen" => Prim::ConstStringLen,
        "ConstStringCharAt" => Prim::ConstStringCharAt,
        "IsInt" => Prim::IsInt,
        "IsBool" => Prim::IsBool,
        "IsConstString" => Prim::IsConstString,
        "IsSymbol" => Prim::IsSymbol,
        "IsTuple" => Prim::IsTuple,
        "TupleLength" => Prim::TupleLength,
        "AsBool" => Prim::AsBool,
        "AsInt" => Prim::AsInt,
        "AsTuple" => Prim::AsTuple(width),
        _ => return None,
    })
}

// ---- the vocabulary ---------------------------------------------------------

/// Gives the engine the sort and the primitives `rules.egg` calls.
///
/// Runs before the program is read: a rule cannot mention a primitive that
/// does not exist yet, and `Lits` has to be a sort before `vm-eval` can be
/// typed against it.
///
/// `vm-eval` is the one that matters. Folding owes the interpreter exact
/// agreement, junk included, so a literal window is run on the real `vm`
/// rather than on a second implementation that could drift — see
/// [`run_window`].
pub fn vocabulary(egraph: &mut EGraph, session: &Session) {
    let lits = VecSort::make_sort(
        egraph.type_info(),
        LITS.to_string(),
        &[Expr::Var(span!(), "i64".to_string())],
    )
    .expect("a vec of i64 is a sort");
    egraph
        .add_arcsort(lits.clone(), span!())
        .expect("nothing else declares Lits");

    add_primitive!(egraph, "value-is-bool" = {session.clone(): Session} |i: i64| -?> () {
        matches!(self.ctx.value_of(i as usize), bytecode::Value::Bool(_)).then_some(())
    });
    add_primitive!(egraph, "value-truthy" = {session.clone(): Session} |i: i64| -?> () {
        self.ctx.value_of(i as usize).truthy().then_some(())
    });
    add_primitive!(egraph, "value-falsy" = {session.clone(): Session} |i: i64| -?> () {
        (!self.ctx.value_of(i as usize).truthy()).then_some(())
    });
    add_primitive!(egraph, "call-inputs" = {session.clone(): Session} |i: i64| -> i64 {
        self.ctx.call_of(i as usize).1.inputs as i64
    });
    add_primitive!(egraph, "call-outputs" = {session.clone(): Session} |i: i64| -> i64 {
        self.ctx.call_of(i as usize).1.outputs as i64
    });
    add_primitive!(
        egraph,
        "vm-eval" = {session.clone(): Session}
        |vs: @VecContainer (lits), op: S, width: i64, k: i64| -?> @VecContainer (lits) {
            {
                let values: Vec<usize> = vs
                    .data
                    .iter()
                    .map(|v| exec_state.base_values().unwrap::<i64>(*v) as usize)
                    .collect();
                fold_window(&self.ctx, &values, op.as_str(), width as usize, k as usize).map(
                    |out| VecContainer {
                        do_rebuild: false,
                        data: out
                            .into_iter()
                            .map(|i| exec_state.base_values().get::<i64>(i as i64))
                            .collect(),
                    },
                )
            }
        }
    );
}

/// A literal window feeding an instruction, folded to the pushes of what the
/// machine answers.
///
/// `vs` is the run of interned values the window pushes and `k` the
/// operation's input count, so the operands are the top `k` of them and
/// everything below passes through untouched. `None` is the fold declining —
/// too few operands, or the machine would not run.
fn fold_window(
    session: &Session,
    vs: &[usize],
    op: &str,
    width: usize,
    k: usize,
) -> Option<Vec<usize>> {
    if vs.len() < k {
        return None;
    }
    let prim = prim_of(op, width).expect("only an instruction leaf carries an opcode");
    let operands: Vec<Value> = vs[vs.len() - k..]
        .iter()
        .map(|i| session.value_of(*i))
        .collect();
    let answers = run_window(&operands, &prim.to_instruction())?;
    let mut result: Vec<usize> = vs[..vs.len() - k].to_vec();
    for v in &answers {
        result.push(session.value(v));
    }
    Some(result)
}

/// Runs one instruction on the operands it wants, on the machine itself.
///
/// The fold owes the interpreter exact agreement, junk included, so there is
/// no second implementation to drift: a scratch library holding
/// `push v̄ ; inst` is executed and the stack it leaves is the answer.
fn run_window(operands: &[Value], inst: &Instruction) -> Option<Vec<Value>> {
    let mut library = Library::new();
    let mut sentence: Vec<Instruction> = operands
        .iter()
        .map(|v| Instruction::Push(v.clone()))
        .collect();
    sentence.push(inst.clone());
    library.sentences.push(sentence);
    let start = library.sentences.first_key().expect("one sentence");
    let mut vm = vm::VM::new(library);
    vm.execute(start).ok()?;
    Some(vm.stack().to_vec())
}

// ---- terms in and out -------------------------------------------------------

/// The s-expression a term denotes, interning its leaves as it goes.
pub fn sexp_of(term: &Term, session: &Session) -> String {
    let mut out = String::new();
    write_sexp(term, session, &None, &mut out);
    out
}

/// The query `solve` matches: the term's s-expression with each hole — a call
/// to one of the listed indices, which no sentence has — written as the
/// pattern variable its name spells.
pub fn pattern_of(
    term: &Term,
    holes: &HashMap<SentenceIndex, String>,
    session: &Session,
) -> String {
    let mut out = String::new();
    write_sexp(term, session, &Some(holes), &mut out);
    out
}

fn write_sexp(
    term: &Term,
    session: &Session,
    holes: &Option<&HashMap<SentenceIndex, String>>,
    out: &mut String,
) {
    if let Term::Call { target, .. } = term
        && let Some(holes) = holes
        && let Some(var) = holes.get(target)
    {
        out.push_str(var);
        return;
    }
    match term {
        Term::Id(n) => {
            let _ = write!(out, "(Id {})", n);
        }
        Term::Drop(n) => {
            let _ = write!(out, "(Drop {})", n);
        }
        Term::Copy(n) => {
            let _ = write!(out, "(Copy {})", n);
        }
        Term::Call { target, arity } => {
            let _ = write!(out, "(Call {})", session.call(*target, *arity));
        }
        Term::Op(Prim::Push(v)) => {
            let _ = write!(out, "(Push {})", session.value(v));
        }
        Term::Op(prim) => {
            let name = node_name(prim);
            match prim {
                Prim::Tuple(n) | Prim::Untuple(n) | Prim::AsTuple(n) => {
                    let _ = write!(out, "({} {})", name, n);
                }
                _ => {
                    let _ = write!(out, "({})", name);
                }
            }
        }
        Term::Compose(a, b) => {
            out.push_str("(Seq ");
            write_sexp(a, session, holes, out);
            out.push(' ');
            write_sexp(b, session, holes, out);
            out.push(')');
        }
        Term::Par(a, b) => {
            out.push_str("(Par ");
            write_sexp(a, session, holes, out);
            out.push(' ');
            write_sexp(b, session, holes, out);
            out.push(')');
        }
        Term::Branch { if_true, if_false } => {
            out.push_str("(Branch ");
            write_sexp(if_true, session, holes, out);
            out.push(' ');
            write_sexp(if_false, session, holes, out);
            out.push(')');
        }
    }
}

/// Reads an extracted term back into a [`Term`], for printing what an e-class
/// holds in the spelling the rest of the tool uses.
///
/// Built from the raw variants rather than the checking constructors: an
/// extracted term came out of an e-graph whose program already asserted every
/// arity, and a residual printer must not panic on the thing it exists to
/// show.
pub fn term_of(dag: &TermDag, id: TermId, session: &Session) -> Term {
    use egglog::Term as ETerm;
    let int = |dag: &TermDag, id: TermId| -> usize {
        match dag.get(id) {
            ETerm::Lit(egglog::ast::Literal::Int(n)) => *n as usize,
            other => panic!("a width argument that is not an integer: {:?}", other),
        }
    };
    let (head, args) = match dag.get(id) {
        ETerm::App(head, args) => (head.as_str(), args.as_slice()),
        other => panic!("an extracted node that is not an application: {:?}", other),
    };
    match head {
        "Seq" => Term::Compose(
            Box::new(term_of(dag, args[0], session)),
            Box::new(term_of(dag, args[1], session)),
        ),
        "Par" => Term::Par(
            Box::new(term_of(dag, args[0], session)),
            Box::new(term_of(dag, args[1], session)),
        ),
        "Branch" => Term::Branch {
            if_true: Box::new(term_of(dag, args[0], session)),
            if_false: Box::new(term_of(dag, args[1], session)),
        },
        "Id" => Term::Id(int(dag, args[0])),
        "Drop" => Term::Drop(int(dag, args[0])),
        "Copy" => Term::Copy(int(dag, args[0])),
        "Push" => Term::Op(Prim::Push(session.value_of(int(dag, args[0])))),
        "Call" => {
            let (target, arity) = session.call_of(int(dag, args[0]));
            Term::Call { target, arity }
        }
        name => {
            let width = args.first().map(|a| int(dag, *a)).unwrap_or(0);
            Term::Op(
                prim_of(name, width).unwrap_or_else(|| {
                    panic!("an extracted node the model does not have: {}", name)
                }),
            )
        }
    }
}

// ---- reading the program ----------------------------------------------------

/// The program's top-level forms, each with the label written above it.
///
/// Both rule files use one convention — a comment line holding a single word,
/// immediately above the form it names — and this is what reads it: the
/// firings report turns a rule's text back into its label this way, and the
/// tests below walk the same list to hold the file to the instruction set.
pub fn forms(program: &str) -> Vec<(Option<String>, String)> {
    let mut out = Vec::new();
    let mut label: Option<String> = None;
    let mut form = String::new();
    let mut depth = 0isize;
    for line in program.lines() {
        let code = line.split(';').next().unwrap_or("");
        if depth == 0 && code.trim().is_empty() {
            let comment = line.trim().trim_start_matches(';').trim();
            // A label is one word. Prose and the `==== heading ====` rules are
            // not, and neither is a blank line.
            if comment.split_whitespace().count() == 1 {
                label = Some(comment.to_string());
            }
            continue;
        }
        form.push_str(code);
        form.push(' ');
        depth += code.matches('(').count() as isize;
        depth -= code.matches(')').count() as isize;
        if depth <= 0 {
            out.push((label.take(), flatten(&form)));
            form.clear();
            depth = 0;
        }
    }
    out
}

/// A form's text in the one spelling both sides can be compared in: no
/// whitespace except between atoms, so the file's layout and egglog's printing
/// of the same rule come out identical.
pub fn flatten(text: &str) -> String {
    let mut out = String::new();
    let mut spaced = false;
    for c in text.chars() {
        if c.is_whitespace() {
            spaced = true;
            continue;
        }
        if spaced && !out.is_empty() && c != ')' && !out.ends_with('(') {
            out.push(' ');
        }
        spaced = false;
        out.push(c);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value `(set (<field> t) …)` gives, out of a flattened rule.
    fn field(rule: &str, name: &str) -> Option<String> {
        let head = format!("(set ({} t) ", name);
        let rest = &rule[rule.find(&head)? + head.len()..];
        let end = rest.find(')')?;
        Some(rest[..end].to_string())
    }

    /// The `leaf-*` rules of `rules.egg`, keyed by the node each is about.
    fn leaf_rules() -> HashMap<String, String> {
        forms(program())
            .into_iter()
            .filter_map(|(label, rule)| {
                let label = label?;
                let node = label.strip_prefix("leaf-")?;
                rule.contains("(set (opcode t) ")
                    .then(|| (node.to_string(), rule))
            })
            .collect()
    }

    #[test]
    fn the_node_table_round_trips() {
        for prim in Prim::all() {
            if matches!(prim, Prim::Push(_)) {
                continue;
            }
            let width = match &prim {
                Prim::Tuple(n) | Prim::Untuple(n) | Prim::AsTuple(n) => *n,
                _ => 0,
            };
            assert_eq!(
                prim_of(node_name(&prim), width),
                Some(prim.clone()),
                "{}",
                prim
            );
        }
        assert_eq!(prim_of("Nonesuch", 0), None);
    }

    #[test]
    fn the_program_declares_every_node() {
        let datatype = forms(program())
            .into_iter()
            .map(|(_, form)| form)
            .find(|form| form.starts_with("(datatype Hana"))
            .expect("the program declares the model");
        for node in ["Seq", "Par", "Branch", "Id", "Drop", "Copy", "Push", "Call"] {
            assert!(
                datatype.contains(&format!("({} ", node)),
                "{} is not a node",
                node
            );
        }
        for prim in Prim::all() {
            let name = node_name(&prim);
            let carries_width = matches!(
                prim,
                Prim::Tuple(_) | Prim::Untuple(_) | Prim::AsTuple(_) | Prim::Push(_)
            );
            let declared = if carries_width {
                format!("({} i64)", name)
            } else {
                format!("({})", name)
            };
            assert!(datatype.contains(&declared), "{} is not a node", prim);
        }
    }

    #[test]
    fn the_program_agrees_with_the_instruction_set() {
        // Arity, codomain, commutativity and the name a fold runs an
        // instruction under are all written out in `rules.egg`. This is what
        // says they are the instruction set's — a wrong `yields-bool` entry is
        // a soundness bug rather than an inaccurate comment.
        let rules = leaf_rules();
        for prim in Prim::all() {
            if matches!(prim, Prim::Push(_)) {
                continue;
            }
            let node = node_name(&prim);
            let rule = rules
                .get(&node.to_lowercase())
                .unwrap_or_else(|| panic!("{} has no leaf rule", prim));
            let inst = prim.to_instruction();

            assert_eq!(
                field(rule, "opcode").as_deref(),
                Some(format!("\"{}\"", node).as_str()),
                "{} folds under the wrong name",
                prim
            );
            assert_eq!(
                rule.contains("(yields-bool t)"),
                inst.yields_bool(),
                "{} disagrees with Instruction::yields_bool",
                prim
            );
            assert_eq!(
                rule.contains("(commutative t)"),
                inst.commutative(),
                "{} disagrees with Instruction::commutative",
                prim
            );

            // A width-carrying leaf states its arity in terms of the width
            // it carries; everything else states two numbers.
            let arity = prim.arity();
            let (inputs, outputs, width) = match &prim {
                Prim::Tuple(_) => ("?n".to_string(), "1".to_string(), "?n"),
                Prim::Untuple(_) => ("1".to_string(), "?n".to_string(), "?n"),
                Prim::AsTuple(_) => ("1".to_string(), "1".to_string(), "?n"),
                _ => (arity.inputs.to_string(), arity.outputs.to_string(), "0"),
            };
            assert_eq!(
                field(rule, "arity-in").as_deref(),
                Some(inputs.as_str()),
                "{}",
                prim
            );
            assert_eq!(
                field(rule, "arity-out").as_deref(),
                Some(outputs.as_str()),
                "{}",
                prim
            );
            assert_eq!(field(rule, "opwidth").as_deref(), Some(width), "{}", prim);
        }
        assert_eq!(
            rules.len(),
            Prim::all().len() - 1,
            "a leaf rule names something that is not a prim"
        );
    }

    #[test]
    fn the_constants_are_interned_first() {
        // `rules.egg` writes these indices as literals, so a session that did
        // not intern them first would have `eval-nothing` push a value that
        // belongs to some other goal.
        let session = Session::default();
        assert_eq!(session.value_of(UNIT_VALUE), Value::unit());
        assert_eq!(session.value_of(TRUE_VALUE), Value::Bool(true));
        assert!(program().contains(&format!("(let $unit-value {})", UNIT_VALUE)));
        assert!(program().contains(&format!("(let $true-value {})", TRUE_VALUE)));
    }

    #[test]
    fn interning_a_value_twice_answers_the_same_index() {
        let session = Session::default();
        let a = session.value(&Value::Int(7));
        let b = session.value(&Value::Int(7));
        assert_eq!(a, b);
        assert_eq!(session.value_of(a), Value::Int(7));
        assert_ne!(a, session.value(&Value::Int(8)));
    }

    #[test]
    fn a_term_becomes_the_s_expression_the_engine_reads() {
        let session = Session::default();
        let term = Term::pad_compose(
            Term::op(Prim::Push(Value::Int(1))),
            Term::op(Prim::Push(Value::Int(2))),
        );
        assert_eq!(
            sexp_of(&term, &session),
            "(Seq (Push 2) (Par (Id 1) (Push 3)))"
        );
    }

    #[test]
    fn a_form_and_its_label_come_off_the_program() {
        let read =
            forms(";; a-label\n(rule (x)\n      (y))\n\n;; prose that is not a label\n(other)\n");
        assert_eq!(
            read,
            vec![
                (Some("a-label".to_string()), "(rule (x) (y))".to_string()),
                (None, "(other)".to_string()),
            ]
        );
    }
}
