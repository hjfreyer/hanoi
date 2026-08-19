//! [`Term`] as an egglog datatype, plus the per-class facts saturation reads.
//!
//! The e-graph is where a goal's two sides go to meet, so this module is the
//! seam between the term model and the search. Four things live here:
//!
//! - [`Session`] interns the two kinds of leaf data an e-node cannot carry
//!   directly — pushed [`Value`]s and called sentences — so every node is a
//!   constructor over `i64`.
//! - [`schema`] is the egglog program that declares the datatype, the tables
//!   the facts live in, and the rules that compute them. The per-instruction
//!   part of it is *generated* from [`Prim`], so the node set, the arities,
//!   the `yields_bool` list and the opcode table cannot drift from the term
//!   model they mirror.
//! - [`primitives`] registers the handful of egglog primitives the rules use
//!   to reach back into Rust: the session's leaf data, and the interpreter
//!   itself for `vm-eval`.
//! - The conversions: a [`Term`] into the s-expression egglog reads, a
//!   template into the query `solve` matches, and an extracted term back into
//!   a [`Term`].
//!
//! The load-bearing fact is the **arity**. Every rule instance over this model
//! is arity-preserving — padding made that so — which means arity is invariant
//! across an e-class. `arity-in` and `arity-out` are therefore declared
//! `:no-merge`: uniting two classes with different stack effects is an illegal
//! merge, and egglog refuses it on the spot rather than producing a wrong
//! proof.
//!
//! # The node spellings
//!
//! egglog's parser takes `;` for a comment and already owns `*`, so compose
//! and par are spelled `Seq` and `Par` rather than the `;` and `*` the algebra
//! and the residual printer use. Everything else is the mnemonic in
//! CamelCase. Widths ride *inside* the node — `(Id 3)`, not egg's `id@3` —
//! which is the whole reason the rules can be written down: a width is an
//! ordinary pattern variable, so `(rewrite (Par (Id ?n) (Id ?m)) (Id (+ ?n
//! ?m)))` is a rule rather than a Rust closure.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::{Arc, Mutex};

use bytecode::{Instruction, Library, SentenceIndex, Value};
use egglog::sort::VecContainer;
use egglog::{EGraph, TermDag, TermId, add_primitive};

use crate::term::{Arity, Prim, Term};

/// The sort every program node has.
pub const SORT: &str = "Hana";

/// The leaf data an e-node cannot carry: pushed values and called sentences.
///
/// A [`Value`] is neither `Ord` nor `Hash`, and a call's arity is a fact about
/// the library rather than about the node, so both are interned here and the
/// nodes carry indices. One session per proving run, shared with the
/// primitives the rules call — `vm-eval` interns the values a fold answers
/// with, so the table grows during saturation and every reader must see the
/// same one.
#[derive(Debug, Clone, Default)]
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

// ---- the node set -----------------------------------------------------------

/// The name a prim's node is spelled with, and the tag `opcode` gives it.
///
/// Both come from [`Prim::all`], so a prim added to the term model shows up
/// here without anything else being edited — and `every_prim_has_a_node`
/// holds the two to each other.
fn prim_nodes() -> Vec<(Prim, String)> {
    Prim::all()
        .into_iter()
        .filter(|p| !matches!(p, Prim::Push(_)))
        .map(|p| {
            let name = node_name(&p);
            (p, name)
        })
        .collect()
}

/// `const_string_char_at` as `ConstStringCharAt`.
fn camel(mnemonic: &str) -> String {
    mnemonic
        .split('_')
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().chain(chars).collect::<String>(),
                None => String::new(),
            }
        })
        .collect()
}

/// The prim a `(opcode, opwidth)` pair names, for [`fold_window`].
fn prim_of(code: usize, width: usize) -> Prim {
    match prim_nodes()[code].0.clone() {
        Prim::Tuple(_) => Prim::Tuple(width),
        Prim::Untuple(_) => Prim::Untuple(width),
        Prim::AsTuple(_) => Prim::AsTuple(width),
        other => other,
    }
}

/// Whether a prim carries a width, and so takes its node's argument.
fn width_carrying(p: &Prim) -> bool {
    matches!(p, Prim::Tuple(_) | Prim::Untuple(_) | Prim::AsTuple(_))
}

// ---- the schema -------------------------------------------------------------

/// The egglog program that declares the model: the datatype, the tables the
/// facts live in, and the helper constructors the rules build with.
/// [`analysis`] holds the rules that fill them.
///
/// What each fact means, and why it is here:
///
/// - `arity-in` / `arity-out` are the invariant — see the module docs.
/// - `is-id` / `is-drop` / `is-copy` say the class contains that structural
///   leaf, or something the facts compose to one. The width is the arity's.
/// - `yields-bool` says whatever this computes leaves a `Bool` on top. The
///   [`Instruction::yields_bool`] list, lifted through composition.
/// - `literal` says the class behaves as `id(inputs) * (push v1 ; … ; push
///   vk)` — it pushes exactly those values over an untouched stack. What the
///   folding rules read.
/// - `opcode` / `opwidth` name the instruction a leaf stands for, for the one
///   rule that runs the machine. `Push` deliberately has none: a literal is
///   not an operation to fold.
///
/// All of them but the arities are one-way: absent means "not known to hold",
/// never "known not to". egglog has no negation, so a rule cannot ask whether
/// a fact is *missing*, and none of the rules in `rules.egg` needs to.
///
/// The declarations are separated from the rules because the order matters:
/// everything a rule *mentions* has to exist before it is read, and the rules
/// mention primitives that only exist once [`primitives`] has run. So a
/// session declares, registers, and only then states.
pub fn declarations() -> String {
    let mut s = String::new();

    // ---- the datatype ------------------------------------------------------
    s.push_str("(datatype Hana\n");
    s.push_str("  (Seq Hana Hana)\n");
    s.push_str("  (Par Hana Hana)\n");
    s.push_str("  (Branch Hana Hana)\n");
    s.push_str("  (Id i64)\n");
    s.push_str("  (Drop i64)\n");
    s.push_str("  (Copy i64)\n");
    s.push_str("  (Push i64)\n");
    s.push_str("  (Call i64)\n");
    for (prim, name) in prim_nodes() {
        if width_carrying(&prim) {
            let _ = writeln!(s, "  ({} i64)", name);
        } else {
            let _ = writeln!(s, "  ({})", name);
        }
    }
    s.push_str(")\n\n");

    // ---- the facts ---------------------------------------------------------
    s.push_str(
        r#"(sort Lits (Vec i64))

(function arity-in  (Hana) i64 :no-merge)
(function arity-out (Hana) i64 :no-merge)
(relation is-id (Hana))
(relation is-drop (Hana))
(relation is-copy (Hana))
(relation yields-bool (Hana))
(function literal (Hana) Lits :merge old)
(function opcode  (Hana) i64 :no-merge)
(function opwidth (Hana) i64 :no-merge)
(relation commutative (Hana))

; The canonical spelling of "push these values over `n` untouched ones" — the
; shape `lower` gives a run of pushes, and the shape whose class the literal
; fact recognizes. A rule builds one by naming the run; these unfold it. The
; helpers are unextractable so a residual is printed in the term language and
; never in the scaffolding that built it.
(constructor lit-chain (i64 Lits) Hana :unextractable)
(constructor lit-step  (i64 i64)  Hana :unextractable)
(constructor top-drop  (i64)      Hana :unextractable)


"#,
    );

    s
}

/// The rules that compute the facts [`declarations`] made room for.
///
/// Run after [`primitives`], which is what the leaf rules call to read the
/// session and the codomain tables.
pub fn analysis() -> String {
    let mut s = String::new();
    s.push_str(
        r#"; lit-chain-empty
(rule ((= c (lit-chain ?n ?vs)) (= 0 (vec-length ?vs)))
      ((union c (Id ?n))))
; lit-chain-step
(rule ((= c (lit-chain ?n ?vs))
       (= ?k (- (vec-length ?vs) 1))
       (>= ?k 0)
       (= ?v (vec-get ?vs ?k)))
      ((union c (Seq (lit-chain ?n (vec-remove ?vs ?k)) (lit-step (+ ?n ?k) ?v)))))
; lit-step-bare
(rule ((= s (lit-step 0 ?v)))            ((union s (Push ?v))))
; lit-step-framed
(rule ((= s (lit-step ?d ?v)) (> ?d 0))  ((union s (Par (Id ?d) (Push ?v)))))

; `drop(1)` at the top of `n + 1` values: the deep `n` pass through.
; top-drop-bare
(rule ((= d (top-drop 0)))            ((union d (Drop 1))))
; top-drop-framed
(rule ((= d (top-drop ?n)) (> ?n 0))  ((union d (Par (Id ?n) (Drop 1)))))

; ---- the structural leaves --------------------------------------------------
; leaf-id
(rule ((= t (Id ?n)))
      ((set (arity-in t) ?n) (set (arity-out t) ?n) (is-id t)
       ; `id(0)` pushes nothing over an untouched stack, which is what lets a
       ; literal prefix compose past it.
       (set (literal t) (vec-of))))
; leaf-drop
(rule ((= t (Drop ?n)))
      ((set (arity-in t) ?n) (set (arity-out t) 0) (is-drop t)))
; leaf-copy
(rule ((= t (Copy ?n)))
      ((set (arity-in t) ?n) (set (arity-out t) (+ ?n ?n)) (is-copy t)))
; leaf-push
(rule ((= t (Push ?v)))
      ((set (arity-in t) 0) (set (arity-out t) 1) (set (literal t) (vec-of ?v))))
; leaf-push-bool
(rule ((= t (Push ?v)) (value-is-bool ?v))
      ((yields-bool t)))
; leaf-call
(rule ((= t (Call ?c)))
      ((set (arity-in t) (call-inputs ?c)) (set (arity-out t) (call-outputs ?c))))

; ---- compose ----------------------------------------------------------------
; compose-arity
(rule ((= t (Seq ?a ?b)) (= ?i (arity-in ?a)) (= ?o (arity-out ?b)))
      ((set (arity-in t) ?i) (set (arity-out t) ?o)))
; compose-meets
(rule ((= t (Seq ?a ?b)) (= ?o (arity-out ?a)) (= ?i (arity-in ?b)) (!= ?o ?i))
      ((panic "a compose node whose halves do not meet")))
; compose-is-id
(rule ((= t (Seq ?a ?b)) (is-id ?a) (is-id ?b))     ((is-id t)))
; compose-is-drop-after-id
(rule ((= t (Seq ?a ?b)) (is-id ?a) (is-drop ?b))   ((is-drop t)))
; compose-is-drop
(rule ((= t (Seq ?a ?b)) (is-drop ?a) (is-drop ?b)) ((is-drop t)))
; compose-is-drop-then-nothing
(rule ((= t (Seq ?a ?b)) (is-drop ?a) (is-id ?b) (= 0 (arity-in ?b)))
      ((is-drop t)))
; compose-is-copy
(rule ((= t (Seq ?a ?b)) (is-copy ?a) (is-id ?b))   ((is-copy t)))
; The suffix answers for the top of the stack; an identity suffix leaves the
; prefix's answer standing. The second rule is the other side of that `if`:
; egglog cannot ask whether the suffix is *not* an identity, and it need not —
; an identity class that also yielded a bool would be claiming its own input is
; always a `Bool`, which no sound union can put there.
; compose-bool-through-id
(rule ((= t (Seq ?a ?b)) (is-id ?b) (> (arity-in ?b) 0) (yields-bool ?a))
      ((yields-bool t)))
; compose-bool
(rule ((= t (Seq ?a ?b)) (yields-bool ?b))
      ((yields-bool t)))
; Both halves push over an untouched stack, so the pushes concatenate: the
; suffix's land on top.
; compose-literal
(rule ((= t (Seq ?a ?b)) (= ?xs (literal ?a)) (= ?ys (literal ?b)))
      ((set (literal t) (vec-append ?xs ?ys))))

; ---- par --------------------------------------------------------------------
; par-arity
(rule ((= t (Par ?a ?b))
       (= ?ai (arity-in ?a)) (= ?bi (arity-in ?b))
       (= ?ao (arity-out ?a)) (= ?bo (arity-out ?b)))
      ((set (arity-in t) (+ ?ai ?bi)) (set (arity-out t) (+ ?ao ?bo))))
; par-is-id
(rule ((= t (Par ?a ?b)) (is-id ?a) (is-id ?b))     ((is-id t)))
; par-is-drop
(rule ((= t (Par ?a ?b)) (is-drop ?a) (is-drop ?b)) ((is-drop t)))
; par-bool-top
(rule ((= t (Par ?a ?b)) (> (arity-out ?b) 0) (yields-bool ?b)) ((yields-bool t)))
; par-bool-deep
(rule ((= t (Par ?a ?b)) (= 0 (arity-out ?b)) (yields-bool ?a)) ((yields-bool t)))
; The deep side's pushes land under the shallow side's inputs, so this is a
; literal only when the shallow side reads nothing (its pushes then sit
; directly on the deep side's) or the deep side pushes nothing at all.
; par-literal
(rule ((= t (Par ?a ?b)) (= ?xs (literal ?a)) (= ?ys (literal ?b)) (= 0 (arity-in ?b)))
      ((set (literal t) (vec-append ?xs ?ys))))
; par-literal-over-id
(rule ((= t (Par ?a ?b)) (is-id ?a) (= ?ys (literal ?b)))
      ((set (literal t) ?ys)))

; ---- branch -----------------------------------------------------------------
; branch-arity
(rule ((= t (Branch ?x ?y)) (= ?i (arity-in ?x)) (= ?o (arity-out ?x)))
      ((set (arity-in t) (+ ?i 1)) (set (arity-out t) ?o)))
; branch-arms-agree-in
(rule ((= t (Branch ?x ?y)) (= ?p (arity-in ?x)) (= ?q (arity-in ?y)) (!= ?p ?q))
      ((panic "a branch node whose arms differ")))
; branch-arms-agree-out
(rule ((= t (Branch ?x ?y)) (= ?p (arity-out ?x)) (= ?q (arity-out ?y)) (!= ?p ?q))
      ((panic "a branch node whose arms differ")))
; branch-bool
(rule ((= t (Branch ?x ?y)) (> (arity-out ?x) 0) (yields-bool ?x) (yields-bool ?y))
      ((yields-bool t)))

"#,
    );

    // ---- the instruction leaves -------------------------------------------
    // Arity, codomain and commutativity all come off the term model and the
    // instruction set, so this table is derived rather than written.
    s.push_str("; ---- the instruction leaves ---------------------------------\n");
    for (code, (prim, name)) in prim_nodes().into_iter().enumerate() {
        let arity = prim.arity();
        let inst = prim.to_instruction();
        let (head, width) = if width_carrying(&prim) {
            (format!("({} ?n)", name), "?n".to_string())
        } else {
            (format!("({})", name), "0".to_string())
        };
        let (inputs, outputs) = if width_carrying(&prim) {
            match prim {
                Prim::Tuple(_) => ("?n".to_string(), "1".to_string()),
                Prim::Untuple(_) => ("1".to_string(), "?n".to_string()),
                _ => ("1".to_string(), "1".to_string()),
            }
        } else {
            (arity.inputs.to_string(), arity.outputs.to_string())
        };
        let mut actions = format!(
            "(set (arity-in t) {}) (set (arity-out t) {})\n       (set (opcode t) {}) (set (opwidth t) {})",
            inputs, outputs, code, width
        );
        if inst.yields_bool() {
            actions.push_str(" (yields-bool t)");
        }
        if inst.commutative() {
            actions.push_str(" (commutative t)");
        }
        let _ = writeln!(
            s,
            "; leaf-{}\n(rule ((= t {}))\n      ({}))",
            name.to_lowercase(),
            head,
            actions
        );
    }
    s
}

/// The globals `rules.egg` names: the two constants a rule pushes out of thin
/// air, interned so their indices are the session's.
pub fn constants(session: &Session) -> String {
    format!(
        "(let $unit-value {})\n(let $true-value {})\n",
        session.value(&Value::unit()),
        session.value(&Value::Bool(true))
    )
}

// ---- the primitives ---------------------------------------------------------

/// Registers the primitives the rules use to reach back into Rust: the
/// session's leaf data, and the interpreter itself.
///
/// `vm-eval` is the one that matters. Folding owes the interpreter exact
/// agreement, junk included, so a literal window is run on the real `vm`
/// rather than on a second implementation that could drift — see
/// [`run_window`].
pub fn primitives(egraph: &mut EGraph, session: &Session) {
    let lits = egraph
        .get_sort_by_name("Lits")
        .expect("the schema declares Lits")
        .clone();

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
        |vs: @VecContainer (lits), code: i64, width: i64, k: i64| -?> @VecContainer (lits) {
            {
                let values: Vec<usize> = vs
                    .data
                    .iter()
                    .map(|v| exec_state.base_values().unwrap::<i64>(*v) as usize)
                    .collect();
                fold_window(&self.ctx, &values, code as usize, width as usize, k as usize).map(
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
/// `vs` is the run of interned values the window pushes and `k` the operation's
/// input count, so the operands are the top `k` of them and everything below
/// passes through untouched. `None` is the fold declining — too few operands,
/// or the machine would not run.
fn fold_window(
    session: &Session,
    vs: &[usize],
    code: usize,
    width: usize,
    k: usize,
) -> Option<Vec<usize>> {
    if vs.len() < k {
        return None;
    }
    let operands: Vec<Value> = vs[vs.len() - k..]
        .iter()
        .map(|i| session.value_of(*i))
        .collect();
    let answers = run_window(&operands, &prim_of(code, width).to_instruction())?;
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

/// The node a prim is spelled with: its mnemonic, in CamelCase.
///
/// An instruction prints its operands too — `tuple 3` — and a node's width is
/// its argument rather than part of its name, so only the head is taken.
fn node_name(prim: &Prim) -> String {
    let printed = prim.to_instruction().to_string();
    camel(printed.split_whitespace().next().expect("a mnemonic"))
}

/// Reads an extracted term back into a [`Term`], for printing what an e-class
/// holds in the spelling the rest of the tool uses.
///
/// Built from the raw variants rather than the checking constructors: an
/// extracted term came out of an e-graph whose schema already asserted every
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
            let width = args.first().map(|a| int(dag, *a));
            let prim = prim_nodes()
                .into_iter()
                .find(|(_, n)| n == name)
                .map(|(p, _)| p)
                .unwrap_or_else(|| panic!("an extracted node the model does not have: {}", name));
            Term::Op(match (prim, width) {
                (Prim::Tuple(_), Some(n)) => Prim::Tuple(n),
                (Prim::Untuple(_), Some(n)) => Prim::Untuple(n),
                (Prim::AsTuple(_), Some(n)) => Prim::AsTuple(n),
                (other, _) => other,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_prim_has_a_node_the_schema_declares() {
        let schema = declarations();
        for prim in Prim::all() {
            if matches!(prim, Prim::Push(_)) {
                continue;
            }
            let name = node_name(&prim);
            assert!(
                schema.contains(&format!("({} i64)", name))
                    || schema.contains(&format!("({})\n", name)),
                "{} has no node",
                prim
            );
        }
    }

    #[test]
    fn an_opcode_names_the_prim_it_came_from() {
        for (code, (prim, _)) in prim_nodes().into_iter().enumerate() {
            let width = match &prim {
                Prim::Tuple(n) | Prim::Untuple(n) | Prim::AsTuple(n) => *n,
                _ => 0,
            };
            assert_eq!(prim_of(code, width), prim);
        }
    }

    #[test]
    fn a_mnemonic_becomes_its_node_name() {
        assert_eq!(camel("const_string_char_at"), "ConstStringCharAt");
        assert_eq!(camel("swap"), "Swap");
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
            "(Seq (Push 0) (Par (Id 1) (Push 1)))"
        );
    }
}
