//! The case-tree normal form: symbolic evaluation as a decision procedure.
//!
//! [docs/algebra.md](../../docs/algebra.md) promises this module twice over.
//! In the free cartesian category a branch-free morphism `n -> m` **is** an
//! m-tuple of first-order terms over n variables, so running a term on a
//! stack of variables and reading off what lands is a *complete* decision
//! procedure for layer 1: two branch-free terms are equal under the
//! copy/drop/swap/frame laws iff symbolic evaluation answers the same tuple.
//! Branches extend the answer to a **case tree** — the ADHS shape — with the
//! condition evaluated symbolically and both arms taken; that extension is
//! sound but no longer complete (independent branches commute, and this
//! normal form does not see it), which is exactly the layer-2 hardness the
//! docs predict.
//!
//! What evaluation gets for free, and the rule each freebie answers to:
//!
//! - copy/drop/swap/frame bureaucracy has no spelling at all — the whole of
//!   layer 1, `copy-nat` and `drop-nat` included, is absorbed by values
//!   being *values*;
//! - a zero-output computation vanishes (`drop-nat` at the codomain: the
//!   language is total and pure, so `X : n -> 0` is `drop(n)`);
//! - a literal window folds by running the machine itself ([`run_window`],
//!   shared with the `eval` rule so there is no second semantics);
//! - a branch on a literal takes its arm (`fold-branch`), a branch whose
//!   arms came out equal collapses (the branch-of-equal-arms lemma), a
//!   condition already tested on this path is decided (`retest-*`), and a
//!   value that tested `equal` to a literal *is* that literal in the then
//!   arm (`specialize-equal`);
//! - commutative operands sort (`commute`), `tuple n ; untuple n` cancels
//!   (`tuple-cancel`), `untuple n ; tuple n` reads back as the coercion
//!   (`untuple-retuple`), coercions idempote (`as-*-idem`), and a test of a
//!   `yields_bool` answer is `true` (`bool-result`).
//!
//! Calls stay opaque: a [`Term::Call`] is an uninterpreted operation, the
//! same stance the e-graph takes, so `inline` remains the step that spends a
//! definition.
//!
//! **Trust.** Nothing here produces a derivation. [`normalize`] is a second
//! judge of equality, held to the machine by [`run_window`] and to the rule
//! set by tests, and how much to lean on it is a per-proof choice: the
//! `norm` step uses it only to *find* a waypoint (the reified normal form,
//! [`reify`]) and makes the e-graph check both halves, while `norm_trusted`
//! closes on this module's word alone. See `docs/proving.md`.

use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use bytecode::{Instruction, Library, SentenceIndex, Value};

use crate::term::{Arity, Prim, Term};

/// A symbolic value: one thing on the stack, as a first-order term over the
/// program's inputs.
///
/// This is the normal form's whole vocabulary. `copy` is two `Rc`s to one
/// node, `drop` is a node nothing references, `swap` is the order of a
/// [`Nf::Leaf`] — the structural layer exists only as the *shape* of the
/// tuple, which is why tuples that match are programs that are equal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    /// Input `i`, counted from the deepest (0) upward.
    Var(usize),
    /// A literal the program pushed or folding produced.
    Lit(Value),
    /// A single-output operation applied to arguments, deepest first.
    App { op: Op, args: Vec<Rc<Val>> },
    /// Output `index` of a multi-output operation. The universal property of
    /// the product says `f = ⟨f;π₁, …, f;πₘ⟩`, so splitting a multi-output
    /// application into its projections loses nothing.
    Proj {
        index: usize,
        op: Op,
        args: Vec<Rc<Val>>,
    },
}

/// An operation a [`Val`] can apply: a primitive, or a call left opaque.
///
/// `push` and `swap` never appear — the first is a [`Val::Lit`], the second
/// is structure — and the arity on a call is carried for the same reason
/// [`Term::Call`] carries one: the normal form stays meaningful without a
/// library in hand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Prim(Prim),
    Call { target: SentenceIndex, arity: Arity },
}

impl Op {
    fn arity(&self) -> Arity {
        match self {
            Op::Prim(p) => p.arity(),
            Op::Call { arity, .. } => *arity,
        }
    }
}

/// The normal form: a case tree whose leaves are tuples of symbolic values.
///
/// A leaf holds the whole output stack, deepest first. A branch holds the
/// condition as a value and both arms; every leaf under one node has the
/// same width, because the term it came from had one arity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Nf {
    Leaf(Vec<Rc<Val>>),
    Branch {
        cond: Rc<Val>,
        if_true: Box<Nf>,
        if_false: Box<Nf>,
    },
}

/// The conditions the current path has already decided, outermost first.
type Path = Vec<(Rc<Val>, bool)>;

/// The normal form of a term: run it on a stack of variables and keep what
/// lands.
pub fn normalize(term: &Term) -> Nf {
    let stack: Vec<Rc<Val>> = (0..term.arity().inputs)
        .map(|i| Rc::new(Val::Var(i)))
        .collect();
    eval(term, stack, &mut Vec::new())
}

/// One term on one symbolic stack — exactly the term's inputs, deepest
/// first — under the conditions the path has decided.
fn eval(term: &Term, mut stack: Vec<Rc<Val>>, path: &mut Path) -> Nf {
    debug_assert_eq!(stack.len(), term.arity().inputs, "the caller cuts by arity");
    match term {
        Term::Id(_) => Nf::Leaf(stack),
        Term::Drop(_) => Nf::Leaf(Vec::new()),
        // Block-wise: `copy(2)` takes `[a, b]` to `[a, b, a, b]`.
        Term::Copy(_) => {
            let again = stack.clone();
            stack.extend(again);
            Nf::Leaf(stack)
        }
        Term::Op(Prim::Push(v)) => Nf::Leaf(vec![Rc::new(Val::Lit(v.clone()))]),
        Term::Op(Prim::Swap) => {
            stack.swap(0, 1);
            Nf::Leaf(stack)
        }
        Term::Op(prim) => Nf::Leaf(apply(&Op::Prim(prim.clone()), stack)),
        Term::Call { target, arity } => Nf::Leaf(apply(
            &Op::Call {
                target: *target,
                arity: *arity,
            },
            stack,
        )),
        Term::Compose(a, b) => {
            let first = eval(a, stack, path);
            graft(first, path, &mut |left, path| eval(b, left, path))
        }
        Term::Par(a, b) => {
            // The second argument gets the top; branches inside the deep
            // side fork first, which is the one ordering decision this
            // normal form makes for terms that run side by side.
            let top = stack.split_off(stack.len() - b.arity().inputs);
            let deep = eval(a, stack, path);
            graft(deep, path, &mut |left, path| {
                let above = eval(b, top.clone(), path);
                graft(above, path, &mut |right, _| {
                    let mut whole = left.clone();
                    whole.extend(right);
                    Nf::Leaf(whole)
                })
            })
        }
        Term::Branch { if_true, if_false } => {
            let cond = stack.pop().expect("a branch has its condition on top");
            branch_on(cond, stack, if_true, if_false, path)
        }
    }
}

/// Continues a computation under every leaf of an already-built tree,
/// keeping the path honest as it descends and re-collapsing arms that come
/// out equal.
fn graft(tree: Nf, path: &mut Path, then: &mut dyn FnMut(Vec<Rc<Val>>, &mut Path) -> Nf) -> Nf {
    match tree {
        Nf::Leaf(stack) => then(stack, path),
        Nf::Branch {
            cond,
            if_true,
            if_false,
        } => {
            path.push((cond.clone(), true));
            let t = graft(*if_true, path, then);
            path.pop();
            path.push((cond.clone(), false));
            let f = graft(*if_false, path, then);
            path.pop();
            mk_branch(cond, t, f)
        }
    }
}

/// A branch on a symbolic condition: decided if it can be, forked if not.
fn branch_on(
    cond: Rc<Val>,
    stack: Vec<Rc<Val>>,
    if_true: &Term,
    if_false: &Term,
    path: &mut Path,
) -> Nf {
    // `fold-branch`: a literal condition selects its arm.
    if let Val::Lit(v) = &*cond {
        let taken = if v.truthy() { if_true } else { if_false };
        return eval(taken, stack, path);
    }
    // `retest-*`: a condition this path already tested answers the same.
    if let Some(&(_, taken)) = path.iter().find(|(c, _)| *c == cond) {
        let arm = if taken { if_true } else { if_false };
        return eval(arm, stack, path);
    }
    // `specialize-equal`: inside the then arm, a value that tested `equal`
    // to a literal is that literal — `equal` is structural identity.
    let then_stack = specialize(&cond, &stack);
    path.push((cond.clone(), true));
    let t = eval(if_true, then_stack, path);
    path.pop();
    path.push((cond.clone(), false));
    let f = eval(if_false, stack, path);
    path.pop();
    mk_branch(cond, t, f)
}

/// A branch node, unless its arms came out equal — then the branch never
/// happened (the branch-of-equal-arms lemma, with the condition's work
/// vanishing by `drop-nat`).
fn mk_branch(cond: Rc<Val>, if_true: Nf, if_false: Nf) -> Nf {
    if if_true == if_false {
        return if_true;
    }
    Nf::Branch {
        cond,
        if_true: Box::new(if_true),
        if_false: Box::new(if_false),
    }
}

/// The then-arm's stack when the condition is `v = literal`: every
/// occurrence of `v` replaced by the literal it just proved to be.
fn specialize(cond: &Rc<Val>, stack: &[Rc<Val>]) -> Vec<Rc<Val>> {
    let Val::App {
        op: Op::Prim(Prim::Equal),
        args,
    } = &**cond
    else {
        return stack.to_vec();
    };
    let [a, b] = &args[..] else {
        return stack.to_vec();
    };
    let (from, to) = match (&**a, &**b) {
        (_, Val::Lit(_)) => (a, b),
        (Val::Lit(_), _) => (b, a),
        _ => return stack.to_vec(),
    };
    stack.iter().map(|v| subst(v, from, to)).collect()
}

/// `v` with every occurrence of `from` replaced by `to`, re-canonicalized on
/// the way back up — a substitution can complete a literal window, and the
/// rebuilt application must fold the way a fresh one would.
fn subst(v: &Rc<Val>, from: &Rc<Val>, to: &Rc<Val>) -> Rc<Val> {
    if v == from {
        return to.clone();
    }
    match &**v {
        Val::Var(_) | Val::Lit(_) => v.clone(),
        Val::App { op, args } => {
            let walked: Vec<Rc<Val>> = args.iter().map(|a| subst(a, from, to)).collect();
            if walked == *args {
                return v.clone();
            }
            let out = apply(op, walked);
            debug_assert_eq!(out.len(), 1, "an App is a single-output application");
            out.into_iter().next().expect("just asserted")
        }
        Val::Proj { index, op, args } => {
            let walked: Vec<Rc<Val>> = args.iter().map(|a| subst(a, from, to)).collect();
            if walked == *args {
                return v.clone();
            }
            apply(op, walked)[*index].clone()
        }
    }
}

/// One operation on its symbolic arguments: the outputs it leaves, folded as
/// far as the facts reach.
fn apply(op: &Op, args: Vec<Rc<Val>>) -> Vec<Rc<Val>> {
    let Arity { inputs, outputs } = op.arity();
    debug_assert_eq!(args.len(), inputs, "the caller cuts by arity");

    // `drop-nat` at the codomain: the language is total and pure, so a
    // computation that leaves nothing is nothing — its arguments' work
    // vanishes with it.
    if outputs == 0 {
        return Vec::new();
    }

    if let Op::Prim(prim) = op {
        // `eval`: an all-literal window runs on the machine itself, junk
        // semantics included, so folding cannot disagree with `vm`.
        let literals: Option<Vec<Value>> = args
            .iter()
            .map(|a| match &**a {
                Val::Lit(v) => Some(v.clone()),
                _ => None,
            })
            .collect();
        if let Some(operands) = literals
            && let Some(answers) = run_window(&operands, &prim.to_instruction())
        {
            debug_assert_eq!(answers.len(), outputs, "the machine honors the arity table");
            return answers.into_iter().map(|v| Rc::new(Val::Lit(v))).collect();
        }

        // `tuple-cancel`: taking apart what `tuple n` just built.
        if let Prim::Untuple(n) = prim
            && let Val::App {
                op: Op::Prim(Prim::Tuple(m)),
                args: elems,
            } = &*args[0]
            && m == n
        {
            return elems.clone();
        }

        // `untuple-retuple`: rebuilding what `untuple n` took apart is the
        // coercion, not the identity — the slots may have been junk-filled.
        if let Prim::Tuple(n) = prim
            && *n > 0
            && let Some(inner) = retupled(*n, &args)
        {
            return apply(&Op::Prim(Prim::AsTuple(*n)), vec![inner]);
        }

        // `as-*-idem`: coercing twice is coercing once.
        if idempotent_coercion(prim, &args) {
            return vec![args.into_iter().next().expect("a coercion has an argument")];
        }

        // `bool-result`: asking `is_bool` of an answer the instruction set
        // promises is a bool. The promise is measured by `vm`.
        if matches!(prim, Prim::IsBool)
            && let Val::App {
                op: Op::Prim(inner),
                ..
            } = &*args[0]
            && inner.to_instruction().yields_bool()
        {
            return vec![Rc::new(Val::Lit(Value::Bool(true)))];
        }

        // `commute`: a commutative operation's operands in one canonical
        // order, so `swap ; op` and `op` normalize alike.
        if prim.to_instruction().commutative() {
            let mut args = args;
            args.sort_by(|a, b| cmp_val(a, b));
            return build(op, args, outputs);
        }
    }

    build(op, args, outputs)
}

/// The symbolic application nothing folded: an `App`, or one `Proj` per
/// output.
fn build(op: &Op, args: Vec<Rc<Val>>, outputs: usize) -> Vec<Rc<Val>> {
    if outputs == 1 {
        return vec![Rc::new(Val::App {
            op: op.clone(),
            args,
        })];
    }
    (0..outputs)
        .map(|index| {
            Rc::new(Val::Proj {
                index,
                op: op.clone(),
                args: args.clone(),
            })
        })
        .collect()
}

/// The common argument under `args`, when they are exactly the outputs of
/// `untuple n` on it, in order.
fn retupled(n: usize, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    let inner = |arg: &Rc<Val>, want: usize| -> Option<Rc<Val>> {
        match &**arg {
            // `untuple 1` has one output, so it is an `App`, not a `Proj`.
            Val::App {
                op: Op::Prim(Prim::Untuple(m)),
                args: a,
            } if *m == n && want == 0 && n == 1 => Some(a[0].clone()),
            Val::Proj {
                index,
                op: Op::Prim(Prim::Untuple(m)),
                args: a,
            } if *m == n && *index == want => Some(a[0].clone()),
            _ => None,
        }
    };
    let first = inner(&args[0], 0)?;
    for (i, arg) in args.iter().enumerate().skip(1) {
        if inner(arg, i)? != first {
            return None;
        }
    }
    Some(first)
}

/// Whether this is a coercion applied to its own answer.
fn idempotent_coercion(prim: &Prim, args: &[Rc<Val>]) -> bool {
    let inner = match &*args[0] {
        Val::App {
            op: Op::Prim(p), ..
        } => p,
        _ => return false,
    };
    matches!(
        (prim, inner),
        (Prim::AsBool, Prim::AsBool) | (Prim::AsInt, Prim::AsInt)
    ) || matches!((prim, inner), (Prim::AsTuple(n), Prim::AsTuple(m)) if n == m)
}

// ---- ordering, for the one canonical choice sorting needs -------------------

/// A total order on values, consistent with equality (symbols compare by
/// `id`, the same field their equality reads). Only the *existence* of the
/// order matters — it is the tiebreak that makes commutative operands
/// canonical — so the ranking is arbitrary and stable.
fn cmp_val(a: &Val, b: &Val) -> Ordering {
    fn rank(v: &Val) -> u8 {
        match v {
            Val::Var(_) => 0,
            Val::Lit(_) => 1,
            Val::App { .. } => 2,
            Val::Proj { .. } => 3,
        }
    }
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (Val::Var(i), Val::Var(j)) => i.cmp(j),
        (Val::Lit(v), Val::Lit(w)) => cmp_value(v, w),
        (Val::App { op, args }, Val::App { op: oq, args: brgs }) => {
            cmp_op(op, oq).then_with(|| cmp_args(args, brgs))
        }
        (
            Val::Proj { index, op, args },
            Val::Proj {
                index: jndex,
                op: oq,
                args: brgs,
            },
        ) => cmp_op(op, oq)
            .then_with(|| cmp_args(args, brgs))
            .then_with(|| index.cmp(jndex)),
        _ => unreachable!("ranks matched"),
    })
}

fn cmp_args(a: &[Rc<Val>], b: &[Rc<Val>]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .zip(b)
            .map(|(x, y)| cmp_val(x, y))
            .find(|o| *o != Ordering::Equal)
            .unwrap_or(Ordering::Equal)
    })
}

fn cmp_op(a: &Op, b: &Op) -> Ordering {
    match (a, b) {
        (Op::Prim(p), Op::Prim(q)) => {
            // Distinct prims print distinct mnemonics (widths included), and
            // `push` never becomes an `Op`, so the spelling is a faithful key.
            debug_assert!(!matches!(p, Prim::Push(_)));
            p.to_string().cmp(&q.to_string())
        }
        (Op::Prim(_), Op::Call { .. }) => Ordering::Less,
        (Op::Call { .. }, Op::Prim(_)) => Ordering::Greater,
        (
            Op::Call { target, arity },
            Op::Call {
                target: t2,
                arity: a2,
            },
        ) => usize::from(*target)
            .cmp(&usize::from(*t2))
            .then_with(|| (arity.inputs, arity.outputs).cmp(&(a2.inputs, a2.outputs))),
    }
}

/// A total order on the machine's values, consistent with [`Value`]'s
/// equality: symbols by `id`, everything else by content.
fn cmp_value(a: &Value, b: &Value) -> Ordering {
    fn rank(v: &Value) -> u8 {
        match v {
            Value::Bool(_) => 0,
            Value::Int(_) => 1,
            Value::ConstString(_) => 2,
            Value::Tuple(_) => 3,
            Value::Symbol(_) => 4,
        }
    }
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::ConstString(x), Value::ConstString(y)) => x.cmp(y),
        (Value::Tuple(x), Value::Tuple(y)) => x.len().cmp(&y.len()).then_with(|| {
            x.iter()
                .zip(y)
                .map(|(v, w)| cmp_value(v, w))
                .find(|o| *o != Ordering::Equal)
                .unwrap_or(Ordering::Equal)
        }),
        (Value::Symbol(x), Value::Symbol(y)) => x.id.cmp(&y.id),
        _ => unreachable!("ranks matched"),
    })
}

// ---- the machine, consulted -------------------------------------------------

/// Runs one instruction on the operands it wants, on the machine itself.
///
/// The fold owes the interpreter exact agreement, junk included, so there is
/// no second implementation to drift: a scratch library holding
/// `push v̄ ; inst` is executed and the stack it leaves is the answer. Shared
/// with the `eval` rule in [`crate::rules`] — one bridge, two customers.
pub(crate) fn run_window(operands: &[Value], inst: &Instruction) -> Option<Vec<Value>> {
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

// ---- reading a normal form back as a term -----------------------------------

/// The normal form as a [`Term`] again: a canonical spelling, deterministic
/// in the tree, so equal trees reify to one term.
///
/// The scheme is deliberately naive — each output is computed from fresh
/// copies of the inputs, `pick`-style, and the inputs are dropped at the
/// end — because its job is to be *written down*, as a `norm` cut's waypoint
/// or a residual's evidence, not to be efficient code. Sharing is the
/// e-graph's to rediscover (`copy-nat` backward), and it does.
pub fn reify(nf: &Nf, inputs: usize) -> Term {
    match nf {
        Nf::Leaf(vals) => {
            let mut steps = Vec::new();
            let mut height = inputs;
            for v in vals {
                emit_val(v, &mut steps, &mut height);
            }
            debug_assert_eq!(height, inputs + vals.len());
            // The inputs, still untouched underneath, go together.
            if inputs > 0 {
                steps.push(if vals.is_empty() {
                    Term::drop(inputs)
                } else {
                    Term::par(Term::drop(inputs), Term::id(vals.len()))
                });
            }
            fold_steps(steps)
        }
        Nf::Branch {
            cond,
            if_true,
            if_false,
        } => {
            let mut steps = Vec::new();
            let mut height = inputs;
            emit_val(cond, &mut steps, &mut height);
            debug_assert_eq!(height, inputs + 1);
            steps.push(
                Term::branch(reify(if_true, inputs), reify(if_false, inputs))
                    .expect("arms of one tree share a width"),
            );
            fold_steps(steps)
        }
    }
}

/// Steps composed left to right with the padding lowering would add — an
/// empty run is the identity on nothing.
fn fold_steps(steps: Vec<Term>) -> Term {
    let mut steps = steps.into_iter();
    let Some(first) = steps.next() else {
        return Term::id(0);
    };
    steps.fold(first, Term::pad_compose)
}

/// Code that computes `v` on top of the current stack, appended to `steps`.
///
/// `height` is how deep the stack is right now, inputs included; a variable
/// is fetched by copying at its depth and bubbling the copy up, which is
/// exactly the frame spelling `pick` lowers to.
fn emit_val(v: &Val, steps: &mut Vec<Term>, height: &mut usize) {
    match v {
        Val::Var(i) => {
            let depth = *height - 1 - i;
            steps.push(if depth == 0 {
                Term::copy(1)
            } else {
                Term::par(Term::copy(1), Term::id(depth))
            });
            *height += 1;
            for k in (1..=depth).rev() {
                steps.push(if k == 1 {
                    Term::op(Prim::Swap)
                } else {
                    Term::par(Term::op(Prim::Swap), Term::id(k - 1))
                });
            }
        }
        Val::Lit(value) => {
            steps.push(Term::op(Prim::Push(value.clone())));
            *height += 1;
        }
        Val::App { op, args } => {
            for a in args {
                emit_val(a, steps, height);
            }
            let Arity { inputs, outputs } = op.arity();
            debug_assert_eq!(outputs, 1);
            steps.push(op_term(op));
            *height = *height - inputs + outputs;
        }
        Val::Proj { index, op, args } => {
            for a in args {
                emit_val(a, steps, height);
            }
            let Arity { inputs, outputs } = op.arity();
            steps.push(op_term(op));
            *height = *height - inputs + outputs;
            // Keep output `index`: drop the block above it, then the block
            // beneath it.
            let above = outputs - 1 - index;
            if above > 0 {
                steps.push(Term::drop(above));
                *height -= above;
            }
            if *index > 0 {
                steps.push(Term::par(Term::drop(*index), Term::id(1)));
                *height -= index;
            }
        }
    }
}

fn op_term(op: &Op) -> Term {
    match op {
        Op::Prim(p) => Term::op(p.clone()),
        Op::Call { target, arity } => Term::call(*target, *arity),
    }
}

// ---- printing ---------------------------------------------------------------

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Var(i) => write!(f, "x{}", i),
            Val::Lit(v) => write!(f, "{}", v),
            Val::App { op, args } => write_app(f, op, args),
            Val::Proj { index, op, args } => {
                write_app(f, op, args)?;
                write!(f, ".{}", index)
            }
        }
    }
}

fn write_app(f: &mut fmt::Formatter<'_>, op: &Op, args: &[Rc<Val>]) -> fmt::Result {
    match op {
        Op::Prim(p) => write!(f, "{}", p)?,
        Op::Call { target, .. } => write!(f, "call#{}", usize::from(*target))?,
    }
    write!(f, "(")?;
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", a)?;
    }
    write!(f, ")")
}

impl fmt::Display for Nf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Nf::Leaf(vals) => {
                write!(f, "[")?;
                for (i, v) in vals.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Nf::Branch {
                cond,
                if_true,
                if_false,
            } => write!(f, "if {} then {} else {}", cond, if_true, if_false),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::lower;
    use bytecode::assemble;

    /// The term a sentence written inline lowers to.
    fn term_of(body: &str) -> Term {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        lower(&library, idx).unwrap()
    }

    /// The normal form of a sentence written inline.
    fn nf_of(body: &str) -> Nf {
        normalize(&term_of(body))
    }

    /// The two sides' normal forms, padded to one arity first — the same
    /// net-change allowance `Goal::aligned` pays, since `pick 1 ; drop 0` =
    /// ε is `(2 -> 2)` against `(0 -> 0)`.
    fn aligned_nfs(a: &str, b: &str) -> (Nf, Nf) {
        let goal = crate::goal::Goal::aligned(term_of(a), term_of(b));
        (normalize(&goal.lhs), normalize(&goal.rhs))
    }

    fn agree(a: &str, b: &str) {
        let (na, nb) = aligned_nfs(a, b);
        assert_eq!(na, nb, "\n  left:  {}\n  right: {}", na, nb);
    }

    fn differ(a: &str, b: &str) {
        let (na, nb) = aligned_nfs(a, b);
        assert_ne!(na, nb, "\n  both: {}", na);
    }

    // ---- layer 1: the cartesian core has no spelling ----

    #[test]
    fn the_structural_layer_vanishes() {
        agree("swap swap", "");
        // The counit: copy, then drop the copy.
        agree("pick 0 drop 0", "");
        // Yang–Baxter, as pure permutation shuffling.
        agree("swap dip { swap } swap", "dip { swap } swap dip { swap }");
    }

    #[test]
    fn discarded_work_is_no_work() {
        // Compute on copies, drop the answer: ε-naturality, silently.
        agree("pick 1 pick 1 equal drop 0", "");
        agree("add drop 0", "drop 0 drop 0");
    }

    #[test]
    fn copying_a_constant_is_pushing_it_twice() {
        agree("push 9 pick 0", "push 9 push 9");
    }

    #[test]
    fn a_frame_is_a_roll_pair() {
        // `taking_a_frame_off`, the corpus identity.
        agree("dip 1 { not }", "roll 1 not roll 1");
    }

    // ---- layer 3, folded into the values ----

    #[test]
    fn a_literal_window_runs_on_the_machine() {
        agree("push 1 push 2 add", "push 3");
        // Junk semantics included.
        agree("push true push 2 add", "push 0");
    }

    #[test]
    fn commutative_operands_sort() {
        agree("swap add", "add");
        agree("swap equal", "equal");
        differ("swap subtract", "subtract");
    }

    #[test]
    fn tuples_cancel_and_retuple_to_the_coercion() {
        agree("tuple 2 untuple 2", "");
        agree("untuple 2 tuple 2", "as_tuple 2");
        agree("as_bool as_bool", "as_bool");
    }

    #[test]
    fn a_promised_bool_answers_its_test() {
        agree("is_int is_bool", "drop 0 push true");
        agree("is_bool is_bool", "drop 0 push true");
        // Two spellings of one test, and neither reduces to the other.
        agree("is_bool is_bool", "is_int is_bool");
    }

    // ---- layer 2: what the case tree sees ----

    #[test]
    fn a_literal_condition_selects_its_arm() {
        agree("push true branch { push 1 } { push 2 }", "push 1");
        agree("push false branch { push 1 } { push 2 }", "push 2");
        // Junk is truthy.
        agree("push 7 branch { push 1 } { push 2 }", "push 1");
    }

    #[test]
    fn equal_arms_never_branch() {
        agree("branch { push 1 } { push 1 }", "drop 0 push 1");
    }

    #[test]
    fn a_retested_condition_is_decided() {
        // The corpus's `a_value_tested_twice`, whole.
        agree(
            "pick 0 branch { branch { push 1 } { push 2 } } { branch { push 3 } { push 4 } }",
            "branch { push 1 } { push 4 }",
        );
    }

    #[test]
    fn a_value_that_tested_equal_is_the_literal() {
        // The corpus's `specializing_a_tested_value`: substituting the
        // literal completes a window folding then finishes.
        agree(
            "pick 0 push 7 equal branch { push 7 equal } { drop 0 push false }",
            "pick 0 push 7 equal branch { drop 0 push true } { drop 0 push false }",
        );
    }

    #[test]
    fn branches_on_independent_conditions_stay_apart() {
        // The known incompleteness, pinned: both orders of two independent
        // branches are equal in the theory, and this normal form does not
        // see it. If this test ever fails, the normalizer learned something
        // — move the claim to `agree`.
        differ(
            "dip { branch { push 1 } { push 2 } } branch { push 3 } { push 4 } tuple 3",
            "branch { dip { branch { push 1 } { push 2 } } push 3 } { dip { branch { push 1 } { push 2 } } push 4 } tuple 3",
        );
    }

    // ---- calls stay opaque ----

    #[test]
    fn a_call_is_an_uninterpreted_operation() {
        let code = r#"
            sentence helper { add }
            sentence probe_a { jump crate::helper }
            sentence probe_b { add }
        "#;
        let library = assemble(code).unwrap();
        let by_name = |name: &str| {
            let idx = library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(idx, _)| idx)
                .unwrap();
            normalize(&lower(&library, idx).unwrap())
        };
        // The call is not its body…
        assert_ne!(by_name("probe_a"), by_name("probe_b"));
        // …but a zero-output call is a drop, because the language is total.
        let f = Term::call(SentenceIndex::from(9), Arity::new(2, 0));
        assert_eq!(normalize(&f), normalize(&Term::drop(2)));
    }

    // ---- reification ----

    #[test]
    fn reify_speaks_the_frame_language() {
        // The identity on one value, spelled canonically: fetch the input,
        // then drop the original underneath.
        let term = reify(&nf_of("swap swap"), 2);
        term.check().unwrap();
        assert_eq!(
            format!("{}", term),
            "copy(1) * id(1) ; id(1) * swap ; id(1) * (copy(1) * id(1)) ; \
             id(2) * swap ; drop(2) * id(2)"
        );
        // Each fetch is the `pick` frame spelling: copy at depth, bubble up.
        let one = reify(&Nf::Leaf(vec![Rc::new(Val::Var(0))]), 1);
        one.check().unwrap();
        assert_eq!(format!("{}", one), "copy(1) ; drop(1) * id(1)");
    }

    /// Every sentence the integration suite compiles: normalize, reify,
    /// check the reified term, and normalize again to the same tree.
    ///
    /// The round trip is the strongest cheap statement of the module's
    /// contract: reification is a *canonical spelling* of the tree, so
    /// re-reading it must lose nothing — across every real program in the
    /// corpus, branches, calls, tuples and all.
    #[test]
    fn the_whole_corpus_round_trips() {
        let tests = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("the crate sits in the workspace")
            .join("tests");
        let text = std::fs::read_to_string(tests.join("main.hana")).unwrap();
        let mut map = bytecode::SourceMap::new();
        let file = map.add("main.hana", text);
        let library = bytecode::assemble_source(&mut map, file, Some(&tests))
            .unwrap_or_else(|e| panic!("{}", map.render(&e)));

        let terms = crate::term::lower_all(&library).unwrap();
        assert!(terms.len() > 100, "the corpus should be a real one");
        for (idx, term) in terms.iter_enumerated() {
            let nf = normalize(term);
            let reified = reify(&nf, term.arity().inputs);
            reified.check().unwrap_or_else(|e| {
                panic!("sentence {} reified ill-formed: {}", library.names[idx], e)
            });
            assert_eq!(
                reified.arity(),
                term.arity(),
                "sentence {} changed arity through reification",
                library.names[idx]
            );
            assert_eq!(
                normalize(&reified),
                nf,
                "sentence {} did not round-trip",
                library.names[idx]
            );
        }
    }
}
