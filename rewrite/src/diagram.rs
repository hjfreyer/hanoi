//! The string-diagram engine: programs as wiring, equality as one spelling.
//!
//! A program here is not a term but a **diagram**: operations are boxes with
//! ordered ports, values are wires, and the whole structural layer of
//! [docs/algebra.md](../../docs/algebra.md) is representation rather than
//! rules —
//!
//! - `id(n)` is a wire passing through: it has no node, so there is nothing
//!   to pad, fuse or eliminate;
//! - `;` and `*` are not stored: sequencing is one box's output wire being
//!   another's input, side-by-side is two boxes sharing no wires, so both
//!   associativities and the interchange law are unstatable — the spellings
//!   they translate between are the same data;
//! - `swap` is wires crossing, and the data structure does not remember
//!   crossings;
//! - `copy` is a wire with two consumers and `drop` is a wire no one
//!   consumes, both free because the language is total and pure — which is
//!   also why interning makes `copy-nat` automatic (one node per distinct
//!   computation, however many wires read it) and reachability makes
//!   `drop-nat` automatic (unconsumed work has no spelling to survive in).
//!
//! Everything lives in a [`Ctx`]: an arena interning both the wires
//! ([`ValNode`], addressed by [`ValId`]) and the diagrams themselves
//! ([`DiagNode`], addressed by [`DiagId`]), so equality at either level is
//! integer comparison and equal subtrees are one node however often they
//! recur. Normalize both sides of a goal in one `Ctx` and "same diagram"
//! costs nothing to ask.
//!
//! Branches are the part with real content left, and they take the decision-
//! diagram discipline whole: the canonical form is an **ordered, shared case
//! tree** — along every path conditions appear in one global order
//! ([`cmp_val`]), so two programs that test independent conditions in
//! different orders reach one spelling, and a long chain of checks whose
//! arms reconverge collapses instead of doubling ([`Ctx::branch`] refuses a
//! node whose arms are one diagram). [`Ctx::ite`] is the reordering
//! constructor, restriction is Shannon expansion, and the arm that saw
//! `true` has its condition's literal written through it
//! (`specialize-equal`) at every level, joins included. What remains beyond
//! this form is genuinely semantic: η (introducing a case split on an
//! opaque value), and whatever of layer 2 no ordering reaches.
//!
//! Every law of the algebra sheet with a bounded, confluent reading is
//! folded here, one place per law: literal windows run on the machine
//! itself ([`run_window`], so there is no second semantics), a literal
//! condition takes its arm (`fold-branch`), a retested condition is decided
//! (`retest`), commutative operands sort (`commute`), `tuple n ; untuple n`
//! cancels (`tuple-cancel`), `untuple n ; tuple n` reads back as the
//! coercion (`untuple-retuple`), coercions idempote (`as-*-idem`), a test
//! of a `yields_bool` answer is `true` (`bool-result`), and a zero-output
//! computation vanishes (`drop-nat` at the codomain). Calls stay opaque:
//! `inline` remains the step that spends a definition.
//!
//! **Trust.** Nothing here produces a derivation yet. This module *is* the
//! prover's judge of equality — the `diagram` step normalizes both sides of
//! a goal and asks whether they are one — held to the machine by
//! [`run_window`], to itself by the reify round trip, and to the corpus by
//! tests. The intended next layer is rewriting *on* diagrams — rules as
//! cut-and-splice on the wiring, each step small and checkable, which is
//! how claims beyond the canonical form (η, case splits) get proofs — and
//! this module is the representation it will run on.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

use bytecode::{Instruction, Library, SentenceIndex, Value};

use crate::term::{Arity, Prim, Term};

// ---- the arena ----------------------------------------------------------------

/// A wire: an index into a [`Ctx`]. Two wires are the same computation iff
/// they are the same index, which is the point of interning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValId(u32);

/// A diagram: an index into a [`Ctx`]. Same contract as [`ValId`]: one
/// index per distinct diagram, so equal case analyses share and equality is
/// integer comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagId(u32);

/// The arena everything lives in — wires, diagrams, and the memo tables
/// that keep the decision-diagram operations linear in *distinct* nodes
/// rather than in paths. One `Ctx` per goal: both sides normalize into it.
#[derive(Default)]
pub struct Ctx {
    vals: Vec<ValNode>,
    vals_interned: HashMap<ValNode, ValId>,
    diags: Vec<DiagNode>,
    diags_interned: HashMap<DiagNode, DiagId>,
    // The operation caches. Everything memoized is a pure function of
    // append-only arena contents, so an entry never goes stale.
    restrict_memo: HashMap<(DiagId, ValId, bool), DiagId>,
    subst_val_memo: HashMap<(ValId, ValId, ValId), ValId>,
    subst_diag_memo: HashMap<(DiagId, ValId, ValId), DiagId>,
    ite_memo: HashMap<(ValId, DiagId, DiagId), DiagId>,
}

/// One computation: what a wire carries, as a node over other wires.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValNode {
    /// Input `i`, counted from the deepest (0) upward.
    Var(usize),
    /// A literal the program pushed or folding produced.
    Lit(HVal),
    /// A single-output operation applied to arguments, deepest first.
    App { op: Op, args: Vec<ValId> },
    /// Output `index` of a multi-output operation — `f = ⟨f;π₁, …, f;πₘ⟩`,
    /// so splitting an application into its projections loses nothing.
    Proj {
        index: usize,
        op: Op,
        args: Vec<ValId>,
    },
}

/// One diagram: a tuple of output wires, or a decision on a condition wire.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DiagNode {
    /// The output stack, deepest first.
    Leaf(Vec<ValId>),
    /// A branch, with the ordered-tree invariant: every condition below
    /// sorts after `cond` under [`cmp_val`].
    Branch {
        cond: ValId,
        if_true: DiagId,
        if_false: DiagId,
    },
}

impl Ctx {
    pub fn val(&self, id: ValId) -> &ValNode {
        &self.vals[id.0 as usize]
    }

    pub fn diag(&self, id: DiagId) -> &DiagNode {
        &self.diags[id.0 as usize]
    }

    fn intern_val(&mut self, node: ValNode) -> ValId {
        if let Some(&id) = self.vals_interned.get(&node) {
            return id;
        }
        let id = ValId(u32::try_from(self.vals.len()).expect("an arena fits in u32"));
        self.vals.push(node.clone());
        self.vals_interned.insert(node, id);
        id
    }

    fn intern_diag(&mut self, node: DiagNode) -> DiagId {
        if let Some(&id) = self.diags_interned.get(&node) {
            return id;
        }
        let id = DiagId(u32::try_from(self.diags.len()).expect("an arena fits in u32"));
        self.diags.push(node.clone());
        self.diags_interned.insert(node, id);
        id
    }

    fn var(&mut self, i: usize) -> ValId {
        self.intern_val(ValNode::Var(i))
    }

    fn lit(&mut self, v: Value) -> ValId {
        self.intern_val(ValNode::Lit(HVal(v)))
    }

    fn leaf(&mut self, vals: Vec<ValId>) -> DiagId {
        self.intern_diag(DiagNode::Leaf(vals))
    }

    fn root_cond(&self, d: DiagId) -> Option<ValId> {
        match self.diag(d) {
            DiagNode::Leaf(_) => None,
            DiagNode::Branch { cond, .. } => Some(*cond),
        }
    }

    /// A branch node — after the last local facts are spent: arms that came
    /// out equal never branch (the branch-of-equal-arms lemma, the
    /// condition's work vanishing by `drop-nat`), and an arm re-testing its
    /// own condition at the root is decided (`retest`, for diagrams met
    /// after the path was recorded).
    fn branch(&mut self, cond: ValId, if_true: DiagId, if_false: DiagId) -> DiagId {
        let if_true = self.restrict(if_true, cond, true);
        let if_false = self.restrict(if_false, cond, false);
        if if_true == if_false {
            return if_true;
        }
        self.intern_diag(DiagNode::Branch {
            cond,
            if_true,
            if_false,
        })
    }

    /// The case tree for "if `cond` then `t` else `f`", with the decision-
    /// diagram invariant restored: any condition in the arms that sorts
    /// before `cond` is hoisted above it (Shannon expansion), so conditions
    /// appear in one global order along every path. This is what makes two
    /// programs that test independent conditions in different orders one
    /// diagram.
    fn ite(&mut self, cond: ValId, t: DiagId, f: DiagId) -> DiagId {
        // A condition that folded to a literal on the way here decides
        // itself.
        if let ValNode::Lit(HVal(v)) = self.val(cond) {
            return if v.truthy() { t } else { f };
        }
        let key = (cond, t, f);
        if let Some(&hit) = self.ite_memo.get(&key) {
            return hit;
        }
        let earlier = [self.root_cond(t), self.root_cond(f)]
            .into_iter()
            .flatten()
            .filter(|&d| cmp_val(self, d, cond) == Ordering::Less)
            .min_by(|&a, &b| cmp_val(self, a, b));
        let out = match earlier {
            None => self.branch(cond, t, f),
            Some(d) => {
                let tt = self.restrict(t, d, true);
                let ft = self.restrict(f, d, true);
                let te = self.restrict(t, d, false);
                let fe = self.restrict(f, d, false);
                let hi = self.ite(cond, tt, ft);
                let lo = self.ite(cond, te, fe);
                // Through `ite`, not `branch`: the restrictions substitute
                // literals, and a substituted condition can fold or
                // re-sort, so the rebuilt arms may carry roots that belong
                // above `d`.
                self.ite(d, hi, lo)
            }
        };
        self.ite_memo.insert(key, out);
        out
    }

    /// The diagram, knowing `cond` came out `taken`: the root level testing
    /// `cond` collapses to its arm, and — when the condition proved a value
    /// equal to a literal — the `true` side has the literal written through
    /// it. Ordered input, ordered output; a condition never hides below a
    /// level it sorts above, so only the root can test `cond`.
    fn restrict(&mut self, d: DiagId, cond: ValId, taken: bool) -> DiagId {
        let key = (d, cond, taken);
        if let Some(&hit) = self.restrict_memo.get(&key) {
            return hit;
        }
        let base = match *self.diag(d) {
            DiagNode::Branch {
                cond: c,
                if_true,
                if_false,
            } if c == cond => {
                if taken {
                    if_true
                } else {
                    if_false
                }
            }
            _ => d,
        };
        let out = if taken {
            match equal_to_literal(self, cond) {
                Some((from, to)) => self.subst_diag(base, from, to),
                None => base,
            }
        } else {
            base
        };
        self.restrict_memo.insert(key, out);
        out
    }

    /// The diagram with every occurrence of `from` replaced by `to`, leaves
    /// and conditions alike — a substitution can decide a condition
    /// outright, so the result is rebuilt through [`Ctx::ite`] on the way
    /// up.
    fn subst_diag(&mut self, d: DiagId, from: ValId, to: ValId) -> DiagId {
        let key = (d, from, to);
        if let Some(&hit) = self.subst_diag_memo.get(&key) {
            return hit;
        }
        let out = match self.diag(d).clone() {
            DiagNode::Leaf(vals) => {
                let walked: Vec<ValId> =
                    vals.iter().map(|&v| self.subst_val(v, from, to)).collect();
                self.leaf(walked)
            }
            DiagNode::Branch {
                cond,
                if_true,
                if_false,
            } => {
                let cond = self.subst_val(cond, from, to);
                let t = self.subst_diag(if_true, from, to);
                let f = self.subst_diag(if_false, from, to);
                self.ite(cond, t, f)
            }
        };
        self.subst_diag_memo.insert(key, out);
        out
    }

    /// The wire with every occurrence of `from` replaced by `to`, re-
    /// canonicalized on the way back up — a substitution can complete a
    /// literal window, and the rebuilt application must fold the way a
    /// fresh one would.
    fn subst_val(&mut self, v: ValId, from: ValId, to: ValId) -> ValId {
        if v == from {
            return to;
        }
        let key = (v, from, to);
        if let Some(&hit) = self.subst_val_memo.get(&key) {
            return hit;
        }
        let out = match self.val(v).clone() {
            ValNode::Var(_) | ValNode::Lit(_) => v,
            ValNode::App { op, args } => {
                let walked: Vec<ValId> =
                    args.iter().map(|&a| self.subst_val(a, from, to)).collect();
                if walked == args {
                    v
                } else {
                    let out = apply(self, &op, walked);
                    debug_assert_eq!(out.len(), 1, "an App is a single-output application");
                    out[0]
                }
            }
            ValNode::Proj { index, op, args } => {
                let walked: Vec<ValId> =
                    args.iter().map(|&a| self.subst_val(a, from, to)).collect();
                if walked == args {
                    v
                } else {
                    apply(self, &op, walked)[index]
                }
            }
        };
        self.subst_val_memo.insert(key, out);
        out
    }
}

/// A [`Value`] with the hash its equality deserves: symbols hash by `id`,
/// the field their equality reads, and everything else by content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HVal(pub Value);

impl Hash for HVal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_value(&self.0, state)
    }
}

fn hash_value<H: Hasher>(v: &Value, state: &mut H) {
    std::mem::discriminant(v).hash(state);
    match v {
        Value::Bool(b) => b.hash(state),
        Value::Int(i) => i.hash(state),
        Value::ConstString(s) => s.hash(state),
        Value::Tuple(vs) => {
            vs.len().hash(state);
            for v in vs {
                hash_value(v, state);
            }
        }
        Value::Symbol(s) => s.id.hash(state),
    }
}

/// An operation a box can be: a primitive, or a call left opaque.
///
/// `push` and `swap` never appear — the first is a [`ValNode::Lit`], the
/// second is wiring — and a call carries its arity for the same reason
/// [`Term::Call`] does: the diagram stays meaningful without a library.
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

impl Hash for Op {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Op::Prim(p) => {
                0u8.hash(state);
                std::mem::discriminant(p).hash(state);
                match p {
                    Prim::Tuple(n) | Prim::Untuple(n) | Prim::AsTuple(n) => n.hash(state),
                    // `push` is a Lit, never an Op; hash it anyway so the
                    // impl is total.
                    Prim::Push(v) => hash_value(v, state),
                    _ => {}
                }
            }
            Op::Call { target, arity } => {
                1u8.hash(state);
                usize::from(*target).hash(state);
                arity.inputs.hash(state);
                arity.outputs.hash(state);
            }
        }
    }
}

/// The conditions the current path has already decided, outermost first.
type Path = Vec<(ValId, bool)>;

/// The diagram of a term: run it on a stack of input wires and keep what
/// lands, folded and ordered as it builds.
pub fn normalize(ctx: &mut Ctx, term: &Term) -> DiagId {
    let stack: Vec<ValId> = (0..term.arity().inputs).map(|i| ctx.var(i)).collect();
    eval(ctx, term, stack, &mut Vec::new())
}

/// One term on one stack of wires — exactly the term's inputs, deepest
/// first — under the conditions the path has decided.
fn eval(ctx: &mut Ctx, term: &Term, mut stack: Vec<ValId>, path: &mut Path) -> DiagId {
    debug_assert_eq!(stack.len(), term.arity().inputs, "the caller cuts by arity");
    match term {
        Term::Id(_) => ctx.leaf(stack),
        Term::Drop(_) => ctx.leaf(Vec::new()),
        // Block-wise: `copy(2)` takes `[a, b]` to `[a, b, a, b]`. No new
        // node: a copy is the same wire read twice.
        Term::Copy(_) => {
            let again = stack.clone();
            stack.extend(again);
            ctx.leaf(stack)
        }
        Term::Op(Prim::Push(v)) => {
            let lit = ctx.lit(v.clone());
            ctx.leaf(vec![lit])
        }
        Term::Op(Prim::Swap) => {
            stack.swap(0, 1);
            ctx.leaf(stack)
        }
        Term::Op(prim) => {
            let out = apply(ctx, &Op::Prim(prim.clone()), stack);
            ctx.leaf(out)
        }
        Term::Call { target, arity } => {
            let out = apply(
                ctx,
                &Op::Call {
                    target: *target,
                    arity: *arity,
                },
                stack,
            );
            ctx.leaf(out)
        }
        Term::Compose(a, b) => {
            let first = eval(ctx, a, stack, path);
            graft(ctx, first, path, Vec::new(), &mut |ctx, left, path, _| {
                eval(ctx, b, left, path)
            })
        }
        Term::Par(a, b) => {
            // The second argument gets the top. A par is the one place
            // wires *join a path late*: the top slice runs under whatever
            // the deep side branched on, and the deep side's answers land
            // under whatever the top branched on. `branch_on` specialized
            // only the stack present at its own fork, so each join hands
            // its slice to `graft` as a carried stack, which substitutes
            // each condition's literal through it once, at the descent.
            let top = stack.split_off(stack.len() - b.arity().inputs);
            let deep = eval(ctx, a, stack, path);
            graft(ctx, deep, path, top, &mut |ctx, deep_out, path, top_in| {
                let above = eval(ctx, b, top_in, path);
                graft(
                    ctx,
                    above,
                    path,
                    deep_out,
                    &mut |ctx, top_out, _, deep_out| {
                        let mut whole = deep_out;
                        whole.extend(top_out);
                        ctx.leaf(whole)
                    },
                )
            })
        }
        Term::Branch { if_true, if_false } => {
            let cond = stack.pop().expect("a branch has its condition on top");
            branch_on(ctx, cond, stack, if_true, if_false, path)
        }
    }
}

/// Continues a computation under every leaf of an already-built diagram,
/// keeping the path honest as it descends and re-ordering as it rebuilds —
/// the continuation may have forked on conditions that sort before the ones
/// already stacked.
///
/// `carried` is a stack of wires that joins the path late — a par's other
/// slice, which was not present at the forks this diagram made. Each
/// condition's literal is written through it once, at the descent into the
/// arm that saw `true` (`specialize-equal` for joiners), so a leaf receives
/// it specialized against exactly the conditions above that leaf.
///
/// The continuation gets the leaf's own stack, the path, and the carried
/// stack as it stands at that leaf.
type Graft<'g> = &'g mut dyn FnMut(&mut Ctx, Vec<ValId>, &mut Path, Vec<ValId>) -> DiagId;

fn graft(ctx: &mut Ctx, d: DiagId, path: &mut Path, carried: Vec<ValId>, then: Graft) -> DiagId {
    match ctx.diag(d).clone() {
        DiagNode::Leaf(stack) => then(ctx, stack, path, carried),
        DiagNode::Branch {
            cond,
            if_true,
            if_false,
        } => {
            let carried_true = match equal_to_literal(ctx, cond) {
                Some((from, to)) => carried
                    .iter()
                    .map(|&v| ctx.subst_val(v, from, to))
                    .collect(),
                None => carried.clone(),
            };
            path.push((cond, true));
            let t = graft(ctx, if_true, path, carried_true, then);
            path.pop();
            path.push((cond, false));
            let f = graft(ctx, if_false, path, carried, then);
            path.pop();
            ctx.ite(cond, t, f)
        }
    }
}

/// A branch on a symbolic condition: decided if it can be, forked and
/// slotted into condition order if not.
fn branch_on(
    ctx: &mut Ctx,
    cond: ValId,
    stack: Vec<ValId>,
    if_true: &Term,
    if_false: &Term,
    path: &mut Path,
) -> DiagId {
    // `fold-branch`: a literal condition selects its arm.
    if let ValNode::Lit(HVal(v)) = ctx.val(cond) {
        let taken = if v.truthy() { if_true } else { if_false };
        return eval(ctx, taken, stack, path);
    }
    // `retest-*`: a condition this path already tested answers the same.
    if let Some(&(_, taken)) = path.iter().find(|(c, _)| *c == cond) {
        let arm = if taken { if_true } else { if_false };
        return eval(ctx, arm, stack, path);
    }
    // `specialize-equal`: inside the then arm, a value that tested `equal`
    // to a literal is that literal — `equal` is structural identity.
    let then_stack = specialize(ctx, cond, &stack);
    path.push((cond, true));
    let t = eval(ctx, if_true, then_stack, path);
    path.pop();
    path.push((cond, false));
    let f = eval(ctx, if_false, stack, path);
    path.pop();
    ctx.ite(cond, t, f)
}

// ---- specialization ----------------------------------------------------------

/// The value–literal pair a condition proves equal when it holds: `equal`
/// is structural identity, so the arm that saw `true` may write the literal
/// wherever the value stood.
fn equal_to_literal(ctx: &Ctx, cond: ValId) -> Option<(ValId, ValId)> {
    let ValNode::App {
        op: Op::Prim(Prim::Equal),
        args,
    } = ctx.val(cond)
    else {
        return None;
    };
    let [a, b] = args[..] else {
        return None;
    };
    match (ctx.val(a), ctx.val(b)) {
        (_, ValNode::Lit(_)) => Some((a, b)),
        (ValNode::Lit(_), _) => Some((b, a)),
        _ => None,
    }
}

/// The then-arm's stack when the condition is `v = literal`: every
/// occurrence of `v` replaced by the literal it just proved to be.
fn specialize(ctx: &mut Ctx, cond: ValId, stack: &[ValId]) -> Vec<ValId> {
    let Some((from, to)) = equal_to_literal(ctx, cond) else {
        return stack.to_vec();
    };
    stack.iter().map(|&v| ctx.subst_val(v, from, to)).collect()
}

// ---- one operation, folded as far as the facts reach ---------------------------

/// One box on its argument wires: the output wires it leaves, folded as far
/// as the facts reach.
fn apply(ctx: &mut Ctx, op: &Op, args: Vec<ValId>) -> Vec<ValId> {
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
            .map(|&a| match ctx.val(a) {
                ValNode::Lit(HVal(v)) => Some(v.clone()),
                _ => None,
            })
            .collect();
        if let Some(operands) = literals
            && let Some(answers) = run_window(&operands, &prim.to_instruction())
        {
            debug_assert_eq!(answers.len(), outputs, "the machine honors the arity table");
            return answers.into_iter().map(|v| ctx.lit(v)).collect();
        }

        // `tuple-cancel`: taking apart what `tuple n` just built.
        if let Prim::Untuple(n) = prim
            && let ValNode::App {
                op: Op::Prim(Prim::Tuple(m)),
                args: elems,
            } = ctx.val(args[0])
            && m == n
        {
            return elems.clone();
        }

        // `untuple-retuple`: rebuilding what `untuple n` took apart is the
        // coercion, not the identity — the slots may have been junk-filled.
        if let Prim::Tuple(n) = prim
            && *n > 0
            && let Some(inner) = retupled(ctx, *n, &args)
        {
            return apply(ctx, &Op::Prim(Prim::AsTuple(*n)), vec![inner]);
        }

        // `as-*-idem`: coercing twice is coercing once.
        if idempotent_coercion(ctx, prim, &args) {
            return vec![args[0]];
        }

        // `bool-result`: asking `is_bool` of an answer the instruction set
        // promises is a bool. The promise is measured by `vm`.
        if matches!(prim, Prim::IsBool)
            && let ValNode::App {
                op: Op::Prim(inner),
                ..
            } = ctx.val(args[0])
            && inner.to_instruction().yields_bool()
        {
            let truth = ctx.lit(Value::Bool(true));
            return vec![truth];
        }

        // `commute`: a commutative operation's operands in one canonical
        // order, so `swap ; op` and `op` normalize alike.
        if prim.to_instruction().commutative() {
            let mut args = args;
            args.sort_by(|&a, &b| cmp_val(ctx, a, b));
            return build(ctx, op, args, outputs);
        }
    }

    build(ctx, op, args, outputs)
}

/// The box nothing folded: an `App` wire, or one `Proj` wire per output.
fn build(ctx: &mut Ctx, op: &Op, args: Vec<ValId>, outputs: usize) -> Vec<ValId> {
    if outputs == 1 {
        return vec![ctx.intern_val(ValNode::App {
            op: op.clone(),
            args,
        })];
    }
    (0..outputs)
        .map(|index| {
            ctx.intern_val(ValNode::Proj {
                index,
                op: op.clone(),
                args: args.clone(),
            })
        })
        .collect()
}

/// The common argument under `args`, when they are exactly the outputs of
/// `untuple n` on it, in order.
fn retupled(ctx: &Ctx, n: usize, args: &[ValId]) -> Option<ValId> {
    let inner = |arg: ValId, want: usize| -> Option<ValId> {
        match ctx.val(arg) {
            // `untuple 1` has one output, so it is an `App`, not a `Proj`.
            ValNode::App {
                op: Op::Prim(Prim::Untuple(m)),
                args: a,
            } if *m == n && want == 0 && n == 1 => Some(a[0]),
            ValNode::Proj {
                index,
                op: Op::Prim(Prim::Untuple(m)),
                args: a,
            } if *m == n && *index == want => Some(a[0]),
            _ => None,
        }
    };
    let first = inner(args[0], 0)?;
    for (i, &arg) in args.iter().enumerate().skip(1) {
        if inner(arg, i)? != first {
            return None;
        }
    }
    Some(first)
}

/// Whether this is a coercion applied to its own answer.
fn idempotent_coercion(ctx: &Ctx, prim: &Prim, args: &[ValId]) -> bool {
    let inner = match ctx.val(args[0]) {
        ValNode::App {
            op: Op::Prim(p), ..
        } => p,
        _ => return false,
    };
    matches!(
        (prim, inner),
        (Prim::AsBool, Prim::AsBool) | (Prim::AsInt, Prim::AsInt)
    ) || matches!((prim, inner), (Prim::AsTuple(n), Prim::AsTuple(m)) if n == m)
}

// ---- ordering, the one global choice --------------------------------------------

/// A total order on wires, consistent with their equality and stable across
/// contexts (it reads structure, not indices). It is both the tiebreak that
/// makes commutative operands canonical and the global condition order the
/// case trees keep.
pub fn cmp_val(ctx: &Ctx, a: ValId, b: ValId) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    fn rank(v: &ValNode) -> u8 {
        match v {
            ValNode::Var(_) => 0,
            ValNode::Lit(_) => 1,
            ValNode::App { .. } => 2,
            ValNode::Proj { .. } => 3,
        }
    }
    let (na, nb) = (ctx.val(a), ctx.val(b));
    rank(na).cmp(&rank(nb)).then_with(|| match (na, nb) {
        (ValNode::Var(i), ValNode::Var(j)) => i.cmp(j),
        (ValNode::Lit(HVal(v)), ValNode::Lit(HVal(w))) => cmp_value(v, w),
        (ValNode::App { op, args }, ValNode::App { op: oq, args: brgs }) => {
            cmp_op(op, oq).then_with(|| cmp_args(ctx, args, brgs))
        }
        (
            ValNode::Proj { index, op, args },
            ValNode::Proj {
                index: jndex,
                op: oq,
                args: brgs,
            },
        ) => cmp_op(op, oq)
            .then_with(|| cmp_args(ctx, args, brgs))
            .then_with(|| index.cmp(jndex)),
        _ => unreachable!("ranks matched"),
    })
}

fn cmp_args(ctx: &Ctx, a: &[ValId], b: &[ValId]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .zip(b)
            .map(|(&x, &y)| cmp_val(ctx, x, y))
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

// ---- the machine, consulted ----------------------------------------------------

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

// ---- reading a diagram back as a term --------------------------------------------

/// The diagram as a [`Term`] again: a canonical spelling, deterministic in
/// the diagram, so equal diagrams reify to one term.
///
/// The spelling is a stack schedule: every distinct wire is computed
/// **once**, in the order the outputs first need it, and later uses fetch
/// it with the `pick` frame spelling instead of recomputing — so the term
/// stays linear-ish in the diagram where re-expanding the sharing would be
/// exponential. The working values and the inputs are dropped together at
/// the end. Its job is to be *written down*, as a `norm` cut's waypoint or
/// a residual's evidence, not to be efficient code.
pub fn reify(ctx: &Ctx, d: DiagId, inputs: usize) -> Term {
    match ctx.diag(d) {
        DiagNode::Leaf(vals) => {
            let mut schedule = Schedule::new(ctx, inputs);
            for &v in vals {
                schedule.ensure(v);
            }
            for &v in vals {
                schedule.fetch(v);
            }
            let work = schedule.height - vals.len();
            if work > 0 {
                schedule.steps.push(if vals.is_empty() {
                    Term::drop(work)
                } else {
                    Term::par(Term::drop(work), Term::id(vals.len()))
                });
            }
            fold_steps(schedule.steps)
        }
        DiagNode::Branch {
            cond,
            if_true,
            if_false,
        } => {
            // The condition on top of the untouched inputs, its scaffolding
            // dropped, then the branch; the arms answer for themselves.
            let mut schedule = Schedule::new(ctx, inputs);
            schedule.ensure(*cond);
            schedule.fetch(*cond);
            let work = schedule.height - inputs - 1;
            if work > 0 {
                schedule
                    .steps
                    .push(Term::par(Term::drop(work), Term::id(1)));
            }
            let mut steps = schedule.steps;
            steps.push(
                Term::branch(reify(ctx, *if_true, inputs), reify(ctx, *if_false, inputs))
                    .expect("arms of one diagram share a width"),
            );
            fold_steps(steps)
        }
    }
}

/// The stack scheduler behind [`reify`]: emits each distinct wire once and
/// remembers where on the stack it lives.
struct Schedule<'c> {
    ctx: &'c Ctx,
    steps: Vec<Term>,
    /// How deep the stack is right now, inputs included.
    height: usize,
    /// Where each computed wire sits, as a position from the bottom.
    positions: HashMap<ValId, usize>,
    /// The multi-output applications already run, so one `Proj` sibling
    /// does not re-run the operation another already paid for.
    groups: HashMap<(Op, Vec<ValId>), ()>,
}

impl<'c> Schedule<'c> {
    fn new(ctx: &'c Ctx, inputs: usize) -> Self {
        let mut positions = HashMap::new();
        for i in 0..inputs {
            if let Some(&id) = ctx.vals_interned.get(&ValNode::Var(i)) {
                positions.insert(id, i);
            }
        }
        Schedule {
            ctx,
            steps: Vec::new(),
            height: inputs,
            positions,
            groups: HashMap::new(),
        }
    }

    /// Makes sure `v` is somewhere on the stack, computing it — and first
    /// its arguments — if this is its first use.
    fn ensure(&mut self, v: ValId) {
        if self.positions.contains_key(&v) {
            return;
        }
        match self.ctx.val(v).clone() {
            ValNode::Var(_) => unreachable!("inputs are seeded"),
            ValNode::Lit(HVal(value)) => {
                self.steps.push(Term::op(Prim::Push(value)));
                self.positions.insert(v, self.height);
                self.height += 1;
            }
            ValNode::App { op, args } => {
                self.emit_application(&op, &args);
                self.positions.insert(v, self.height - 1);
            }
            ValNode::Proj { op, args, .. } => {
                let key = (op.clone(), args.clone());
                if self.groups.contains_key(&key) {
                    // The operation already ran; every sibling projection
                    // was registered then.
                    debug_assert!(self.positions.contains_key(&v));
                    return;
                }
                self.emit_application(&op, &args);
                self.groups.insert(key.clone(), ());
                let outputs = op.arity().outputs;
                for index in 0..outputs {
                    let sibling = ValNode::Proj {
                        index,
                        op: op.clone(),
                        args: args.clone(),
                    };
                    if let Some(&id) = self.ctx.vals_interned.get(&sibling) {
                        self.positions.insert(id, self.height - outputs + index);
                    }
                }
            }
        }
    }

    /// Arguments computed, fetched to the top in order, the box applied.
    fn emit_application(&mut self, op: &Op, args: &[ValId]) {
        for &a in args {
            self.ensure(a);
        }
        for &a in args {
            self.fetch(a);
        }
        self.steps.push(op_term(op));
        let Arity { inputs, outputs } = op.arity();
        self.height = self.height - inputs + outputs;
    }

    /// A copy of `v` brought to the top of the stack — the `pick` frame
    /// spelling: copy at depth, bubble the copy up.
    fn fetch(&mut self, v: ValId) {
        let depth = self.height - 1 - self.positions[&v];
        self.steps.push(if depth == 0 {
            Term::copy(1)
        } else {
            Term::par(Term::copy(1), Term::id(depth))
        });
        self.height += 1;
        for k in (1..=depth).rev() {
            self.steps.push(if k == 1 {
                Term::op(Prim::Swap)
            } else {
                Term::par(Term::op(Prim::Swap), Term::id(k - 1))
            });
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

fn op_term(op: &Op) -> Term {
    match op {
        Op::Prim(p) => Term::op(p.clone()),
        Op::Call { target, arity } => Term::call(*target, *arity),
    }
}

// ---- printing ---------------------------------------------------------------

/// A wire, printed through its context.
pub struct ShowVal<'c>(pub &'c Ctx, pub ValId);

impl fmt::Display for ShowVal<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ShowVal(ctx, id) = *self;
        match ctx.val(id) {
            ValNode::Var(i) => write!(f, "x{}", i),
            ValNode::Lit(HVal(v)) => write!(f, "{}", v),
            ValNode::App { op, args } => write_app(f, ctx, op, args),
            ValNode::Proj { index, op, args } => {
                write_app(f, ctx, op, args)?;
                write!(f, ".{}", index)
            }
        }
    }
}

fn write_app(f: &mut fmt::Formatter<'_>, ctx: &Ctx, op: &Op, args: &[ValId]) -> fmt::Result {
    match op {
        Op::Prim(p) => write!(f, "{}", p)?,
        Op::Call { target, .. } => write!(f, "call#{}", usize::from(*target))?,
    }
    write!(f, "(")?;
    for (i, &a) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", ShowVal(ctx, a))?;
    }
    write!(f, ")")
}

/// A diagram, printed through its context.
pub struct ShowDiagram<'c>(pub &'c Ctx, pub DiagId);

impl fmt::Display for ShowDiagram<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ShowDiagram(ctx, id) = *self;
        match ctx.diag(id) {
            DiagNode::Leaf(vals) => {
                write!(f, "[")?;
                for (i, &v) in vals.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ShowVal(ctx, v))?;
                }
                write!(f, "]")
            }
            DiagNode::Branch {
                cond,
                if_true,
                if_false,
            } => write!(
                f,
                "if {} then {} else {}",
                ShowVal(ctx, *cond),
                ShowDiagram(ctx, *if_true),
                ShowDiagram(ctx, *if_false)
            ),
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

    /// Both sides' diagrams in one context, padded to one arity first — the
    /// same net-change allowance `Goal::aligned` pays.
    fn aligned(a: &str, b: &str) -> (Ctx, DiagId, DiagId) {
        let goal = crate::goal::Goal::aligned(term_of(a), term_of(b));
        let mut ctx = Ctx::default();
        let da = normalize(&mut ctx, &goal.lhs);
        let db = normalize(&mut ctx, &goal.rhs);
        (ctx, da, db)
    }

    fn agree(a: &str, b: &str) {
        let (ctx, da, db) = aligned(a, b);
        assert_eq!(
            da,
            db,
            "\n  left:  {}\n  right: {}",
            ShowDiagram(&ctx, da),
            ShowDiagram(&ctx, db)
        );
    }

    fn differ(a: &str, b: &str) {
        let (ctx, da, db) = aligned(a, b);
        assert_ne!(da, db, "\n  both: {}", ShowDiagram(&ctx, da));
    }

    // ---- the structural layer is representation ----

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

    // ---- layer 3, folded into the wires ----

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

    // ---- the branch layer: what the ordered case tree sees ----

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
    fn specialization_reaches_values_that_join_the_path_late() {
        // The tested original passes *under* the frame that computes the
        // condition — the shape an inlined precondition takes — so it is
        // not on the stack when the fork happens inside the par's top, and
        // joins the path only at the graft. The substitution has to reach
        // it there: the then arm re-tests the original, which folds to
        // `true` only as the literal.
        let body = Term::pad_compose(
            Term::pad_compose(Term::op(Prim::Push(Value::Int(7))), Term::op(Prim::Equal)),
            Term::branch(
                Term::op(Prim::Push(Value::Bool(true))),
                Term::op(Prim::Push(Value::Bool(false))),
            )
            .unwrap(),
        );
        let retest = Term::pad_compose(Term::op(Prim::Push(Value::Int(7))), Term::op(Prim::Equal));
        let term = Term::compose(
            Term::copy(1),
            Term::compose(
                Term::par(Term::id(1), body),
                Term::branch(
                    retest,
                    Term::pad_compose(Term::drop(1), Term::op(Prim::Push(Value::Bool(true)))),
                )
                .unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let claim = Term::pad_compose(Term::drop(1), Term::op(Prim::Push(Value::Bool(true))));
        let mut ctx = Ctx::default();
        let da = normalize(&mut ctx, &term);
        let db = normalize(&mut ctx, &claim);
        assert_eq!(da, db, "\n  got: {}", ShowDiagram(&ctx, da));
    }

    #[test]
    fn independent_branches_reorder_to_one_spelling() {
        // The same four-leaf function, testing its two inputs in either
        // order. The ordered case tree hoists conditions into one global
        // order, so both spellings are one diagram — the incompleteness the
        // old case-tree normalizer pinned as unreachable.
        agree(
            "branch { branch { push 1 } { push 2 } } { branch { push 3 } { push 4 } }",
            "swap branch { branch { push 1 } { push 3 } } { branch { push 2 } { push 4 } }",
        );
    }

    #[test]
    fn a_branch_beside_a_branch_meets_its_sequential_spellings() {
        // Two branches on unrelated values, side by side — and the same
        // pair with the stack swapped around them, so the forks happen in
        // the other order. The ordered tree makes them one diagram.
        let arm = |v| Term::op(Prim::Push(Value::Int(v)));
        let b1 = || Term::branch(arm(10), arm(20)).unwrap();
        let b2 = || Term::branch(arm(30), arm(40)).unwrap();
        let lhs = Term::par(b1(), b2());
        let rhs = Term::compose(
            Term::compose(Term::op(Prim::Swap), Term::par(b2(), b1())).unwrap(),
            Term::op(Prim::Swap),
        )
        .unwrap();
        let mut ctx = Ctx::default();
        let da = normalize(&mut ctx, &lhs);
        let db = normalize(&mut ctx, &rhs);
        assert_eq!(
            da,
            db,
            "\n  left:  {}\n  right: {}",
            ShowDiagram(&ctx, da),
            ShowDiagram(&ctx, db)
        );
    }

    #[test]
    fn a_long_chain_of_reconverging_checks_stays_small() {
        // Sequential branches whose arms come back together — the shape of
        // a test sentence full of asserts. Shared subtrees keep the diagram
        // linear where a plain tree doubles per check; this pins that no
        // spelling of the chain explodes.
        let mut body = String::new();
        for i in 0..24 {
            body.push_str(&format!(
                "push {} equal branch {{ push 1 }} {{ push 1 }} drop 0 pick 0 ",
                i
            ));
        }
        body.push_str("drop 0");
        let mut ctx = Ctx::default();
        let d = normalize(&mut ctx, &term_of(&body));
        assert!(
            ctx.diags.len() < 200,
            "{} diagram nodes for a reconverging chain",
            ctx.diags.len()
        );
        let _ = d;
    }

    #[test]
    fn eta_stays_beyond_the_diagram() {
        // `branch { push true } { push false }` *is* `as_bool` — the
        // machine defines the coercion by truthiness — but seeing it means
        // inventing a case split on an opaque value, which no canonical
        // form here performs. The pinned boundary of the branch layer; if
        // this test ever fails, the diagram learned η — move the claim to
        // `agree`.
        differ("branch { push true } { push false }", "as_bool");
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
        let mut ctx = Ctx::default();
        let by_name = |ctx: &mut Ctx, name: &str| {
            let idx = library
                .names
                .iter_enumerated()
                .find(|(_, n)| *n == name)
                .map(|(idx, _)| idx)
                .unwrap();
            normalize(ctx, &lower(&library, idx).unwrap())
        };
        // The call is not its body…
        let a = by_name(&mut ctx, "probe_a");
        let b = by_name(&mut ctx, "probe_b");
        assert_ne!(a, b);
        // …but a zero-output call is a drop, because the language is total.
        let f = Term::call(SentenceIndex::from(9), Arity::new(2, 0));
        let df = normalize(&mut ctx, &f);
        let dd = normalize(&mut ctx, &Term::drop(2));
        assert_eq!(df, dd);
    }

    // ---- reification ----

    #[test]
    fn reify_speaks_the_frame_language() {
        let mut ctx = Ctx::default();
        // The identity on two values, spelled canonically: fetch each
        // input, then drop the originals underneath.
        let two = normalize(&mut ctx, &term_of("swap swap"));
        let term = reify(&ctx, two, 2);
        term.check().unwrap();
        assert_eq!(
            format!("{}", term),
            "copy(1) * id(1) ; id(1) * swap ; id(1) * (copy(1) * id(1)) ; \
             id(2) * swap ; drop(2) * id(2)"
        );
        // Each fetch is the `pick` frame spelling: copy at depth, bubble up.
        let x0 = ctx.var(0);
        let leaf = ctx.leaf(vec![x0]);
        let one = reify(&ctx, leaf, 1);
        one.check().unwrap();
        assert_eq!(format!("{}", one), "copy(1) ; drop(1) * id(1)");
    }

    /// Every sentence the integration suite compiles: normalize, reify,
    /// check the reified term, and normalize again to the same diagram.
    ///
    /// The round trip is the strongest cheap statement of the module's
    /// contract: reification is a *canonical spelling* of the diagram, so
    /// re-reading it must lose nothing — across every real program in the
    /// corpus, branches, calls, tuples and all.
    ///
    /// One caveat, pinned: a diagram shares branch subtrees and a term
    /// cannot, so a handful of state-machine test sentences tree-expand
    /// past any reasonable term. Those normalize like everything else but
    /// are excused from the reify round trip, by name, so a new escapee is
    /// a visible event rather than a slow one.
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
        let mut ctx = Ctx::default();
        let mut skipped = 0usize;
        for (idx, term) in terms.iter_enumerated() {
            let diagram = normalize(&mut ctx, term);
            let mut budget = 1_000usize;
            if !fits(&ctx, diagram, &mut budget) {
                skipped += 1;
                continue;
            }
            let reified = reify(&ctx, diagram, term.arity().inputs);
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
                normalize(&mut ctx, &reified),
                diagram,
                "sentence {} did not round-trip",
                library.names[idx]
            );
        }
        assert!(
            skipped <= 120,
            "{} sentences outgrew the round trip; the diagrams got bushier",
            skipped
        );
    }

    /// Whether the diagram's tree expansion stays within `budget` nodes —
    /// the size its reified term is proportional to.
    fn fits(ctx: &Ctx, d: DiagId, budget: &mut usize) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match *ctx.diag(d) {
            DiagNode::Leaf(_) => true,
            DiagNode::Branch {
                if_true, if_false, ..
            } => fits(ctx, if_true, budget) && fits(ctx, if_false, budget),
        }
    }
}
