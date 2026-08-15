//! [`Term`] as an [`egg`] language, plus the per-class facts saturation reads.
//!
//! The e-graph is where a goal's two sides go to meet, so this module is the
//! seam between the term model and the search: [`Session`] interns the two
//! kinds of leaf data an e-node cannot carry directly (pushed [`Value`]s and
//! called sentences), [`HanaLang`] mirrors [`Term`] node for node, and
//! [`Proving`] is the analysis that gives every e-class the facts the rules
//! condition on.
//!
//! The load-bearing fact is the **arity**. Every rule instance over this model
//! is arity-preserving — padding made that so — which means arity is invariant
//! across an e-class, and [`Proving::merge`] asserts it. A rule that broke a
//! stack effect would trip that assertion on the spot rather than producing a
//! wrong proof.

use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

use bytecode::{Instruction, SentenceIndex, Value};
use egg::{Analysis, DidMerge, EGraph, Id, RecExpr, define_language};

use crate::term::{Arity, Prim, Term};

/// A width-carrying leaf, printed and parsed as `prefix@n`.
///
/// egg's `define_language!` derives parsing and printing from the data type, so
/// each width-carrying variant gets its own wrapper with a distinct prefix —
/// otherwise `id(2)`, `drop(2)` and `copy(2)` would all print as a bare `2`,
/// and an explanation could not say which it meant.
macro_rules! width_leaf {
    ($(#[$doc:meta])* $name:ident, $prefix:literal) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub usize);

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($prefix, "@{}"), self.0)
            }
        }

        impl FromStr for $name {
            type Err = String;
            fn from_str(s: &str) -> Result<Self, String> {
                s.strip_prefix(concat!($prefix, "@"))
                    .ok_or_else(|| format!("not a {} leaf: {}", $prefix, s))?
                    .parse()
                    .map($name)
                    .map_err(|e| format!("bad {} width: {}", $prefix, e))
            }
        }
    };
}

width_leaf!(/** `id@n` */ IdW, "id");
width_leaf!(/** `drop@n` */ DropW, "drop");
width_leaf!(/** `copy@n` */ CopyW, "copy");
width_leaf!(/** `tuple@n` */ TupleW, "tuple");
width_leaf!(/** `untuple@n` */ UntupleW, "untuple");
width_leaf!(/** `as_tuple@n` */ AsTupleW, "as_tuple");
width_leaf!(/** `push@i` — an index into [`Session::value_of`] */ PushW, "push");
width_leaf!(/** `call@i` — an index into [`Session::call_of`] */ CallW, "call");

define_language! {
    /// [`Term`], node for node. `;` and `*` keep their spelling, a branch's
    /// two children are its arms (the condition is stack, not syntax), the
    /// dataless instructions keep their mnemonics, and everything that carries
    /// data is a [`width_leaf!`] wrapper.
    pub enum HanaLang {
        ";" = Compose([Id; 2]),
        "*" = Par([Id; 2]),
        "branch" = Branch([Id; 2]),

        "swap" = Swap,
        "equal" = Equal,
        "greater" = Greater,
        "less" = Less,
        "add" = Add,
        "subtract" = Subtract,
        "multiply" = Multiply,
        "divide" = Divide,
        "modulo" = Modulo,
        "not" = Not,
        "negate" = Negate,
        "and" = And,
        "or" = Or,
        "const_string_len" = ConstStringLen,
        "const_string_char_at" = ConstStringCharAt,
        "is_int" = IsInt,
        "is_bool" = IsBool,
        "is_const_string" = IsConstString,
        "is_symbol" = IsSymbol,
        "is_tuple" = IsTuple,
        "tuple_length" = TupleLength,
        "as_bool" = AsBool,
        "as_int" = AsInt,

        Idn(IdW),
        Dropn(DropW),
        Copyn(CopyW),
        Tuplen(TupleW),
        Untuplen(UntupleW),
        AsTuplen(AsTupleW),
        Push(PushW),
        Call(CallW),
    }
}

impl HanaLang {
    /// The instruction a node stands for, where it stands for one.
    ///
    /// `None` for the structural nodes and for [`HanaLang::Push`], whose value
    /// lives in the [`Session`] — [`Session::instruction_of`] covers both.
    pub fn instruction(&self) -> Option<Instruction> {
        Some(match self {
            HanaLang::Swap => Instruction::Swap,
            HanaLang::Equal => Instruction::Equal,
            HanaLang::Greater => Instruction::Greater,
            HanaLang::Less => Instruction::Less,
            HanaLang::Add => Instruction::Add,
            HanaLang::Subtract => Instruction::Subtract,
            HanaLang::Multiply => Instruction::Multiply,
            HanaLang::Divide => Instruction::Divide,
            HanaLang::Modulo => Instruction::Modulo,
            HanaLang::Not => Instruction::Not,
            HanaLang::Negate => Instruction::Negate,
            HanaLang::And => Instruction::And,
            HanaLang::Or => Instruction::Or,
            HanaLang::ConstStringLen => Instruction::ConstStringLen,
            HanaLang::ConstStringCharAt => Instruction::ConstStringCharAt,
            HanaLang::IsInt => Instruction::IsInt,
            HanaLang::IsBool => Instruction::IsBool,
            HanaLang::IsConstString => Instruction::IsConstString,
            HanaLang::IsSymbol => Instruction::IsSymbol,
            HanaLang::IsTuple => Instruction::IsTuple,
            HanaLang::TupleLength => Instruction::TupleLength,
            HanaLang::AsBool => Instruction::AsBool,
            HanaLang::AsInt => Instruction::AsInt,
            HanaLang::Tuplen(TupleW(n)) => Instruction::Tuple(*n),
            HanaLang::Untuplen(UntupleW(n)) => Instruction::Untuple(*n),
            HanaLang::AsTuplen(AsTupleW(n)) => Instruction::AsTuple(*n),
            _ => return None,
        })
    }
}

/// The leaf data an e-node cannot carry: pushed values and called sentences.
///
/// A [`Value`] is neither `Ord` nor `Hash`, and a call's arity is a fact about
/// the library rather than about the node, so both are interned here and the
/// nodes carry indices. One session per proving run; the analysis owns it, so
/// every rule reaches it through the e-graph it was handed.
#[derive(Debug, Default)]
pub struct Session {
    values: Vec<Value>,
    /// Keyed by debug rendering, `Value` not being hashable. Two values with
    /// one rendering are one value: `Debug` shows ids and text in full.
    value_keys: HashMap<String, usize>,
    calls: Vec<(SentenceIndex, Arity)>,
    call_keys: HashMap<SentenceIndex, usize>,
}

impl Session {
    /// Interns a value, answering the leaf that names it.
    pub fn value(&mut self, v: &Value) -> PushW {
        let key = format!("{:?}", v);
        if let Some(&i) = self.value_keys.get(&key) {
            return PushW(i);
        }
        let i = self.values.len();
        self.values.push(v.clone());
        self.value_keys.insert(key, i);
        PushW(i)
    }

    /// The value a `push@i` leaf pushes.
    pub fn value_of(&self, w: PushW) -> &Value {
        &self.values[w.0]
    }

    /// Interns a call, answering the leaf that names it.
    pub fn call(&mut self, target: SentenceIndex, arity: Arity) -> CallW {
        if let Some(&i) = self.call_keys.get(&target) {
            return CallW(i);
        }
        let i = self.calls.len();
        self.calls.push((target, arity));
        self.call_keys.insert(target, i);
        CallW(i)
    }

    /// The sentence a `call@i` leaf calls, and its arity.
    pub fn call_of(&self, w: CallW) -> (SentenceIndex, Arity) {
        self.calls[w.0]
    }

    /// [`HanaLang::instruction`], extended to `push` by reading the session.
    pub fn instruction_of(&self, node: &HanaLang) -> Option<Instruction> {
        match node {
            HanaLang::Push(w) => Some(Instruction::Push(self.value_of(*w).clone())),
            other => other.instruction(),
        }
    }
}

/// What saturation knows about an e-class.
///
/// `arity` is the invariant — see the module docs. The rest are one-way facts
/// (false means "not known to hold", never "known not to"), each earning its
/// place by being the side condition of a rule:
///
/// - `is_id` / `is_drop` / `is_copy`: the class contains that structural leaf,
///   or something the facts compose to one. The width is the arity's.
/// - `yields_bool`: whatever this computes, its top output is a `Bool`. The
///   [`Instruction::yields_bool`] list, lifted through composition.
/// - `literal`: the class behaves as `id(inputs) * (push v1 ; … ; push vk)` —
///   it pushes exactly those values over an untouched stack. What the folding
///   rules read.
#[derive(Debug, Clone, PartialEq)]
pub struct Facts {
    pub arity: Arity,
    pub is_id: bool,
    pub is_drop: bool,
    pub is_copy: bool,
    pub yields_bool: bool,
    pub literal: Option<Vec<PushW>>,
}

impl Facts {
    fn leaf(arity: Arity) -> Facts {
        Facts {
            arity,
            is_id: false,
            is_drop: false,
            is_copy: false,
            yields_bool: false,
            literal: None,
        }
    }
}

/// The analysis a proving run's e-graph carries: the [`Session`] plus the
/// computation of [`Facts`].
#[derive(Debug, Default)]
pub struct Proving {
    pub session: Session,
}

impl Analysis<HanaLang> for Proving {
    type Data = Facts;

    fn make(egraph: &mut EGraph<HanaLang, Self>, enode: &HanaLang, _id: Id) -> Facts {
        let f = |id: &Id| egraph[*id].data.clone();
        match enode {
            HanaLang::Idn(IdW(n)) => Facts {
                is_id: true,
                // `id(0)` pushes nothing over an untouched stack, which is
                // what lets a literal prefix compose past it.
                literal: Some(vec![]),
                ..Facts::leaf(Arity::new(*n, *n))
            },
            HanaLang::Dropn(DropW(n)) => Facts {
                is_drop: true,
                ..Facts::leaf(Arity::new(*n, 0))
            },
            HanaLang::Copyn(CopyW(n)) => Facts {
                is_copy: true,
                ..Facts::leaf(Arity::new(*n, 2 * n))
            },
            HanaLang::Push(w) => Facts {
                yields_bool: matches!(egraph.analysis.session.value_of(*w), Value::Bool(_)),
                literal: Some(vec![*w]),
                ..Facts::leaf(Arity::new(0, 1))
            },
            HanaLang::Call(w) => Facts::leaf(egraph.analysis.session.call_of(*w).1),
            HanaLang::Compose([a, b]) => {
                let (fa, fb) = (f(a), f(b));
                debug_assert_eq!(
                    fa.arity.outputs, fb.arity.inputs,
                    "a compose node whose halves do not meet"
                );
                Facts {
                    arity: Arity::new(fa.arity.inputs, fb.arity.outputs),
                    is_id: fa.is_id && fb.is_id,
                    is_drop: (fa.is_id || fa.is_drop) && fb.is_drop
                        || fa.is_drop && fb.is_id && fb.arity.inputs == 0,
                    is_copy: fa.is_copy && fb.is_id,
                    // The suffix answers for the top of the stack; an identity
                    // suffix leaves the prefix's answer standing.
                    yields_bool: if fb.is_id && fb.arity.inputs > 0 {
                        fa.yields_bool
                    } else {
                        fb.yields_bool
                    },
                    // Both halves push over an untouched stack, so the pushes
                    // concatenate: the suffix's land on top.
                    literal: match (fa.literal, fb.literal) {
                        (Some(xs), Some(ys)) => Some(xs.into_iter().chain(ys).collect()),
                        _ => None,
                    },
                }
            }
            HanaLang::Par([a, b]) => {
                let (fa, fb) = (f(a), f(b));
                Facts {
                    arity: Arity::new(
                        fa.arity.inputs + fb.arity.inputs,
                        fa.arity.outputs + fb.arity.outputs,
                    ),
                    is_id: fa.is_id && fb.is_id,
                    is_drop: fa.is_drop && fb.is_drop,
                    is_copy: false,
                    yields_bool: if fb.arity.outputs > 0 {
                        fb.yields_bool
                    } else {
                        fa.yields_bool
                    },
                    // The deep side's pushes land under the shallow side's
                    // inputs, so this is a literal only when the shallow side
                    // reads nothing (its pushes then sit directly on the deep
                    // side's) or the deep side pushes nothing at all.
                    literal: match (&fa.literal, &fb.literal) {
                        (Some(xs), Some(ys)) if fb.arity.inputs == 0 => {
                            Some(xs.iter().chain(ys.iter()).copied().collect())
                        }
                        (_, Some(ys)) if fa.is_id => Some(ys.clone()),
                        _ => None,
                    },
                }
            }
            HanaLang::Branch([t, e]) => {
                let (ft, fe) = (f(t), f(e));
                debug_assert_eq!(ft.arity, fe.arity, "a branch node whose arms differ");
                Facts {
                    arity: Arity::new(ft.arity.inputs + 1, ft.arity.outputs),
                    yields_bool: ft.arity.outputs > 0 && ft.yields_bool && fe.yields_bool,
                    ..Facts::leaf(Arity::new(ft.arity.inputs + 1, ft.arity.outputs))
                }
            }
            prim => {
                let inst = prim
                    .instruction()
                    .expect("every remaining node is an instruction");
                let arity = Prim::from_instruction(&inst)
                    .expect("a lang instruction is always a prim")
                    .arity();
                Facts {
                    yields_bool: inst.yields_bool(),
                    ..Facts::leaf(arity)
                }
            }
        }
    }

    fn merge(&mut self, a: &mut Facts, b: Facts) -> DidMerge {
        // The soundness net: two spellings of one class must agree on their
        // stack effect. A rule that unioned across arities is a broken rule,
        // and this is the earliest place it can be caught.
        assert_eq!(
            a.arity, b.arity,
            "a rewrite united two classes with different stack effects"
        );
        let or = |a: &mut bool, b: bool| -> (bool, bool) {
            let a_gains = !*a && b;
            let b_loses = *a && !b;
            *a |= b;
            (a_gains, b_loses)
        };
        let mut a_changed = false;
        let mut b_changed = false;
        for (ac, bc) in [
            or(&mut a.is_id, b.is_id),
            or(&mut a.is_drop, b.is_drop),
            or(&mut a.is_copy, b.is_copy),
            or(&mut a.yields_bool, b.yields_bool),
        ] {
            a_changed |= ac;
            b_changed |= bc;
        }
        match (&a.literal, &b.literal) {
            (None, Some(_)) => {
                a.literal = b.literal;
                a_changed = true;
            }
            (Some(_), None) => b_changed = true,
            _ => {}
        }
        DidMerge(a_changed, b_changed)
    }
}

/// A proving run's e-graph.
pub type ProofGraph = EGraph<HanaLang, Proving>;

/// Writes a term into a [`RecExpr`], interning its leaves, and answers the id
/// of its root node.
pub fn term_to_expr(term: &Term, session: &mut Session, expr: &mut RecExpr<HanaLang>) -> Id {
    let node = match term {
        Term::Id(n) => HanaLang::Idn(IdW(*n)),
        Term::Drop(n) => HanaLang::Dropn(DropW(*n)),
        Term::Copy(n) => HanaLang::Copyn(CopyW(*n)),
        Term::Call { target, arity } => HanaLang::Call(session.call(*target, *arity)),
        Term::Op(prim) => match prim {
            Prim::Push(v) => HanaLang::Push(session.value(v)),
            Prim::Tuple(n) => HanaLang::Tuplen(TupleW(*n)),
            Prim::Untuple(n) => HanaLang::Untuplen(UntupleW(*n)),
            Prim::AsTuple(n) => HanaLang::AsTuplen(AsTupleW(*n)),
            other => other
                .to_instruction()
                .pipe_into_node()
                .expect("every dataless prim has a lang node"),
        },
        Term::Compose(a, b) => {
            let a = term_to_expr(a, session, expr);
            let b = term_to_expr(b, session, expr);
            HanaLang::Compose([a, b])
        }
        Term::Par(a, b) => {
            let a = term_to_expr(a, session, expr);
            let b = term_to_expr(b, session, expr);
            HanaLang::Par([a, b])
        }
        Term::Branch { if_true, if_false } => {
            let t = term_to_expr(if_true, session, expr);
            let e = term_to_expr(if_false, session, expr);
            HanaLang::Branch([t, e])
        }
    };
    expr.add(node)
}

/// The expression a term denotes, ready for [`egg::EGraph::add_expr`].
pub fn expr_of(term: &Term, session: &mut Session) -> RecExpr<HanaLang> {
    let mut expr = RecExpr::default();
    term_to_expr(term, session, &mut expr);
    expr
}

/// Reads an expression back into a [`Term`], for printing what an e-class
/// holds in the spelling the rest of the tool uses.
///
/// Built from the raw variants rather than the checking constructors: an
/// extracted expression came out of an e-graph whose analysis already asserted
/// every arity, and a residual printer must not panic on the thing it exists
/// to show.
pub fn expr_to_term(expr: &RecExpr<HanaLang>, session: &Session) -> Term {
    fn node(expr: &RecExpr<HanaLang>, id: Id, session: &Session) -> Term {
        match &expr[id] {
            HanaLang::Idn(IdW(n)) => Term::Id(*n),
            HanaLang::Dropn(DropW(n)) => Term::Drop(*n),
            HanaLang::Copyn(CopyW(n)) => Term::Copy(*n),
            HanaLang::Call(w) => {
                let (target, arity) = session.call_of(*w);
                Term::Call { target, arity }
            }
            HanaLang::Compose([a, b]) => Term::Compose(
                Box::new(node(expr, *a, session)),
                Box::new(node(expr, *b, session)),
            ),
            HanaLang::Par([a, b]) => Term::Par(
                Box::new(node(expr, *a, session)),
                Box::new(node(expr, *b, session)),
            ),
            HanaLang::Branch([t, e]) => Term::Branch {
                if_true: Box::new(node(expr, *t, session)),
                if_false: Box::new(node(expr, *e, session)),
            },
            prim => Term::Op(
                Prim::from_instruction(
                    &session
                        .instruction_of(prim)
                        .expect("a leaf that is not structural is an instruction"),
                )
                .expect("a lang instruction is always a prim"),
            ),
        }
    }
    node(expr, expr.root(), session)
}

/// A helper for [`term_to_expr`]: the lang node of a dataless instruction.
trait PipeIntoNode {
    fn pipe_into_node(self) -> Option<HanaLang>;
}

impl PipeIntoNode for Instruction {
    fn pipe_into_node(self) -> Option<HanaLang> {
        Some(match self {
            Instruction::Swap => HanaLang::Swap,
            Instruction::Equal => HanaLang::Equal,
            Instruction::Greater => HanaLang::Greater,
            Instruction::Less => HanaLang::Less,
            Instruction::Add => HanaLang::Add,
            Instruction::Subtract => HanaLang::Subtract,
            Instruction::Multiply => HanaLang::Multiply,
            Instruction::Divide => HanaLang::Divide,
            Instruction::Modulo => HanaLang::Modulo,
            Instruction::Not => HanaLang::Not,
            Instruction::Negate => HanaLang::Negate,
            Instruction::And => HanaLang::And,
            Instruction::Or => HanaLang::Or,
            Instruction::ConstStringLen => HanaLang::ConstStringLen,
            Instruction::ConstStringCharAt => HanaLang::ConstStringCharAt,
            Instruction::IsInt => HanaLang::IsInt,
            Instruction::IsBool => HanaLang::IsBool,
            Instruction::IsConstString => HanaLang::IsConstString,
            Instruction::IsSymbol => HanaLang::IsSymbol,
            Instruction::IsTuple => HanaLang::IsTuple,
            Instruction::TupleLength => HanaLang::TupleLength,
            Instruction::AsBool => HanaLang::AsBool,
            Instruction::AsInt => HanaLang::AsInt,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use egg::Language;

    fn probe_term() -> Term {
        // push 1 ; id(1) * push 2 ; add — the shape lowering produces.
        Term::pad_compose(
            Term::pad_compose(
                Term::op(Prim::Push(Value::Int(1))),
                Term::op(Prim::Push(Value::Int(2))),
            ),
            Term::op(Prim::Add),
        )
    }

    #[test]
    fn a_term_round_trips_through_the_expression() {
        let mut session = Session::default();
        let term = probe_term();
        let expr = expr_of(&term, &mut session);
        assert_eq!(expr_to_term(&expr, &session), term);
    }

    #[test]
    fn the_analysis_agrees_with_the_term_about_arity() {
        let term = probe_term();
        let mut egraph = ProofGraph::default();
        let mut expr = RecExpr::default();
        let mut session = Session::default();
        let root = term_to_expr(&term, &mut session, &mut expr);
        egraph.analysis.session = session;
        let class = egraph.add_expr(&expr);
        let _ = root;
        assert_eq!(egraph[class].data.arity, term.arity());
    }

    #[test]
    fn a_literal_prefix_is_read_off_the_class() {
        let term = probe_term();
        let mut egraph = ProofGraph::default();
        let mut session = Session::default();
        let expr = expr_of(&term, &mut session);
        egraph.analysis.session = session;
        let root = egraph.add_expr(&expr);
        // The whole term ends in `add`, which is no literal…
        assert_eq!(egraph[root].data.literal, None);
        // …but its literal prefix is one: `push 1 ; id(1) * push 2`.
        let mut session2 = Session::default();
        let prefix = expr_of(
            &Term::pad_compose(
                Term::op(Prim::Push(Value::Int(1))),
                Term::op(Prim::Push(Value::Int(2))),
            ),
            &mut session2,
        );
        let mut egraph2 = ProofGraph::default();
        egraph2.analysis.session = session2;
        let root2 = egraph2.add_expr(&prefix);
        let lit = egraph2[root2]
            .data
            .literal
            .clone()
            .expect("a literal prefix");
        let values: Vec<&Value> = lit
            .iter()
            .map(|w| egraph2.analysis.session.value_of(*w))
            .collect();
        assert_eq!(values, [&Value::Int(1), &Value::Int(2)]);
    }

    #[test]
    fn every_leaf_wrapper_round_trips_through_its_spelling() {
        assert_eq!("id@3".parse::<IdW>().unwrap(), IdW(3));
        assert_eq!(IdW(3).to_string(), "id@3");
        assert_eq!("as_tuple@2".parse::<AsTupleW>().unwrap(), AsTupleW(2));
        assert!("drop@x".parse::<DropW>().is_err());
        assert!("id@3".parse::<DropW>().is_err());
    }

    #[test]
    fn the_lang_nodes_cover_every_prim() {
        let mut session = Session::default();
        for prim in Prim::all() {
            let term = Term::op(prim.clone());
            let expr = expr_of(&term, &mut session);
            assert_eq!(expr_to_term(&expr, &session), term, "{}", prim);
            assert!(expr.root() == Id::from(expr.len() - 1));
            let node = &expr[expr.root()];
            assert!(node.children().is_empty(), "{} is a leaf", prim);
        }
    }
}
