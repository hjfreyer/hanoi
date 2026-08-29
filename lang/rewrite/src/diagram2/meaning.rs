//! What a program means, with every operation left opaque.
//!
//! The judge the tests of this module use, and the reason they can claim
//! anything about *meaning* without borrowing [`crate::diagram`]'s
//! judgement. `add` on two wires stays `add(x, y)` and never becomes `7`,
//! so this decides nothing — it holds the wiring to account and stops
//! there. A [`Graph`] and the [`Term`] it came from can both be read this
//! way, which is what lets [`build`](super::build) and the rules table each
//! be held to preserving meaning separately.

use std::collections::HashMap;

use crate::graph::{Graph, NodeId, NodeKind, Source, schedule};
use crate::term::{Context, Prim, Term, TermIndex};

/// A name for one value in the symbolic reading of a program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct SymId(u32);

/// What a value *is*, with every operation left uninterpreted.
///
/// `add` on two wires is the node `add(x, y)` and never `7`: nothing is
/// run, so this decides no more equalities than the wiring forces. A
/// branch is a [`Sym::Choice`] **per output** rather than a split in
/// control — which is the same claim the graph makes with `select`, and
/// the reason there is no case tree here to explode.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Sym {
    /// Boundary input `i`.
    Var(usize),
    /// Output `out` of one opaque operation. `op` indexes [`Meaning::ops`];
    /// a call is opaque too, so nothing is ever opened.
    App {
        op: u32,
        args: Vec<SymId>,
        out: usize,
    },
    /// One of two values, according to `cond`.
    Choice {
        cond: SymId,
        if_true: SymId,
        if_false: SymId,
    },
}

/// An interning arena: two programs mean the same thing when they land on
/// the same [`SymId`].
///
/// Interning identifies `push 9 ; copy(1)` with `push 9 ; push 9`, which is
/// the δ-naturality the module itself has *not* bought. That only ever
/// makes an oracle more permissive, so it is safe here — but it is a fact
/// about this test scaffolding, not a position the engine has changed.
#[derive(Default)]
pub(super) struct Meaning {
    nodes: Vec<Sym>,
    seen: HashMap<Sym, SymId>,
    /// Operations by their printed form, since [`Prim`] is not hashable.
    ops: Vec<String>,
}

impl Meaning {
    fn intern(&mut self, node: Sym) -> SymId {
        if let Some(&id) = self.seen.get(&node) {
            return id;
        }
        let id = SymId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.seen.insert(node, id);
        id
    }

    fn var(&mut self, i: usize) -> SymId {
        self.intern(Sym::Var(i))
    }

    fn op(&mut self, name: String) -> u32 {
        match self.ops.iter().position(|held| *held == name) {
            Some(i) => i as u32,
            None => {
                self.ops.push(name);
                (self.ops.len() - 1) as u32
            }
        }
    }

    /// One opaque operation applied, answering with all of its outputs.
    fn apply(&mut self, name: String, args: Vec<SymId>, outputs: usize) -> Vec<SymId> {
        let op = self.op(name);
        (0..outputs)
            .map(|out| {
                self.intern(Sym::App {
                    op,
                    args: args.clone(),
                    out,
                })
            })
            .collect()
    }

    /// Two blocks of an answer paired position by position.
    ///
    /// A choice between one value **is** that value, and this knows it.
    /// That is not a fact about any operation — it holds of `Choice`
    /// itself, whatever the condition turns out to be — so knowing it keeps
    /// the oracle opaque while letting it judge `select-same`, which says
    /// exactly this.
    fn choose(&mut self, cond: SymId, if_true: &[SymId], if_false: &[SymId]) -> Vec<SymId> {
        assert_eq!(if_true.len(), if_false.len(), "the arms answer alike");
        if_true
            .iter()
            .zip(if_false)
            .map(|(&if_true, &if_false)| {
                if if_true == if_false {
                    return if_true;
                }
                self.intern(Sym::Choice {
                    cond,
                    if_true,
                    if_false,
                })
            })
            .collect()
    }
}

/// The name of the one operation a prim stands for — or, for `swap`, none:
/// `swap` is routing, and reading it as an opaque box would make the very
/// cancellation `swap-elim` performs look like a change of meaning.
fn opaque(prim: &Prim) -> Option<String> {
    match prim {
        Prim::Swap => None,
        other => Some(format!("{:?}", other)),
    }
}

/// What a term means, on the symbols standing for its inputs.
pub(super) fn eval_term(
    m: &mut Meaning,
    terms: &Context,
    term: TermIndex,
    stack: Vec<SymId>,
) -> Vec<SymId> {
    debug_assert_eq!(
        stack.len(),
        terms.arity(term).inputs,
        "the caller cuts by arity"
    );
    match terms.get(term) {
        Term::Id(_) => stack,
        Term::Drop(_) => Vec::new(),
        // Block-wise, as the box is.
        Term::Copy(_) => {
            let mut out = stack.clone();
            out.extend(stack);
            out
        }
        Term::Op(prim) => match opaque(prim) {
            None => vec![stack[1], stack[0]],
            Some(name) => m.apply(name, stack, prim.arity().outputs),
        },
        Term::Call { target, arity } => m.apply(format!("call {:?}", target), stack, arity.outputs),
        // Both spines are walked rather than recursed down. A lowered
        // sentence is one step per instruction folded left, and padding
        // makes each step a `*`-product over the whole width, so these
        // chains are as long as the term is wide and deep — recursion
        // overflows a test thread's stack on the corpus.
        Term::Compose(..) => {
            let mut spine = Vec::new();
            let mut head = term;
            while let Term::Compose(first, then) = terms.get(head) {
                spine.push(*then);
                head = *first;
            }
            let mut stack = eval_term(m, terms, head, stack);
            for step in spine.into_iter().rev() {
                stack = eval_term(m, terms, step, stack);
            }
            stack
        }
        Term::Par(..) => {
            let mut spine = Vec::new();
            let mut head = term;
            while let Term::Par(deep, top) = terms.get(head) {
                spine.push(*top);
                head = *deep;
            }
            // The stack is cut from the top down, since `spine` holds
            // the topmost factor first.
            let mut stack = stack;
            let parts: Vec<Vec<SymId>> = spine
                .iter()
                .map(|&factor| {
                    let width = terms.arity(factor).inputs;
                    stack.split_off(stack.len() - width)
                })
                .collect();
            let mut out = eval_term(m, terms, head, stack);
            for (&factor, part) in spine.iter().zip(parts).rev() {
                out.extend(eval_term(m, terms, factor, part));
            }
            out
        }
        // Both arms on the same stack, and a choice per output. With the
        // prims opaque that *is* what a branch means, so the hoist the
        // graph performs is invisible here — which is exactly what makes
        // this oracle linear where a case tree is not.
        Term::Branch { if_true, if_false } => {
            let mut stack = stack;
            let cond = stack.pop().expect("a branch reads its condition");
            let taken = eval_term(m, terms, *if_true, stack.clone());
            let not = eval_term(m, terms, *if_false, stack);
            m.choose(cond, &taken, &not)
        }
    }
}

/// What a graph means — the same reading, one box at a time.
///
/// Read off the graph itself, which is the point: this can hold a rewrite
/// to preserving meaning without a translation in the loop.
pub(super) fn eval_graph(m: &mut Meaning, graph: &Graph, inputs: &[SymId]) -> Vec<SymId> {
    let mut ports: HashMap<(NodeId, usize), SymId> = HashMap::new();
    let read = |ports: &HashMap<(NodeId, usize), SymId>, src: Source| match src {
        Source::Input(i) => inputs[i],
        Source::Port { node, port } => ports[&(node, port)],
    };
    for id in schedule(graph) {
        let args: Vec<SymId> = graph
            .sources(id)
            .iter()
            .map(|&src| read(&ports, src))
            .collect();
        let outs = match graph.kind(id) {
            NodeKind::Op(prim) => match opaque(prim) {
                None => vec![args[1], args[0]],
                Some(name) => m.apply(name, args, prim.arity().outputs),
            },
            NodeKind::Call { target, arity } => {
                m.apply(format!("call {:?}", target), args, arity.outputs)
            }
            NodeKind::Select { arity: n } => {
                let cond = args[0];
                let (taken, not) = (&args[1..=*n], &args[n + 1..=2 * n]);
                m.choose(cond, taken, not)
            }
        };
        for (port, sym) in outs.into_iter().enumerate() {
            ports.insert((id, port), sym);
        }
    }
    graph
        .outputs()
        .iter()
        .map(|&src| read(&ports, src))
        .collect()
}

/// Fresh symbols for `n` boundary inputs.
pub(super) fn boundary(m: &mut Meaning, n: usize) -> Vec<SymId> {
    (0..n).map(|i| m.var(i)).collect()
}
