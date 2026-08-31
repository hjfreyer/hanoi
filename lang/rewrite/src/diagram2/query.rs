//! Pointing at boxes: a conjunctive query over one graph, answered with
//! named nodes.
//!
//! A tactic has to say *where* before it can say *what*, and a [`NodeId`]
//! cannot be the where: an id is meaningful only against the graph that
//! issued it, and a rewrite hands out new ones. So the address a tactic
//! holds is a **description** — "the literal feeding a select's condition"
//! — and the description is re-run against the graph as it now stands,
//! rather than a name held across a step. That is the one rule this module
//! is built around: a [`Bindings`] never crosses a rewrite. Whatever
//! consumes one does so before the next [`rules::apply`](super::rules), and
//! asks again after.
//!
//! A query is a conjunction of [`Atom`]s over named [`Var`]s: what kind of
//! box a variable is, who feeds whom at which port, what reads the
//! boundary, what nothing reads at all. It deliberately does **not** match
//! subgraphs. [`find_at`](crate::graph::find_at) is the one
//! embedding-finder there is, and a second would be a second copy of the
//! search, free to drift from the table; a query narrows to the box a rule
//! is anchored at — *where*, not *what shape* — and payload blanks like
//! [`KindPat::AnyPush`] are resolved by reading the concrete payload off
//! the bound node, so nothing wild ever reaches
//! [`rules::sides`](super::rules::sides).
//!
//! This is search, untrusted the way the matcher is untrusted: a query
//! that answers wrong seeds a step [`rules::apply`](super::rules::apply)
//! refuses, never a wrong graph.
//!
//! [`eval`] answers in a **canonical order** — bindings sorted by the
//! variables' first appearance in the query and then by [`NodeId`] — and
//! the order is part of the meaning, not an accident of the
//! implementation: it is what makes "the first match" a fact a recorded
//! derivation can be reproduced from.

use std::collections::{HashMap, HashSet};

use bytecode::{SentenceIndex, Value};

use crate::term::Prim;

use crate::graph::{Graph, NodeId, NodeKind, Sink, Source};

/// A named hole in a query. The name is the identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub &'static str);

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

/// What a bound node's [`NodeKind`] must be, blanks open.
///
/// A blank is `None`: `Copy(None)` is any copy, `Copy(Some(2))` is
/// `copy(2)`. [`KindPat::Op(None)`](KindPat::Op) is any prim — a literal
/// included, since a `push` is an op; [`KindPat::AnyPush`] is any literal
/// and [`KindPat::Push`] one literal in particular.
#[derive(Debug, Clone, PartialEq)]
pub enum KindPat {
    Op(Option<Prim>),
    AnyPush,
    Push(Value),
    Call(Option<SentenceIndex>),
    Select,
}

impl KindPat {
    /// Whether a box is what the pattern says, blanks matching anything.
    pub fn fits(&self, kind: &NodeKind) -> bool {
        match (self, kind) {
            (KindPat::Op(None), NodeKind::Op(_)) => true,
            (KindPat::Op(Some(p)), NodeKind::Op(q)) => p == q,
            (KindPat::AnyPush, NodeKind::Op(Prim::Push(_))) => true,
            (KindPat::Push(v), NodeKind::Op(Prim::Push(w))) => v == w,
            (KindPat::Call(want), NodeKind::Call { target, .. }) => {
                want.as_ref().is_none_or(|w| w == target)
            }
            (KindPat::Select, NodeKind::Select) => true,
            _ => false,
        }
    }
}

/// What a bound node must be, beyond its kind.
#[derive(Debug, Clone, PartialEq)]
pub enum NodePred {
    /// Any live box.
    Any,
    Kind(KindPat),
    /// Every output port unread — a box the program does not reach through
    /// any port it has. Nothing but a box with no ports at all can be one
    /// now: an unread value is not in the graph to be bound.
    Dead,
}

impl NodePred {
    pub fn holds(&self, graph: &Graph, id: NodeId) -> bool {
        let kind = graph.kind(id);
        match self {
            NodePred::Any => true,
            NodePred::Kind(pat) => pat.fits(kind),
            NodePred::Dead => (0..kind.arity().outputs)
                .all(|port| graph.sinks(Source::Port { node: id, port }).is_empty()),
        }
    }
}

/// One conjunct. Every relation here is a reading of the public surface of
/// [`Graph`] — `kind`, `sources`, `sinks`, `outputs` — and nothing more.
#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    /// The variable is a live node satisfying the predicate.
    Is(Var, NodePred),
    /// Input `to_port` of `to` reads output `from_port` of `from`. A
    /// `None` port means "some port".
    Feeds {
        from: Var,
        from_port: Option<usize>,
        to: Var,
        to_port: Option<usize>,
    },
    /// Input `port` of `node` reads boundary input `input`.
    ReadsInput {
        node: Var,
        port: Option<usize>,
        input: Option<usize>,
    },
    /// Output `port` of `node` is what a boundary output reads.
    Exported { node: Var, port: Option<usize> },
    /// Output `port` of `node` has no readers at all.
    Unread { node: Var, port: usize },
    /// Two distinct nodes. Distinctness is otherwise **not** imposed: two
    /// variables may bind one box, and a query that means two boxes says
    /// so.
    Ne(Var, Var),
}

impl Atom {
    /// The variables this conjunct mentions, in field order.
    fn vars(&self, mut note: impl FnMut(Var)) {
        match *self {
            Atom::Is(v, _) => note(v),
            Atom::Feeds { from, to, .. } => {
                note(from);
                note(to);
            }
            Atom::ReadsInput { node, .. }
            | Atom::Exported { node, .. }
            | Atom::Unread { node, .. } => note(node),
            Atom::Ne(a, b) => {
                note(a);
                note(b);
            }
        }
    }
}

/// A conjunction of atoms. [`eval`] is what it means.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Query {
    pub atoms: Vec<Atom>,
}

impl Query {
    pub fn new() -> Query {
        Query::default()
    }

    /// The variables, in order of first appearance — which is the outer
    /// key of the canonical order [`eval`] answers in.
    fn vars(&self) -> Vec<Var> {
        let mut out: Vec<Var> = Vec::new();
        for atom in &self.atoms {
            atom.vars(|v| {
                if !out.contains(&v) {
                    out.push(v);
                }
            });
        }
        out
    }

    // -- the builder, so a query in the middle of a tactic reads as what
    // it asks rather than as a pile of enum literals --

    pub fn is(mut self, v: &'static str, pred: NodePred) -> Query {
        self.atoms.push(Atom::Is(Var(v), pred));
        self
    }

    pub fn feeds(
        mut self,
        from: &'static str,
        from_port: impl Into<Option<usize>>,
        to: &'static str,
        to_port: impl Into<Option<usize>>,
    ) -> Query {
        self.atoms.push(Atom::Feeds {
            from: Var(from),
            from_port: from_port.into(),
            to: Var(to),
            to_port: to_port.into(),
        });
        self
    }

    pub fn reads_input(
        mut self,
        node: &'static str,
        port: impl Into<Option<usize>>,
        input: impl Into<Option<usize>>,
    ) -> Query {
        self.atoms.push(Atom::ReadsInput {
            node: Var(node),
            port: port.into(),
            input: input.into(),
        });
        self
    }

    pub fn exported(mut self, node: &'static str, port: impl Into<Option<usize>>) -> Query {
        self.atoms.push(Atom::Exported {
            node: Var(node),
            port: port.into(),
        });
        self
    }

    pub fn unread(mut self, node: &'static str, port: usize) -> Query {
        self.atoms.push(Atom::Unread {
            node: Var(node),
            port,
        });
        self
    }

    pub fn ne(mut self, a: &'static str, b: &'static str) -> Query {
        self.atoms.push(Atom::Ne(Var(a), Var(b)));
        self
    }
}

/// One satisfying assignment: variable to live node. Consumed before the
/// next rewrite, never after — persistence is the query's job, by being
/// run again.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bindings(HashMap<Var, NodeId>);

impl Bindings {
    pub fn get(&self, v: Var) -> Option<NodeId> {
        self.0.get(&v).copied()
    }

    /// The bound node, or a panic — for callers that know their own query.
    pub fn node(&self, v: Var) -> NodeId {
        self.get(v)
            .unwrap_or_else(|| panic!("{} is not bound by this query", v))
    }
}

/// Every satisfying assignment, in canonical order: variables by first
/// appearance in the query, candidates by [`NodeId`].
pub fn eval(graph: &Graph, q: &Query) -> Vec<Bindings> {
    eval_in(graph, q, None)
}

/// [`eval`], with every variable held to a region of the graph — what a
/// focused tactic scopes its queries by.
pub fn eval_in(graph: &Graph, q: &Query, region: Option<&HashSet<NodeId>>) -> Vec<Bindings> {
    let mut search = Eval {
        graph,
        q,
        region,
        vars: q.vars(),
        bound: HashMap::new(),
        found: Vec::new(),
    };
    search.walk(0);
    search.found
}

/// The backtracking search behind [`eval`]. Untrusted, like everything
/// here: it narrows where it can and checks every atom it can decide, and
/// what it misses costs a wasted candidate, not a wrong answer.
struct Eval<'g> {
    graph: &'g Graph,
    q: &'g Query,
    region: Option<&'g HashSet<NodeId>>,
    vars: Vec<Var>,
    bound: HashMap<Var, NodeId>,
    found: Vec<Bindings>,
}

impl Eval<'_> {
    fn walk(&mut self, i: usize) {
        if i == self.vars.len() {
            self.found.push(Bindings(self.bound.clone()));
            return;
        }
        let v = self.vars[i];
        for cand in self.candidates(v) {
            self.bound.insert(v, cand);
            if self.consistent() {
                self.walk(i + 1);
            }
            self.bound.remove(&v);
        }
    }

    /// Every atom whose variables are all bound holds; one still waiting
    /// on a variable abstains.
    fn consistent(&self) -> bool {
        self.q.atoms.iter().all(|a| self.holds(a).unwrap_or(true))
    }

    /// The nodes worth trying for one variable — the same narrowing the
    /// matcher's own candidate step does: a `Feeds` atom whose other side
    /// is already bound has only that side's neighbours to offer. Sorted,
    /// so the canonical order is by [`NodeId`] whichever road found them.
    fn candidates(&self, v: Var) -> Vec<NodeId> {
        let mut narrowed: Option<Vec<NodeId>> = None;
        for atom in &self.q.atoms {
            if let Atom::Feeds {
                from,
                from_port,
                to,
                to_port,
            } = *atom
            {
                if from == v
                    && let Some(&reader) = self.bound.get(&to)
                {
                    let cands = self
                        .graph
                        .sources(reader)
                        .iter()
                        .enumerate()
                        .filter(|(tp, _)| to_port.is_none_or(|want| want == *tp))
                        .filter_map(|(_, src)| match *src {
                            Source::Port { node, port }
                                if from_port.is_none_or(|want| want == port) =>
                            {
                                Some(node)
                            }
                            _ => None,
                        })
                        .collect();
                    narrowed = Some(cands);
                    break;
                }
                if to == v
                    && let Some(&maker) = self.bound.get(&from)
                {
                    let mut cands = Vec::new();
                    for port in 0..self.graph.kind(maker).arity().outputs {
                        if from_port.is_none_or(|want| want == port) {
                            for sink in self.graph.sinks(Source::Port { node: maker, port }) {
                                if let Sink::Port { node, .. } = sink {
                                    cands.push(node);
                                }
                            }
                        }
                    }
                    narrowed = Some(cands);
                    break;
                }
            }
        }
        let mut cands = narrowed.unwrap_or_else(|| self.graph.live().map(|(id, _)| id).collect());
        cands.sort_unstable();
        cands.dedup();
        if let Some(region) = self.region {
            cands.retain(|n| region.contains(n));
        }
        cands
    }

    /// Whether one atom holds, or `None` while a variable it mentions is
    /// still open.
    fn holds(&self, atom: &Atom) -> Option<bool> {
        let g = self.graph;
        let of = |v: Var| self.bound.get(&v).copied();
        Some(match *atom {
            Atom::Is(v, ref pred) => pred.holds(g, of(v)?),
            Atom::Feeds {
                from,
                from_port,
                to,
                to_port,
            } => {
                let (f, t) = (of(from)?, of(to)?);
                g.sources(t).iter().enumerate().any(|(tp, src)| {
                    to_port.is_none_or(|want| want == tp)
                        && matches!(*src, Source::Port { node, port }
                            if node == f && from_port.is_none_or(|want| want == port))
                })
            }
            Atom::ReadsInput { node, port, input } => {
                let n = of(node)?;
                g.sources(n).iter().enumerate().any(|(p, src)| {
                    port.is_none_or(|want| want == p)
                        && matches!(*src, Source::Input(i) if input.is_none_or(|want| want == i))
                })
            }
            Atom::Exported { node, port } => {
                let n = of(node)?;
                g.outputs().iter().any(|src| {
                    matches!(*src, Source::Port { node: m, port: p }
                        if m == n && port.is_none_or(|want| want == p))
                })
            }
            Atom::Unread { node, port } => {
                let n = of(node)?;
                g.sinks(Source::Port { node: n, port }).is_empty()
            }
            Atom::Ne(a, b) => of(a)? != of(b)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagram2::build;
    use crate::term::Context;
    use bytecode::assemble;

    /// The graph a body builds — the same probe the rules tests use.
    fn built(body: &str) -> Graph {
        let code = format!("sentence probe {{ {} }}", body);
        let library = assemble(&code).unwrap();
        let idx = library
            .names
            .iter_enumerated()
            .find(|(_, n)| *n == "probe")
            .map(|(idx, _)| idx)
            .unwrap();
        let mut terms = Context::new();
        let term = crate::term::lower(&mut terms, &library, idx).unwrap();
        let graph = build(&terms, term);
        graph.check().unwrap();
        graph
    }

    #[test]
    fn a_query_names_the_shape_it_describes() {
        let graph = built("push true branch { push 1 } { push 2 }");
        let q = Query::new()
            .is("sel", NodePred::Kind(KindPat::Select))
            .is("lit", NodePred::Kind(KindPat::AnyPush))
            .feeds("lit", 0, "sel", 0);
        let found = eval(&graph, &q);
        assert_eq!(found.len(), 1, "one select, one condition:\n{}", graph);
        let b = &found[0];
        assert!(matches!(graph.kind(b.node(Var("sel"))), NodeKind::Select));
        assert!(matches!(
            graph.kind(b.node(Var("lit"))),
            NodeKind::Op(Prim::Push(Value::Bool(true)))
        ));
    }

    /// The canonical order is variables by first appearance, candidates by
    /// id — stated as semantics, so a driver's "first" is reproducible.
    #[test]
    fn answers_come_in_id_order() {
        let graph = built("push 1 push 2 add");
        let q = Query::new().is("p", NodePred::Kind(KindPat::AnyPush));
        let found = eval(&graph, &q);
        assert_eq!(found.len(), 2);
        assert!(found[0].node(Var("p")) < found[1].node(Var("p")));
    }

    #[test]
    fn relations_read_what_the_graph_records() {
        let graph = built("branch { add } { subtract }");
        // One select, the whole of the branch.
        let ends = eval(
            &graph,
            &Query::new().is("s", NodePred::Kind(KindPat::Select)),
        );
        assert_eq!(ends.len(), 1, "one branch, one select:\n{}", graph);
        // Both arms read the very sources the branch was handed — there is
        // nothing between them and the stack, because there is no copy to
        // be.
        let arms = eval(
            &graph,
            &Query::new()
                .is("s", NodePred::Kind(KindPat::Select))
                .is("a", NodePred::Kind(KindPat::Op(Some(Prim::Add))))
                .is("b", NodePred::Kind(KindPat::Op(Some(Prim::Subtract))))
                .feeds("a", None, "s", None)
                .feeds("b", None, "s", None),
        );
        assert_eq!(arms.len(), 1, "one of each, one branch:\n{}", graph);
    }

    #[test]
    fn a_region_holds_every_variable_to_itself() {
        let graph = built("push 1 push 2 add");
        let q = Query::new().is("p", NodePred::Kind(KindPat::AnyPush));
        let all = eval(&graph, &q);
        assert_eq!(all.len(), 2);
        let only: HashSet<NodeId> = [all[1].node(Var("p"))].into_iter().collect();
        let scoped = eval_in(&graph, &q, Some(&only));
        assert_eq!(scoped.len(), 1);
        assert_eq!(scoped[0].node(Var("p")), all[1].node(Var("p")));
    }

    #[test]
    fn boundary_atoms_read_the_boundary() {
        let graph = built("not");
        let q = Query::new()
            .is("n", NodePred::Kind(KindPat::Op(Some(Prim::Not))))
            .reads_input("n", 0, 0)
            .exported("n", 0);
        assert_eq!(eval(&graph, &q).len(), 1);
        // And an unread port is one nothing reads, which no port of a
        // freshly built graph is.
        let q = Query::new().is("n", NodePred::Any).unread("n", 0);
        assert!(eval(&graph, &q).is_empty());
    }
}
