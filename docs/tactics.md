# The tactic language

The rewrite language a proof drives one side of a goal with — the
`lhs(…)`, `rhs(…)` and `both(…)` steps of [docs/proving.md](proving.md)
— and the data model underneath it, in
[`lang/rewrite/src/diagram2/tactic.rs`](../lang/rewrite/src/diagram2/tactic.rs)
and [`query.rs`](../lang/rewrite/src/diagram2/query.rs). A tactic
orchestrates rewrites; it is entirely untrusted. Every firing lands
through `Derivation::push` and is verified by `rules::apply`, so a buggy
tactic produces a refused step, never a wrong graph — a tactic run *is*
a derivation, replayable, and the addressing rules below all serve that
property (see [docs/invariants.md](invariants.md)).

## The surface

Inside `lhs(…)`, `rhs(…)` and `both(…)`, tactics are juxtaposed like
steps are:

| tactic | is |
|---|---|
| `saturate(law, …)` | those laws to fixpoint |
| `branches` | the branch layer to fixpoint |
| `decide` | the whole table to fixpoint — what the `diagram` closer drives |
| `fire(law, …)` | the first proposal of those laws, once — fails finding none |
| `at(#box, law)` | that law, once, in a match that holds **that box** — the id the residual printed |
| `at(#box, law, backward)` | the same, reading the law's equation right to left |
| `repeat(t …)` | the sequence until it stops advancing |
| `try(t …)` | the sequence, or nothing — failure becomes no progress |

A law is named as [docs/rules.md](rules.md) names it — `fold`,
`select-same`, `not-not`; the spellings are `Law::name`'s, read both
ways, so a law added to the table is spellable the moment it is named.
`branching` names the one list with a name of its own. There is no bare
`saturate` any more: it stood for the wiring laws, and wiring is not a
list of laws now but a thing the representation cannot say. This surface is
deliberately smaller than the language underneath: queries and stated
backward steps exist as data first, and grow a spelling here when a
proof needs one.

### `fire` and `at`

`fire` takes the first match it is offered anywhere on the side, in the
canonical order. `at` is for when that is the wrong one: it names a box
by the id the **residual listing** printed beside it, and fires the law
in a match that holds that box — anywhere in the match, not only where
the law's pattern happens to anchor (`not-not` fired by naming its
second `not` is the small case; a whole-branch law named at a box inside
an arm is the one that matters). A goal offering nine `fold`s and
needing the seventh has no other proof to write.

The direction field makes `at` a **found** backward step:
`at(#7, not-not, backward)` looks for the law's right-hand side. This used
to find something only where that side pinned its own match, which most
did not — a side exporting one port twice left the split of that port's
readers a choice nothing in the host settled, so those steps had to be
stated. A substitution asks no such question, so a right-hand side is
looked for like any other graph and backward is a direction like forward.
What still limits it is the payload: `instances` reads payloads off the
boxes the graph itself spells, so a rule whose payload nothing in the
graph names is not on offer. The failure says which.

An id is an exact address and a brittle one, and both halves are the
point. A `NodeId` means one box of one graph at one moment, so an `at`
is written by reading a report and is only good against the goal that
report described: change a step in front of it and the ids behind it
move. (A box's *content* is now its identity, so a box that no rewrite
touched keeps its id — but a rewrite rebuilds everything downstream of
what it replaced, and those boxes are new.) What it buys is that no other spelling of "that one" exists. The
id is never *held* across a rewrite either — it is checked live at every
entry and fails by name, `NoSuchNode`, the moment its box is gone.

### The library drives

Three drivers ship as library tactics — data a proof cites, not an
ordering an engine hardcodes. There were four: the wiring saturation is
gone, because a graph arrives with nothing to sweep.

- `saturate(law, …)` — those laws to fixpoint. Termination is the
  author's claim: the laws named have to be ones that shrink.
- `branches` — the branch layer in the order `rules::branching`
  documents. The phases loop *together*: one law of the layer
  unlocks another, so one `repeat` over the ordered list is the fixpoint
  said plainly.
- `decide` — the whole table: the branch layer and
  the value layer. The closest thing to a normalizer, and still a
  strategy: those laws, in that order, replaceable by any proof that
  chooses differently.

## The model underneath

Three layers, all plain data with an interpreter:

- a **query** points at nodes: a conjunctive relational pattern over the
  host graph — kind predicates with payload blanks, structural
  relations, named variables. Evaluating one yields bindings (name →
  node) in a canonical deterministic order. A query is an *address*: it
  survives rewrites by being run again.
- a **step** is never arbitrary: always `(Rule, Direction, Match)`
  handed to `apply`, reached one of two ways. *Found*: the query narrows
  to a seed node and `propose`/`find_pinned` produce the `Match`.
  *Stated*: the tactic carries a `MatchSpec`, a recipe resolved against
  the bindings and the live graph into a concrete `Match`.
- **combinators** glue steps into a run. The interpreter threads
  `(&mut Graph, &mut Derivation)`, and every firing lands through
  `Derivation::push`.

The division of labour: the query answers **where**, bound to names; the
table answers **what shape**; `apply` answers **whether**. There is
deliberately no second embedding-search — queries narrow and bind, and
`find_pinned`/`check_match` remain the only isomorphism machinery in the
crate. Payload wildcards live in the query layer and resolve by reading
the bound host node; only concrete `Rule`s ever reach `sides`.

### Queries

```rust
// query.rs
pub struct Var(pub &'static str);

pub enum KindPat {
    Op(Option<Prim>),
    AnyPush,                      // any literal
    Push(Value),                  // this literal
    Call(Option<SentenceIndex>),
    Select,
}

pub enum NodePred {
    Any,
    Kind(KindPat),
    Dead,                         // every output port unread
}

/// One conjunct. Every relation reads off the public Graph surface.
pub enum Atom {
    Is(Var, NodePred),
    Feeds { from: Var, from_port: Option<usize>, to: Var, to_port: Option<usize> },
    ReadsInput { node: Var, port: Option<usize>, input: Option<usize> },
    Exported { node: Var, port: Option<usize> },
    Unread { node: Var, port: usize },
    Ne(Var, Var),
}

pub struct Query { pub atoms: Vec<Atom> }
pub struct Bindings(HashMap<Var, NodeId>);

/// All satisfying assignments, in canonical order.
pub fn eval(graph: &Graph, q: &Query) -> Vec<Bindings>;
/// `eval`, with every variable held to a region — how a focused tactic
/// scopes its queries uniformly.
pub fn eval_in(graph: &Graph, q: &Query, region: Option<&HashSet<NodeId>>) -> Vec<Bindings>;
```

Evaluation is backtracking conjunctive-query search, narrowed the way
the matcher's own candidate search is: once one side of a `Feeds` atom
is bound, the other side is restricted to that port's readers or source.
A builder API — `Query::new().is("sel", …).feeds("lit", 0, "sel", 0)` —
keeps authoring bearable.

The rule that makes the whole thing hang together: **bindings never
cross a rewrite**. A `Bindings` is consumed within one primitive step,
before any `apply`; persistence across steps is the query's job — run it
again. `NodeId`s shift meaning across rewrites, so the language never
stores one across a step; it stores the *description*, which is exactly
what "the copy feeding the add" is. (`at`'s named box is the one
deliberate exception, and it is re-checked at every entry rather than
held.)

### Found and stated steps

`find` declines a pattern with **no boxes**: there is nothing to anchor
on, and its image would be a pure guess. Those splices are **stated**
rather than found.

There used to be a second decline, and it was the interesting one: a
pattern that exported **one port twice** left the split of that port's
readers a genuine, result-changing choice, so most right-hand sides
could not be looked for and a backward step was usually a statement. A
substitution re-points every reader of the value it replaces, so the
question is not asked and the decline is gone.

A stated step is what is read, and nothing else:

```rust
// tactic.rs
/// A source, described rather than named — resolved against bindings
/// and the live graph at the moment the step fires.
pub enum SrcExpr {
    PortOf(Var, usize),   // output `port` of the bound node
    FeedOf(Var, usize),   // whatever input `port` of the bound node reads
    Input(usize),         // boundary input of the host
}

/// The recipe for a stated Match against one side of one rule.
pub struct MatchSpec {
    pub nodes: Vec<Var>,             // image of the pattern's boxes
    pub inputs: Vec<SrcExpr>,        // one per pattern boundary input
}

/// Pure reading; the result goes through `apply`, so a wrong resolution
/// is a refused step.
fn resolve(graph: &Graph, b: &Bindings, spec: &MatchSpec)
    -> Result<Match, TacticError>;
```

A stated step can only place *bound* nodes in the pattern image, so a
backward step whose target side contains boxes needs the query to have
bound them — what the matcher cannot read, the derivation must literally
say.

### The tactic type

```rust
// tactic.rs
pub enum RuleSpec {
    /// A payload stated outright, anchored by pinning pattern box `pin`
    /// to the box the query bound — the `find_pinned` path.
    Concrete { rule: Rule, anchor: Var, pin: usize },
    /// Read the payload off the bound anchor, law by law — the propose
    /// path. Wildcards resolve here.
    ReadOff { laws: Vec<Law>, anchor: Var },
}

pub enum Tactic {
    // ---- primitives ----
    /// Forward, found: query → anchor → propose → pick → apply.
    Fire { at: Query, rule: RuleSpec, pick: Pick },
    /// One law, one named box, either direction — the surface's `at`.
    At { node: NodeId, law: Law, dir: Direction, pick: Pick },
    /// Stated, either direction: query → resolve(MatchSpec) → apply.
    State { at: Query, rule: Rule, dir: Direction, with: MatchSpec, pick: Pick },

    // ---- combinators ----
    /// Each in order; fails when one fails.
    Seq(Vec<Tactic>),
    /// The first alternative that succeeds; a failed alternative leaves
    /// no trace (speculation, below).
    First(Vec<Tactic>),
    /// Failure becomes Unchanged — the way to say "optional".
    Try(Box<Tactic>),
    /// Body until it reports Unchanged. `Some(n)` is fuel — a tripwire,
    /// tripped loudly; `None` claims termination.
    Repeat(Box<Tactic>, Option<usize>),
    /// Scope every query inside `body` to a region.
    Within(Region, Box<Tactic>),
}

pub enum Progress { Advanced(usize), Unchanged }
```

A primitive that finds nothing **fails** — loudly, so a proof that no
longer matches says so; `Try` opts out. `apply` refusing a step the
tactic constructed is a tactic bug and is carried as one
(`Refused(rules::Error)`), never papered over.

`At` deserves its own note: `rules::instances(graph, law)` sweeps every
live box for the payloads the graph's own boxes spell, and
`graph::find_over` looks for the chosen side with each of its pattern
boxes pinned in turn to the named node — which is what lets a match
count wherever it *holds* that box, and lets `dir` look for either side
of the equation.

### Ambiguity

Three phenomena, three policies:

- **Disjoint alternatives.** When a query or proposal set answers more
  than once, selection is the combinator's job:

  ```rust
  pub enum Pick {
      First,     // the canonically-first result; the workhorse
      Each,      // keep firing until the answer set is empty
      Unique,    // exactly one, or fail with Ambiguous { found }
  }
  ```

  The canonical order is part of the language's semantics: bindings sort
  by variable declaration order then `NodeId`; matches by their `nodes`
  vector, ties broken by the matcher's own deterministic discovery
  order. Determinism is what makes a recorded derivation reproducible
  from the tactic that wrote it.

- **Overlap.** A fired step deletes what it matched, so any other match
  touching those boxes is stale. The policy is blunt: the interpreter
  never holds a `Match` or a `Bindings` across an `apply` — `Each` and
  `Repeat` re-run the query against the mutated graph after every
  firing. Search is cheap and untrusted; spend it freely. Confluence is
  nowhere assumed: different orders may land in different graphs, and
  that is fine, because a tactic is a chosen strategy rather than a
  normalizer, and the derivation records which road was taken.

- **Ambiguity inside one match.** Pattern automorphisms are deliberately
  *not* detected: canonical ordering already makes the list
  deterministic, the derivation records the actual match, and `Unique`
  intentionally counts automorphic duplicates — the fix for "unique up
  to symmetry" is a sharper query. There used to be a second kind here,
  the reader-split, and it was the one genuine *choice* a match carried:
  which of a port's outside readers belonged to the window. A
  substitution re-points every reader of the value it replaces, so
  nothing is left to choose.

### Failure and speculation

On any error, a run does not unwind committed work: the graph reflects
exactly the steps the derivation records, every one checked, so a failed
run leaves a well-formed graph a person can look at — the last state of
a rewrite in progress, with the derivation as provenance. A bare `Seq`
that fails at its third step leaves the first two applied, on purpose.
Primitives fail *before* mutating (`eval` and `resolve` are pure, and
`apply` checks to completion before splicing).

Backtracking is by **speculation on a clone**, never by `undo`: undoing
puts boxes back with new ids, and a history that went forward, undid,
and went forward again would stop being replayable. `Try` and each
`First` alternative run against a cloned graph and derivation; on
failure the clones are dropped and nothing happened, on success the
speculative suffix replays onto the real graph — ids are handed out in
order, so the steps land identically — and is appended. The derivation
stays a forward-only record.

### Regions

```rust
pub enum Region {
    /// The image of the immediately preceding step: the fresh boxes its
    /// recorded inverse names — data `apply` produced, not guessed.
    LastImage,
    /// One side of a branch, computed fresh at every entry. The branch
    /// is named by the wire it turns on, since a rewrite that narrows a
    /// select puts down a new box with a new id.
    Arm { cond: Source, side: bool },
}
```

A region resolves to a set of nodes when the focus is entered, and
queries are re-scoped to it at *each* evaluation. Membership is dynamic
by doctrine: **the region is what the focus produced plus what
rewriting produced from it** — each new step's image joins the region,
and deleted nodes leave it (a dead id binds nothing, since queries bind
only live nodes).

`Arm` is what a structured `cases` arm runs `Within`
([docs/proving.md](proving.md)). Its membership is the arm's **cone**:
everything upstream of that side's blocks, minus everything upstream of
the condition — the decided test's own making is exactly what an arm
must not touch again — plus the `select` itself, since the branch
layer's laws are read off it. Where more than one live select turns on
the wire, the **outermost** is the branch meant: the one the others lie
inside, which is the one a split introduced. Shared context is
deliberately *in*: a split duplicates only what lies downstream of its
wire, so the tests a nested split must reach sit upstream, shared
between the copies, and a region that evicted them would let an arm
spend its hypothesis but never decompose it. The region scopes *anchors*, not windows — a law fired
from inside may still hold boxes outside in its match, and soundness is
`apply`'s either way.

## One tactic, worked

**Directed: fold a literal condition, and nothing after it.**

```rust
Tactic::Fire {
    at: Query::new()
        .is("sel", NodePred::Kind(KindPat::Select))
        .is("lit", NodePred::Kind(KindPat::AnyPush))
        .feeds("lit", 0, "sel", 0),
    rule: RuleSpec::ReadOff { laws: vec![Law::SelectLiteral], anchor: Var("sel") },
    pick: Pick::Unique,
}
```

The query binds what is natural to *say* — the select — while `ReadOff`
rides `propose`, which seeds what the matcher needs — the literal.

There was a second step here once, a focused wiring sweep to collect
what the fold had orphaned, and a paragraph about why the untaken arm
survived it. Neither is a thing any more: the untaken arm's boxes lose
their reader when the select goes, and a box the boundary does not reach
is not in the program. There is nothing to collect, and so nothing to
scope a collection to.

## What is not here yet

- A surface spelling for queries and for the stated steps — both exist
  as data only, and grow syntax when a proof needs it.
- Serialization for `Tactic` beyond the surface subset.
- Custom equations. When they come, they come as lemmas with stored
  derivations — the `Rule::Lemma { lhs, rhs, warrant }` seam — never as
  unvalidated pairs; see [docs/invariants.md](invariants.md).
