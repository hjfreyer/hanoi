# A tactics language for diagram rewriting

*A design proposal, since landed: `rewrite/src/diagram2/query.rs` and
`rewrite/src/diagram2/tactic.rs` implement what this document designs, and
the document has been trued up against what implementation taught. Where
the two disagree, the code and its tests are the record.*

`rewrite/src/diagram2` keeps a table of laws and the operations a driver is
built out of — `sides`, `find`, `propose`, `apply`, `replay` — and it
deliberately keeps no driver. The one it had was deleted on purpose: which
laws, where, and in what order is a strategy, and a strategy belongs to
whoever is proving something rather than to the module the graph lives in.
The module doc names the destination — "the driver comes back as a tactic
over both" — and this document designs that tactic language: its conceptual
model and its Rust shape. Concrete surface syntax is out of scope; every
construct below is a plain data type with an interpreter.

The vision, in one pass: a **query language** for pointing at sets of nodes
in a graph, a **splice specification** for saying which rewrite to make
there, and **combinators** — sequence, repeat, alternation, focus — for
building a derivation out of the two. Three questions have to be answered
squarely along the way: how queries are structured, how a query hands off
to subgraph-isomorphism finding, and what happens when the isomorphism is
ambiguous in a way that matters.

## Three commitments, inherited

The design is fitted to three facts the codebase already commits to, and
everything else follows from holding them.

**The trust boundary stays where it is.** `rules::sides` and `rules::apply`
are the whole of the trust: one builds the table, the other holds a claimed
embedding to agreeing at every port and then re-points. `find` and
`propose` are search — wrong the way a bad guess is wrong, and every answer
they give goes through `apply` anyway. The tactics layer joins the
untrusted side *entirely*. It mutates a graph through `Derivation::push`
and nothing else, so a buggy tactic produces a refused step, never a wrong
graph. One consequence is worth naming because it dissolves a question
rather than answering it: the crate-private mutation surface of
`diagram2::Graph` stays exactly as private as it is. The tactic engine
needs none of it.

**Backward steps are stated, not found.** `find` declines the patterns that
do not pin their own match — a pattern with no boxes has nothing to anchor
on (every rule's right-hand side but `not-not`'s), and a pattern that
exports one port twice leaves the split of that port's readers a choice
rather than a reading. Those are decisions, and they belong to whatever
writes a derivation. The test
`a_derivation_states_what_the_matcher_cannot_read` shows the idiom today: a
backward step is a hand-written `Match`. The deepest job of the query
language is to be the vocabulary such a statement is written in — bindings
are the nouns of a stated step.

**Strategy is data.** The deleted `saturate` comes back as a *program in
this language*, and the doc-comment knowledge that `select-view` unlocks
the rest of the branch layer comes back as a *library tactic* — data a
proof can cite, not an ordering an engine hardcodes.

Two new submodules, siblings of `rules.rs`:

```
rewrite/src/diagram2/query.rs    — Query, Bindings, eval      (untrusted search)
rewrite/src/diagram2/tactic.rs   — MatchSpec, Tactic, run     (untrusted orchestration)
```

Both are children of `diagram2` and could see its internals; by policy they
read through the public surface of `Graph` (`live`, `kind`, `sources`,
`sinks`, `outputs`, `is_live`) and drive the public operations of `rules`.

## The model in three layers

A **query** is a conjunctive relational pattern over the host graph: kind
predicates with payload blanks, structural relations, named variables.
Evaluating one yields bindings — name to node — in a canonical
deterministic order. A query is an *address*: it survives rewrites by being
run again, which is how stable addressing is had without inventing stable
ids.

A **splice** is never arbitrary. It is always `(Rule, Direction, Match)`
handed to the existing `apply`, reached one of two ways. *Found*, forward:
the query narrows to a seed node, and `propose`/`find_at` produce the
`Match` — the payload read off the host exactly as `read_off` does today.
*Stated*, either direction but above all backward: the tactic carries a
`MatchSpec`, a recipe that resolves against the query's bindings and the
current graph into a concrete `Match` — including the reader-split that
`Match::outputs` is a choice about.

**Combinators** — `Seq`, `First`, `Try`, `Repeat`, `Within` — glue steps
into a run. The interpreter threads `(&mut Graph, &mut Derivation)`, and
every firing lands through `Derivation::push`, so a tactic run *is* a
derivation: replayable by `replay`, undoable by `undo`, the valley-closing
property inherited rather than re-implemented.

Two boundaries are drawn now so they do not blur later. Custom equations —
a user-stated `lhs = rhs` beyond the `Law` table — are out of scope for the
first version. The design leaves one clean seam: a future
`Rule::Lemma { lhs, rhs, warrant }` whose `sides` returns the pair
verbatim, admissible only when the warrant checks — a stored derivation
from existing laws being the honest option. Nothing below changes if that
arrives. And the bridge to `hant` — a term-level proof step that drops an
equality goal into a graph derivation — is deferred; it slots in later as
one new `hant::Step` variant and constrains nothing here.

## Queries narrow and bind; the matcher matches

Two roads were open. A query language could be a full pattern language with
its own embedding search, subsuming `find`; or it could be a relational
filter that produces named bindings, leaving `find_at` and `check_match`
the only isomorphism machinery in the crate. The second is right, for
reasons the module docs already argue:

- A second embedding-finder is a second copy of the search, free to drift
  from the table. The one that exists is exercised by the law tests and
  every answer it gives is held to account by `check_match`.
- Rule sides are the only patterns whose replacement means anything. A
  query that matched an arbitrary subgraph would find things no rule can
  act on; the useful question is always *where could this law fire*, and
  `read_off` plus `find_at` answer it given a seed.
- The one thing a full pattern language buys — matching modulo payload
  wildcards — is better had the way `read_off` already has it: read the
  concrete payload off the host node the query bound, then match the
  *concrete* pattern. Wildcards live in the query and never reach the
  trusted path.

So the division of labour is: the query answers **where**, bound to names;
the table answers **what shape**; `apply` answers **whether**.

```rust
// query.rs

/// A named hole.
pub struct Var(pub &'static str);

/// What a bound node must be. Payload blanks are `None`.
pub enum KindPat {
    Id(Option<usize>), Copy(Option<usize>), Drop(Option<usize>),
    Op(Option<Prim>),
    AnyPush,                      // any literal
    Push(Value),                  // this literal
    Call(Option<SentenceIndex>),
    Fork, Select,
}

pub enum NodePred {
    Any,
    Kind(KindPat),
    Structural,                   // NodeKind::is_structural()
    Dead,                         // every output port unread
}

/// One conjunct. Every relation reads off the public Graph surface.
pub enum Atom {
    /// `var` is a live node satisfying `pred`.
    Is(Var, NodePred),
    /// Input `to_port` of `to` reads output `from_port` of `from`;
    /// `None` ports mean "some port".
    Feeds { from: Var, from_port: Option<usize>, to: Var, to_port: Option<usize> },
    /// `node`'s input `port` reads boundary input `input`.
    ReadsInput { node: Var, port: Option<usize>, input: Option<usize> },
    /// Output `port` of `node` is a boundary output.
    Exported { node: Var, port: Option<usize> },
    /// Output `port` of `node` has no readers at all.
    Unread { node: Var, port: usize },
    /// `fork` and `select` are the two ends of one branch.
    Paired { fork: Var, select: Var },
    /// Distinct nodes. Injectivity is otherwise not imposed.
    Ne(Var, Var),
}

pub struct Query { pub atoms: Vec<Atom> }

/// Only nodes are bound; sources and sinks are derived from them, which
/// keeps the environment one flat map.
pub struct Bindings(HashMap<Var, NodeId>);

/// All satisfying assignments, in canonical order.
pub fn eval(graph: &Graph, q: &Query) -> Vec<Bindings>;

/// `eval`, with every variable held to a region — how a focused tactic
/// scopes its queries, uniformly, rather than atom by atom.
pub fn eval_in(graph: &Graph, q: &Query, region: Option<&HashSet<NodeId>>) -> Vec<Bindings>;
```

Evaluation is the obvious backtracking conjunctive-query search, with the
same narrowing the matcher's own `candidates` uses: once one side of a
`Feeds` atom is bound, the other side is restricted to that port's readers
or source rather than the whole live graph. A builder API —
`Query::new().is("sel", …).feeds("lit", 0, "sel", 0)` — keeps authoring
bearable without committing to surface syntax.

The rule that makes the whole thing hang together: **bindings never cross a
rewrite**. A `Bindings` is consumed within one primitive step, before any
`apply`, and persistence across steps is the query's job — run it again.
`NodeId`s shift meaning across rewrites, so the language never stores one
across a step; it stores the *description*, which is exactly what "the copy
feeding the add" is.

## Handing off to the matcher

The forward pipeline: `eval` the query; take the designated anchor
variable's node as seed; `propose(graph, laws, seed)` — internally
`read_off`, then `find_at` — yields `Step`s; an optional post-filter
prunes; the selection policy picks; `Derivation::push` applies, and `apply`
validates.

One extension to `rules.rs` is wanted. `find_at` pins the pattern's box 0
to the seed, and `read_off` compensates by seeding where the pattern
anchors — for `select-literal` that is the literal, not the select the rule
is naturally *about*. A query, though, binds what is natural to say. Two
remedies, both cheap, both taken: route through `propose` wherever
possible, since `read_off` already computes the right seed for every law in
the table; and add the general form for query-driven matching of a stated
rule,

```rust
/// find_at, with pattern box `pat` — not necessarily 0 — pinned to `host`.
pub fn find_pinned(graph: &Graph, pattern: &Graph, pat: usize, host: NodeId) -> Vec<Match>
```

implemented by reordering the `Search` walk to visit `pat` first, with the
emitted `Match` staying in pattern index order. `find_at` becomes
`find_pinned(_, _, 0, _)`.

Payload wildcards need no matcher change at all: `KindPat::AnyPush` and its
kin resolve to concrete payloads by reading the bound host node, and only
concrete `Rule`s ever reach `sides`.

### Stating what cannot be found

A backward step is a statement, and every piece of the statement is either
a reading of the current graph or a genuine choice. `MatchSpec` separates
the two:

```rust
// tactic.rs

/// A source, described rather than named — resolved against bindings and
/// the live graph at the moment the step fires.
pub enum SrcExpr {
    /// Output `port` of the node bound to `var`.
    PortOf(Var, usize),
    /// Whatever input `port` of the bound node currently reads.
    FeedOf(Var, usize),
    /// Boundary input `i` of the host.
    Input(usize),
}

/// One boundary output's reader list, described. The reader-split choice
/// of `Match::outputs` is stated here, which is the point.
pub enum SinkSel {
    /// The input ports of the bound node that read the relevant source.
    ReadersAt(Var),
    /// A specific input port of a bound node.
    PortOf(Var, usize),
    /// Boundary output `i` of the host.
    Output(usize),
    /// Every reader not claimed by an earlier selector. At most one per spec.
    Rest,
}
// "no readers at all" is the empty selector list — it needs no variant.

/// The recipe for a stated Match against one side of one rule.
pub struct MatchSpec {
    /// Image of the pattern's boxes. Empty for every box-less side.
    pub nodes: Vec<Var>,
    /// One per pattern boundary input.
    pub inputs: Vec<SrcExpr>,
    /// One list per pattern boundary output.
    pub outputs: Vec<Vec<SinkSel>>,
    /// One per pattern branch id: a var bound to a Fork or Select,
    /// whose BranchId is read off.
    pub branches: Vec<Var>,
}

/// Pure reading; the result goes through `apply`, so a wrong resolution
/// is a refused step. The pattern is here because `ReadersAt` and `Rest`
/// select among the readers of what each boundary output stands for, and
/// the pattern's own outputs are what say which source that is.
fn resolve(graph: &Graph, pattern: &Graph, b: &Bindings, spec: &MatchSpec)
    -> Result<Match, TacticError>;
```

`Rest` is what keeps common statements short — "node `x` reads one leg of
the new copy, everyone else keeps reading the other" is two selectors —
without making the choice implicit: the author wrote `Rest`, and that is a
statement. Selectors resolve left to right, so `Rest` is well-defined; the
fullness condition in `check_match` is what holds the split to being
exhaustive and disjoint, so the spec needs no validation of its own beyond
one-`Rest`-at-most.

This is deliberately weaker than the matcher. A stated step can only place
*bound* nodes in the pattern image, so a backward step whose target side
contains boxes needs the query to have bound them. That is the right cost:
what the matcher cannot read, the derivation must literally say.

## Ambiguity

Three phenomena travel under this name and they get three policies.

**Disjoint alternatives.** When a query or a proposal set answers more than
once, selection is the combinator's job:

```rust
pub enum Pick {
    First,     // the canonically-first result; the workhorse
    Each,      // keep firing until the answer set is empty
    Unique,    // exactly one, or fail with Ambiguous { found }
}
```

The canonical order is part of the language's semantics, not an
implementation accident: bindings sort lexicographically by variable
declaration order then `NodeId`; matches sort by their `nodes` vector, ties
broken by the matcher's own discovery order, which is already
deterministic. Determinism is what makes a recorded derivation reproducible
from the tactic that wrote it — the same claim `replay` makes about ids
being handed out in order.

**Overlap.** A fired step deletes what it matched, so any other match
touching those boxes is stale; `apply` would refuse it, which is safe but
order-dependent in a way the author never chose. The policy is blunt: **the
interpreter never holds a `Match` or a `Bindings` across an `apply`**.
`Each` and `Repeat` re-run the query against the mutated graph after every
firing. This is the addressing discipline applied uniformly, it is how the
deleted `saturate` behaved — it re-proposed from a worklist rather than
caching matches — and it matches the economics: search is cheap and
untrusted, so spend it freely rather than engineering incremental match
maintenance. Termination is the author's claim, not the engine's theorem:
every structural law strictly shrinks the live box count, so saturating
them drains, but rather than encode measures, `Repeat` carries an optional
fuel — `None` claims termination, and exhausting an explicit fuel is a loud
error. Confluence is nowhere assumed. Different orders may land in
different graphs, and that is fine, because a tactic is a chosen strategy
rather than a normalizer, and the derivation records which road was taken.

**Ambiguity inside one match.** Two sub-cases, and the line between them is
the finding of this design:

- *Pattern automorphisms.* `dedup`'s left side is symmetric in its two
  boxes, so every real site matches twice, the two differing by the swap
  and the results isomorphic. Do not detect this. Detection is an
  automorphism-group computation whose only payoff is deduplicating a list
  that canonical ordering already makes deterministic; the derivation
  records the actual match, so the choice is auditable; and `Unique`
  intentionally *counts* automorphic duplicates as ambiguity — if an author
  needs "unique up to symmetry", the fix is a sharper query, and the error
  showing both matches is what makes that visible.
- *The reader-split.* When a pattern side exports one port twice, the split
  of the host's readers between the two boundary outputs is a genuine,
  result-changing choice — it decides which readers see which leg of a
  copy. The codebase has already located this correctly: `find` declines
  such patterns, so the split only ever arises in stated steps, where the
  `SinkSel` lists state it explicitly. No default, no inference, never
  silent.

Implementation turned up a third case of the reader-split's kind, and it
got the same treatment. `select-literal`'s kept side **skips** branch ids
so that a `BranchId` means the same branch on both sides of the equation —
which leaves it carrying an id no fork or select of its own witnesses. An
unwitnessed id cannot be read off a match, and its image in the host is a
genuine choice (applying that side backward *mints* the branch the other
side's select carries). So `pins_itself` declines such patterns too, and
they join the ranks of what a derivation states rather than reads.

The principle underneath: a deterministic default for the kind of ambiguity
that cannot matter, a mandatory statement for the kind that can.

## The tactic type and its interpreter

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
    /// Stated, either direction: query → resolve(MatchSpec) → apply.
    State { at: Query, rule: Rule, dir: Direction, with: MatchSpec, pick: Pick },

    // ---- combinators ----
    /// Each in order; fails when one fails.
    Seq(Vec<Tactic>),
    /// The first alternative that succeeds; a failed alternative leaves
    /// no trace (see speculation, below).
    First(Vec<Tactic>),
    /// Failure becomes Unchanged. The way to say "optional".
    Try(Box<Tactic>),
    /// Body until it reports Unchanged, or fails having landed nothing
    /// this round — which is how a saturation says it is done. `Some(n)`
    /// is fuel: a tripwire, not a budget, tripped loudly when an
    /// iteration advances past it (the over-fuel step stands — a fatal
    /// failure keeps its progress). `None` claims termination.
    Repeat(Box<Tactic>, Option<usize>),
    /// Scope every query inside `body` to a region.
    Within(Region, Box<Tactic>),
}

pub enum Progress { Advanced(usize), Unchanged }

pub enum TacticError {
    /// The query bound nothing, or propose offered nothing. A primitive
    /// that finds nothing FAILS — hant's discipline: loudly, so a proof
    /// that no longer matches says so. `Try` opts out.
    NothingFound { at: &'static str },
    Ambiguous { found: usize },
    /// `apply` refused a step the tactic constructed — a tactic bug,
    /// carried with the rules::Error so it can be read.
    Refused(rules::Error),
    Unresolved { var: Var },       // a spec named a var the query lacks
    OutOfRange { var: Var, port: usize },
    NoBranch { var: Var },         // a branch read off a branchless box
    ManyRests,                     // a spec said Rest twice
    OutOfFuel { after: usize },
}

/// Every mutation lands through `deriv.push`, so the run IS a Derivation.
pub fn run(graph: &mut Graph, deriv: &mut Derivation, t: &Tactic)
    -> Result<Progress, TacticError>;
```

The interpreter is plain recursion over the tree — author-written and
shallow — with iteration living inside `Each` and `Repeat` as
`loop { re-query; fire or break }`. There is no dedicated `Saturate`
primitive: `Repeat(Fire { any node, ReadOff(laws), First })` reconstructs
the deleted driver observably, and if the linear re-query per firing ever
hurts, `Saturate` arrives later as an *optimized spelling of that exact
tactic* — its steps still checked one at a time by `apply`, so it costs no
trust.

### A fatal failure leaves the graph standing

On any error, `run` does not unwind committed work. The real graph reflects
exactly the steps the derivation records, every one of which passed
`apply`'s checks, so a failed run leaves a well-formed graph a person can
look at — the last state of a rewrite in progress, with the derivation as
its provenance. The guarantee is structural rather than programmed:
primitives fail *before* mutating (`eval` and `resolve` are pure, and
`apply` runs `check_match` to completion before `splice` touches anything),
speculation happens on clones, and rollback exists only where a
combinator's semantics demand it — `First`'s failed alternatives, `Try`. A
bare `Seq` that fails at its third step leaves the first two applied, on
purpose.

### Speculation clones; the derivation only ever grows

`First` has to discard a failed alternative's partial progress, and the
tempting tool is `Derivation::undo`. It is the wrong tool, for a reason
worth recording: undoing puts boxes *back*, and a box put back is a new box
with a new `NodeId`. A history that went forward, undid, and went forward
again records later matches against ids that will never exist when the
derivation replays from the original graph — the derivation would stop
being replayable, which is the one property it exists to have.

So backtracking is by **speculation on a clone**. `Try` and each `First`
alternative run against a cloned graph and a cloned derivation (cloned
whole, so `LastImage` still sees the history). On failure, the clones are
dropped and nothing happened. On success, the speculative suffix replays
onto the real graph — which sits in exactly the state the clone started
from, and ids are handed out in order, so the steps land identically — and
is appended. `Graph` is `Clone` and small; the cost is one clone per
speculative alternative. `Derivation` stays a forward-only record, and
`undo` stays what it is: the valley-closer, not a backtracking stack.

### Regions

```rust
pub enum Region {
    /// The image of the immediately preceding step: the fresh boxes its
    /// recorded inverse names — data `apply` produced, not data the
    /// tactic guessed. (`Derivation::latest_undo` is the one accessor
    /// this took.)
    LastImage,
    // A Region::Arm — the boxes between a paired fork/select, computed
    // the way rules::arm computes them — is the natural next variant,
    // and nothing lands it until a tactic needs it.
}
```

A region resolves to a set of nodes when the focus is entered, and queries
are re-scoped to it at *each* evaluation. Its inheritance rule is semantic
content, so it is stated as doctrine: **the region is what the focus
produced plus what rewriting produced from it** — while inside a `Within`,
each new step's image joins the region, and deleted nodes leave it (a dead
id in the set binds nothing, since queries bind only live nodes).

### The branch layer's ordering, as data

What the `branching()` doc comment says in prose — `select-view` pulls
blocks out from behind a fork, and until it has, the rest of the layer has
nothing to match — becomes a library tactic:

```rust
/// The deleted driver, as a program: structural laws to fixpoint.
pub fn saturate_structural() -> Tactic;

/// The branch layer, spent to fixpoint with the structural cleanup it
/// needs: the branching laws in the order `rules::branching` documents,
/// structural behind them to spend what a branch rewrite leaves.
pub fn branch_pass() -> Tactic {
    Tactic::Repeat(
        Box::new(fire_first([rules::branching(), rules::structural()].concat())),
        None,
    )
}
```

(A phased spelling — `select-view` to fixpoint, then the rest, then
cleanup — is expressible as a `Seq` of `Repeat`s, but one law of the layer
unlocking another means the phases have to loop *together* to reach a
fixpoint, and one `Repeat` over the ordered list is that loop said
plainly. `branch { add } { add }` dissolving to a single `add` — fork-dedup,
then select-view, then select-same, then dead-node — is the test.)

## Three tactics, worked

**The deleted `saturate(structural())`, resurrected.**

```rust
fn fire_first(laws: Vec<Law>) -> Tactic {
    Tactic::Fire {
        at: Query::new().is("n", NodePred::Any),      // every live node, id order
        rule: RuleSpec::ReadOff { laws, anchor: Var("n") },
        pick: Pick::First,
    }
}

pub fn saturate_structural() -> Tactic {
    // Terminates: every structural law strictly shrinks the live box
    // count — the argument the old worklist's doc made.
    Tactic::Repeat(Box::new(fire_first(rules::structural())), None)
}
```

The semantics match the old driver up to firing order — the worklist popped
LIFO where this scans in id order, and both were unspecified strategy; now
the order is the language's documented canonical one.

**Directed: fold a literal condition, then clean up its image.**

```rust
Tactic::Seq(vec![
    // The select whose condition is a literal — and exactly one, or say so.
    Tactic::Fire {
        at: Query::new()
            .is("sel", NodePred::Kind(KindPat::Select))
            .is("lit", NodePred::Kind(KindPat::AnyPush))
            .feeds("lit", 0, "sel", 0),
        rule: RuleSpec::ReadOff { laws: vec![Law::SelectLiteral], anchor: Var("sel") },
        pick: Pick::Unique,
    },
    // Clean up inside the fold's image, and nowhere else.
    Tactic::Within(Region::LastImage, Box::new(saturate_structural())),
])
```

The query binds what is natural to *say* — the select — while `ReadOff`
rides `propose`'s `(rule, seed)` pairing, which seeds what the matcher
needs — the literal.

The image is smaller than a first reading suggests, and the test that
found this out is worth repeating. When the arms take nothing there is no
fork, and `arm` extracts each arm as a *wire*: the two literals are
"boxes the arm merely reads and does not own", so they sit outside the
window and survive the fold. The image is then just the re-spent
condition, which the focused cleanup collects — while the untaken arm's
literal, dead but **outside** the image, deliberately survives it. A
focus that collected it would not be a focus; the unfocused
`saturate_structural()` is what reaches it.

**Backward, stated: introduce a `copy(1)` on the wire feeding a node.**

```rust
Tactic::State {
    at: Query::new()
        .is("x", NodePred::Kind(KindPat::Op(Some(Prim::Add))))
        .reads_input("x", 0, 0),
    rule: Rule::CopyElim { n: 1 },
    dir: Direction::Backward,                     // rhs → lhs: the copy comes back
    with: MatchSpec {
        nodes: vec![],                            // copy-elim's rhs has no boxes
        // The rhs pattern's one boundary input: whatever x's port 0 reads.
        inputs: vec![SrcExpr::FeedOf(Var("x"), 0)],
        // The rhs exports that source twice; the split is the choice, so
        // it is STATED: x reads leg 0, everyone else keeps leg 1.
        outputs: vec![
            vec![SinkSel::PortOf(Var("x"), 0)],
            vec![SinkSel::Rest],
        ],
        branches: vec![],
    },
    pick: Pick::Unique,
}
```

`resolve` produces exactly the `Match` the existing test writes by hand,
`apply` holds the split to fullness, and the returned inverse — a forward
`copy-elim` at the fresh box — lands in the derivation, closing the valley.

## What changed in the existing code

Almost nothing, and that is a property being claimed, not a convenience.

- `rules.rs` gained `find_pinned` (`find_at` delegates to it; the walk
  visits the pinned box first, so a consumer can be placed before its
  producer — that edge defers to `check_match`, which holds every edge at
  the end either way), one accessor (`Derivation::latest_undo`, how a
  driver reads a step's image), and the third `pins_itself` decline
  (unwitnessed branch ids). Nothing in the trusted pair moved.
- `mod.rs` changed not at all beyond declaring the two modules. The query
  layer reads the public surface; the tactic layer mutates through
  `Derivation::push` alone, and the private mutation surface stays
  private.

The tests that hold this together: `saturate_structural()` restores the
coverage the driver's deletion gave up (meaning preserved across a run,
the structural layer gone, idempotence, a whole graph at every end, the
replay/undo valley); `a_pattern_is_found_from_any_of_its_boxes` pins every
side of the table at every box; the stated-step test re-derives
`a_derivation_states_what_the_matcher_cannot_read` from a spec, `Rest`
included; `speculation_leaves_no_trace` is the replayability claim run
against a failed alternative; `out_of_fuel_leaves_the_graph_standing` is
the fatal-failure invariant, asserted.

The `hant` bridge has since landed, and it ate more than a bridge: a
[goal](../rewrite/src/goal.rs) is two graphs now, the tactic language is
embedded in `.hant` strategies as `lhs(…)`, `rhs(…)` and `both(…)`, and
`exact`'s claim — with the auto-close that tests it before every step —
is whole-graph **isomorphism** (`diagram2::isomorphic`, a pinned-boundary
bijection search, verified link by link before it answers yes). The
surface (in [rewrite/src/hant.rs](../rewrite/src/hant.rs)) spells
`saturate`, `saturate(law, …)`, `branches`, `decide`, `fire(law, …)`,
`repeat(…)` and `try(…)`; queries and stated steps remain data-only until
a proof needs a spelling for them. `peel` and `descend` retired with the
term goal.

And the old engine has since retired outright: the table grew the value
layer (`fold` running the machine's own window, `tested-bool`, `retuple`,
`select-const`), the last-resort `view-value`, and the Shannon expansion —
η itself as a row, `body(w) = if w then body(true) else body(false)`, the
downstream region carried as payload the way `select-literal` carries
arms. `tactic::decide` drives the lists, the `diagram` proof step closes
by that drive plus isomorphism, and the `cases` proof step is untrusted
convenience that picks a wire and fires the Shannon row — nothing in the
prover touches a graph except through `Derivation::push`. `diagram.rs` is
deleted; [docs/proving.md](proving.md) tells that story.

Next, in order of want: a `Region::Arm`; surface spellings for queries
and stated (backward) steps; serialization for `Tactic` beyond the
surface subset; a stored, re-checkable derivation per closed identity.

## Open questions

- **Data or closures.** This design commits to a data AST, mirroring
  `hant::Step`: the stated destination is a driver written beside `.hant`
  proofs, and data is what a derivation can cite. Closures —
  `Fn(&Graph) -> Vec<Bindings>` in queries — would buy flexibility the
  first version does not need at the cost of that destination.
- **Custom equations.** Out of the first version. When they come, they come
  as lemmas with stored derivations, never as unvalidated pairs; the
  `meaning` oracle deliberately decides nothing and should stay that way.
- **`Within` inheritance.** New nodes joining the focused region is
  observable behaviour and is proposed as the rule; the alternative — a
  region frozen at entry — makes "saturate in the arms' image" impossible
  to say, which is the argument.
- **Where surface syntax lands.** A `graph { … }` step inside `.hant`
  files, or a sibling file type. Nothing above depends on the answer; it is
  named so the first version does not accidentally decide it.
