# The tactic language

The rewrite language a proof drives one side of a goal with — the
`lhs(…)`, `rhs(…)` and `both(…)` steps of [docs/proving.md](proving.md)
— and the data model underneath it, in
[`lang/rewrite/src/tactic.rs`](../lang/rewrite/src/tactic.rs)
and [`query.rs`](../lang/rewrite/src/query.rs). A tactic
orchestrates rewrites; it is entirely untrusted. Every firing lands
through `Derivation::push` and is verified by `rules::apply`, so a buggy
tactic produces a refused step, never a wrong graph — a tactic run *is*
a derivation, replayable, and the addressing rules below are how the
current record keeps that property (see
[docs/invariants.md](invariants.md)).

## The surface

Inside `lhs(…)`, `rhs(…)` and `both(…)`, tactics are juxtaposed like
steps are:

| tactic | is |
|---|---|
| `saturate(law, …)` | those laws to fixpoint |
| `branches` | the branch layer to fixpoint |
| `decide` | the whole table to fixpoint — what the `diagram` closer drives |
| `tree` | `select-hoist` past everything but another branch, then `cond-hoist` out of every condition, to fixpoint — the decision tree |
| `fire(law, …)` | the first proposal of those laws, once — fails finding none |
| `at(#box, law)` | that law, once, in a match that holds **that box** — the address the residual printed |
| `at(selects-on(#wire), law)` | the same, once at **every branch that wire decides** — one firing per answer |
| `at(#box, law, backward)` | either aim, reading the law's equation right to left |
| `on(#wire …, law)` | that law stated onto named wires — the introduction whose bare side no search anchors |
| `repeat(t …)` | the sequence until it stops advancing |
| `try(t …)` | the sequence, or nothing — failure becomes no progress |

A law is named as [docs/rules.md](rules.md) names it — `fold`,
`select-same`, `not-not`; the spellings are `Law::name`'s, read both
ways, so a law added to the table is spellable the moment it is named.
`branching` names the one driven list with a name of its own. This surface is
deliberately smaller than the language underneath: queries and stated
backward steps exist as data first, and grow a spelling here when a
proof needs one.

Wherever commas separate — a law list, an `at`'s or an `on`'s fields,
and the sides of a `via` or a `cases` — **the last one is optional**:

```text
lhs(saturate(
    fold,
    not-not,
))
```

so a list written down the page gains a line without touching the one
above it. One separator is spared, and only at the end: a gap between two
commas names nothing, and each list says so in its own words.

Tactics are juxtaposed, and **no tactics is a run of none**: `lhs()` is
the step that leaves its side exactly as it stands, and so are `repeat()`
and `try()`. It is what a proof has while what it is going to say is
commented out —

```text
lhs(
    // at(#nkz, select-same)
)
```

— and the reason a list is the other way round: `fire()` names no law to
fire and `for()` no reader to send, each an argument missing rather than
a run of none, and each still says so.

### `fire` and `at`

`fire` takes the first match it is offered anywhere on the side, in the
canonical order. `at` is for when that is the wrong one: it names a box
by the address the **residual listing** printed beside it, and fires the
law in a match that holds that box — anywhere in the match, not only
where the law's pattern happens to anchor (`not-not` fired by naming its
second `not` is the small case; a whole-branch law named at a box inside
an arm is the one that matters). A goal offering nine `fold`s and
needing the seventh has no other proof to write.

One law is the exception, and for the reason that makes it special
everywhere else: `select-hoist` carries a **region** — the whole cone
below the box it fires at — as its payload. The boxes of that cone are
not the law's own window, they are what it moves, and every branch above
one of them carries it too. So "a match that holds that box" would name
as many equations as there are branches upstream, all but one of them
about a different branch, and `at` would spend the earliest of them
rather than the one written down. It anchors instead: the box named is
the branch that moves, and nothing else. (It is also the difference between microseconds and a
third of a second on a decision tree of a few hundred boxes, the sweep
having pinned a cone-sized pattern once per box in it.)

The direction field makes `at` a **found** backward step:
`at(#nkz, not-not, backward)` looks for the law's right-hand side. A
right-hand side is a graph like any other, so backward is a direction
like forward. What limits it is the payload: `instances` reads payloads
off the boxes the graph itself spells, so a rule whose payload nothing
in the graph names is not on offer. The failure says which.

An address is a box's **name**, and the name is what it computes: a
digest of the box's kind and of the addresses of what it reads, written
in twelve letters of a sixteen-letter alphabet — `z` for nought through
`k` for fifteen, which is Jujutsu's change ids, borrowed whole. A proof
writes as much of one as tells that box from the others on the page,
which is what the listing prints in **bold** on the box's own line and
what it prints wherever one box refers to another. Two or three letters,
in practice.

Being a fact about the computation rather than about the graph, an
address means the same box in every graph that computes it — the goal's
other side included, and the goal as the next step leaves it. What it
does not survive is a rewrite *under* the box, because a value made of
different values is a different value; so an `at` written off a report
is good exactly as long as the steps in front of it leave its box
computing what it computed. What it buys is that no other spelling of
"that one" exists. The name is not *held* across a rewrite either — it
is looked up live at every entry, and fails by name the moment nothing
answers to it (`NoSuchBox`) or two boxes do (`ManyBoxes`).

### `selects-on`, and why an `at` needs a set

A `select` carries **one answer** ([docs/rules.md](rules.md)), so a
`branch` leaving `n` values is `n` selects reading one condition. Every
row of the branch layer is about one of them. That makes "spend
`select-hoist` on this branch" `n` steps, and worse, `n` addresses a
proof can only get by reading them off a report — and `n` is not
something the proof wrote down anywhere.

`at(selects-on(in0), select-hoist)` is the branch named as a branch: the
wire, and every live `select` that turns on it. It is the same group the
listing draws one `if` around, which is what makes it writable from a
report — a reader sees one bracket and writes one aim.

The wire is spelled the way the listing prints one: `in0` for a boundary
input, `#nk` for output 0 of a box, `#nk.1` for a later port.

`select-hoist` is one of the two laws an `at` **anchors** rather than
sweeps for, so each of the firings lands on the select it was aimed at
and never on some other branch whose cone happens to hold it. The set and
the anchoring are the same idea at two scales: the address means the
branch it points at, and the aim means all of the branch.

Two details of the semantics, as they stand:

- The set is read **once, at entry**, and kept as addresses rather than
  ids. Ids because a firing rebuilds boxes; once because `select-hoist`
  puts down a fresh select on the very same condition for each answer
  its region leaves — a step that re-read the set between firings would
  find its own answers and never finish. What the step means is the
  branch as it stood when the step was reached.
- A member gone by its turn is skipped, not mourned: a firing at one
  answer may take another with it. A member still standing that the law
  cannot fire at is the loud case, and names the box.

The reading is **literal** — every select turning on that wire, port 0,
condition and never a block. A branch nested inside another that retests
the same wire turns on it too, and is in. The listing's bracket is the
outermost peers, which is a different question; where the two differ,
the aim is the wider one.

### `on`

`on(#nk in0, tuple-cancel)` states what no search can find. A law whose
one side is **bare wires** — `tuple-cancel`'s right side is `id(n)`
outright — has nothing there for the matcher to anchor on, so
introducing its window is a *statement*: the wires are named in order,
`#nk` a box's answer by the address the listing printed (`#nk.1` for a
later port), `in0` a boundary input, and the law's window goes in **on**
them. Every reader of each wire, the goal boundary included, comes to
read through the introduced pair; the order is the window's shape, so
`on(in1 in0, tuple-cancel)` builds the other tuple.

`on(#nk in0, specialize-equal)` is the other row on the table, and what
it puts in is a **branch**: the first wire tested against the second,
answering with the second where the test held and with the first where
it did not — which is the first wire either way, and why that side is
bare. Two wires exactly, and the order says both things at once: the
wire named first is the one every reader comes to read the branch for,
and the test reads the pair in the order they are named. `comm` is the
row that turns the test round afterwards.

The direction is the law's own — the bare side is the pattern, so
`tuple-cancel` reads backward — and writing it out is allowed and
checked rather than obeyed. Wire names follow `at`'s discipline: looked
up live at every entry rather than held, failing by name (`NoSuchBox`,
`ManyBoxes`, a port the box lacks) rather than firing somewhere else.
Stated on wires the pair already cancels, the step **compounds** — a
second trip stacks on the first, a true thing said one layer deeper, and
never an error — so a `repeat` around an `on` is the author claiming
what a `repeat` always claims. `rules::boxless` is the table of laws
`on` can state: a law both of whose sides hold boxes is not on it,
neither is one whose bare side would take more payload than a width, and
neither is a width at which the law's own side is not bare — `on` says
which of the three it is refusing.

What it is for: manifesting a window. A lemma proved about a packed
value cannot be spent in a goal that never packs until the shape exists;
a side that never packs meets one that does by stating the pair onto the
bare wires and letting `exact` or `decide` take both sides home.

### The library drives

Four drivers ship as library tactics — data a proof cites, not an
ordering an engine hardcodes.

- `saturate(law, …)` — those laws to fixpoint. Termination is the
  author's claim: the laws named have to be ones that shrink.
- `branches` — the branch layer in the order `rules::branching`
  documents. The phases loop *together*: one law of the layer
  unlocks another, so one `repeat` over the ordered list is the fixpoint
  said plainly.
- `decide` — both driven lists: the branch layer and the value layer. Not
  the whole table — the rows no list drives are the ones a driver could
  not run to fixpoint, and a proof names those. The closest thing to a
  normalizer, and still a strategy: those laws, in that order, replaceable
  by any proof that chooses differently.
- `tree` — `select-hoist` spent everywhere it will go, with one stop
  written into the body it carries, and then `cond-hoist` out of every
  condition a branch answered. See below.

### `tree`, and the body it carries

`select-hoist` says that what runs *after* a branch runs inside whichever
arm the branch takes ([docs/rules.md](rules.md)), and the region it moves
over rides as its payload. Which region that is, is a **strategy's**
decision rather than the table's, and the two readings that matter differ
by one thing:

- `fire(select-hoist)` takes the payload `rules::propose` reads, which is
  the whole cone below the select — branches in it included, copied along
  with everything else. That is what a proof asking for one firing wants.
- `tree` reads the same cone with every other `select` **left standing**:
  a branch is not copied, and not moved through another branch.

Spent to fixpoint, the second sorts a graph into two halves — the work,
which reads nothing a branch answers, and the branches, which read the
work and each other. The selects end up bunched at the output, and no
box but a select reads what a select answers.

### The other end of the same sorting

That leaves one port. A branch may still turn on what a branch
*answered* — a select in a **condition**, which is where `select-hoist`
cannot go without carrying the branch below as part of its region.
`cond-hoist` is the row for it ([docs/rules.md](rules.md)), and `tree`
spends it as its second alternative: a round tries a hoist first and
takes a `cond-hoist` only when no branch has anything left to grow over.

Two things follow from that order. What a `cond-hoist` copies is a
**branch** and never work, because by the time one fires every reader of
an answer is already a select. And it hands the first alternative
nothing back — the copies are read by the select it puts down, that
select is read by whoever read the branch that moved, and no box that is
not a select gains an answer to read — so the drive is one phase and
then the other, however the rounds interleave.

The fixpoint is two sentences: *no box but a select reads what a select
answers*, and *no select turns on what a select answered*. Between them
every condition in the graph is select-free — a test of the work,
decided before any branch runs — and the branches below are a tree. That
is a decision tree said in a graph.

Both phases terminate, and the arguments are in `tactic::tree`: a
multiset over what the copies read for the hoisting phase, and for the
condition phase the unfolded term weighted so that a condition costs
what it decides. The first of those is **not currently a proof**. It
leaned on a select never being copied, which held while a select carried
every answer of its branch; now that it carries one, a hoist over a
region leaving `m` answers puts down `m` selects where it found one, and
the multiset gains members rather than only losing them. Nothing is known
to diverge and the drive is held to the machine by test — `tree` run over
branches inside branches, before against after at every assignment — but
the measure wants restating.

The order is the drive's own, and it has to find one: a branch whose body
reads what a branch **below** it answers cannot go first, since the step
would hand that body's readers a new select the body itself feeds back
into. The tactic declines such a branch and takes another; one is always
available, because blocking runs downstream and the cone below a select
is finite, so the bottom of any chain of blocked branches is blocked by
nothing.

It **grows** a graph — which is why no list drives the row today — so a value
under `n` branches can end up written `2^n` times. This is for a goal
that wants its cases laid out, not for tidying a large one. It does
terminate: a hoist replaces each body box with two boxes reading that
branch's blocks rather than its answers, so each copy has strictly fewer
branches above it than the box it came from, and a multiset of naturals
with one member replaced by finitely many smaller ones decreases — with
the caveat above about the selects the step itself puts down.

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
no second embedding-search today — queries narrow and bind, and
`find_pinned`/`check_match` are the only isomorphism machinery in the
crate, which keeps the trusted part small; a second one would sit on the
untrusted side, and nothing rules it out. Payload wildcards live in the query layer and resolve by reading
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

The rule that makes the whole thing hang together today: **bindings do
not cross a rewrite**. A `Bindings` is consumed within one primitive
step, before any `apply`; persistence across steps is the query's job —
run it again. `NodeId`s shift meaning across rewrites, so the language
does not store one across a step; it stores the *description*, which is
exactly what "the copy feeding the add" is. (A record that named boxes
some other way could cache; this one re-runs, and search is cheap
enough that nothing has wanted otherwise.) (`at`'s aim is the one thing carried across steps today, and it is a name rather than an id — looked up against the
live graph at every entry rather than held. `selects-on` keeps a *list*
of names across its own firings, for the reason above, and they are names
too.)

### Found and stated steps

`find` declines a pattern that does not pin its own match: one with
**no boxes**, which has nothing to anchor on and whose image would be a
pure guess, and one with a boundary input nothing in it reads, which
cannot say what that input stands for. Those steps are **stated** rather
than found — `on` is the surface spelling for the bare-wires case.
Everything else is searchable in either direction — a substitution
re-points every reader of the value it replaces, so no pattern leaves a
reader-split for the host to settle. Where a proof *wants* a split, it
states one: a `for(…)`/`except(…)` clause on an `at` or an `on` resolves
to the match's `sel` — which readers of what the law leaves follow it —
and the checker holds that selection reader by reader, like the rest of
the claim.

A stated step is what is read, and nothing else:

```rust
// tactic.rs
/// A source, described rather than named — resolved against bindings
/// and the live graph at the moment the step fires.
pub enum SrcExpr {
    PortOf(Var, usize),      // output `port` of the bound node
    FeedOf(Var, usize),      // whatever input `port` of the bound node reads
    Input(usize),            // boundary input of the host
    Addressed(Prefix, usize),// output `port` of the box the written address
                             // names — `at`'s discipline: looked up live,
                             // never held, failing by name
}

/// The recipe for a stated Match against one side of one rule. Nothing
/// about outputs is said or sayable: a substitution re-points every
/// reader of the value it replaces, so there is no reader-split left to
/// state.
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
    /// `select-hoist` with the body read here rather than by `propose`:
    /// the cone below the bound select, every other select left
    /// standing. What `tree` spends first, and a **stated** step — the
    /// body was lifted off those very boxes, so the match is said
    /// rather than searched for. (`cond-hoist`, which `tree` spends
    /// second, needs none of this: its payload is three widths, so it
    /// is an ordinary `ReadOff`.)
    Hoist { anchor: Var },
}

pub enum Tactic {
    // ---- primitives ----
    /// Forward, found: query → anchor → propose → pick → apply.
    Fire { at: Query, rule: RuleSpec, pick: Pick },
    /// One law, one named box, either direction — the surface's `at`.
    /// The name is as much of the box's `Address` as somebody wrote,
    /// resolved against the side's live boxes at every entry.
    At { at: Prefix, law: Law, dir: Direction, pick: Pick },
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
  to symmetry" is a sharper query. A *found* match carries no choice of
  its own besides: a substitution re-points every reader of the value it
  replaces and leaves every reader of anything else alone, so search
  never has a split of a port's readers to decide. The one choice a
  match can carry is a **stated** reader selection (`for`/`except`),
  which a proof writes and the checker verifies; no search proposes one
  today, though one that did would carry it the same way.

### Failure and speculation

On any error, a run does not unwind committed work: the graph reflects
exactly the steps the derivation records, every one checked, so a failed
run leaves a well-formed graph a person can look at — the last state of
a rewrite in progress, with the derivation as provenance. A bare `Seq`
that fails at its third step leaves the first two applied, on purpose.
Primitives fail *before* mutating (`eval` and `resolve` are pure, and
`apply` checks to completion before splicing).

Backtracking is by **speculation on a clone** rather than by `undo`:
undoing puts boxes back with new ids, and under the id-based record a
history that went forward, undid, and went forward again would stop
being replayable. `Try` and each
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
the condition — the decided test's own making is what an arm
is scoped away from — plus the `select` itself, since the branch
layer's laws are read off it. Where more than one live select turns on
the wire, the **outermost** is the branch meant: the one the others lie
inside, which is the one a split introduced. Shared context is
*in*: a split duplicates only what lies downstream of its
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
rides `propose`, which seeds what the matcher needs — the literal. One
step and no cleanup after it: the untaken arm's boxes lose their reader
when the select goes, and a box the boundary does not reach is not in
the program.

## What is not here yet

- A surface spelling for queries, and for stated steps beyond `on`'s
  bare-wires slice — both exist as data only, and grow syntax when a
  proof needs it.
- Serialization for `Tactic` beyond the surface subset.
- Custom equations, or a hypothesis context. The seam sketched so far is
  a lemma with a stored derivation — `Rule::Lemma { lhs, rhs, warrant }` —
  but which comes first is open; see [docs/invariants.md](invariants.md).
