# Invariants of the prover

The commitments everything else is built on. The other pages say how to
use the prover ([docs/proving.md](proving.md)), what the laws mean
([docs/rules.md](rules.md)), and how to drive them
([docs/tactics.md](tactics.md)); this page is the short list of
properties that must survive any refactor, each with where it lives —
and, after it, a second list of choices that hold today for reasons
given, which a refactor is free to revisit.

## The trust boundary

Trusted, and the whole of it:

- `rules::sides` — builds a law's two graphs from its payload;
- `rules::apply` — holds a claimed embedding to agreeing at every port
  before re-pointing anything (`check_match`, then `Pair::apply`);
- `graph::isomorphic` — answers `true` only after verifying its
  bijection link by link;
- the machine itself, where a law is *about* what an operation computes —
  `fold` consults `run_window`, the real `vm`.

Everything else — `find`, `propose`, drivers, tactics, queries, the
`cases` step's wire-picking, strategy interpretation — is untrusted
search. It mutates a graph through `Derivation::push` and nothing else,
so every step it produces goes through `apply`, and a buggy tactic yields
a refused step, never a wrong graph. `Graph`'s mutation surface stays
crate-private; the tactic layer needs none of it.

## The rewriter reads the machine rather than restating it

Facts about instructions live **on the instruction** and are measured by
`vm` — `truthy`, `op_arity`, `yields_bool`, `commutative`, `idempotent` —
and the rewriter reads them there rather than keeping its own. A row may
read one to stand for a whole family (`comm`, `idem`, `tested-bool`),
which is the same discipline seen from the other end: the table asks the
instruction set which instructions a law is about instead of naming them
itself. `fold` executes its window on a scratch VM rather than
reimplementing any operation. A law that turns on what the machine
computes is tested against `vm`. What holds the wiring laws is the corpus:
`strategy`'s tests pin which of `hana`'s identities the bare table decides,
so a law that stopped saying something true stops closing a claim.

This is a strong preference rather than a prohibition, and the reason
for it is where these facts sit: on the trusted side, where a wrong one —
`subtract` listed as commutative, a `fold` that computes something the
machine does not — permits an unsound rewrite that nothing downstream
catches. One copy is the cheapest way to keep that from drifting. A rule
that finds it easier to carry its own copy of a fact may, provided a test
measures the copy against `vm` the way `commutative` and `yields_bool`
are themselves measured, so that drift fails a test rather than a proof.

## Side conditions are carried by interfaces, never tested

A rule's pattern boundary says what the rule is *about*, and a rule that
wants a shape says it in the pattern rather than testing for it —
`select-hoist` exports its body's outputs and carries the region it moves
as payload, `select-literal` carries its arms. Nothing asks a
question a match could answer. New rules follow the same discipline.

What a boundary does **not** say is *and nothing else reads this*. A
rewrite replaces the value a window exports and rebuilds whatever read
it, so a reader the window never mentioned is not a loose end: `not-not`
fires on a first `not` somebody else reads, and that somebody goes on
reading the box it always read.

A match never *has* to say which readers belong to the window, but a
proof *may* state which readers follow: a `Match` carries an optional
reader selection (`sel`, the surface's `for`/`except`), and the
substitution then re-points exactly the named sinks, every other reader
keeping the box it always read. Nothing is destroyed either way, which
is why the selection costs pointwise checks — each named sink reads the
very port it is named for — and nothing global. What the discipline asks
is only that the choice be a stated payload of the step, carried by its
interface, rather than a question a match answers by testing; where the
choice comes from is open (today, only from a proof — see below).

## Totality, purity and determinism are load-bearing

- Discarding work (a box the boundary does not reach, and every branch's
  untaken arm) is licensed by **totality and purity**: discarded work
  cannot fail and cannot be observed.
- Sharing work (interning: one box per computation, however many read it)
  is licensed by **determinism and purity**: running twice is running
  once.

Neither is a law that fires, and that is exactly why the licenses are
stated here rather than beside a row: both are properties of the
representation. A value is named by what it is, and a value nothing
names is not there. If a partial instruction ever arrives, discard stops
being sound and the graph would have to record what it currently
forgets; if an effectful or nondeterministic one arrives, interning
goes, and with it the whole model.

No instruction may be added without revisiting the table against this
list.

## Derivations replay

A derivation replays from its original graph and lands identically —
that is the property it exists to have, and `Proof::check` is built on
it. What that rests on in the representation: node ids are handed out in
order and never reused, and a box is never edited or removed, so a
`NodeId` names the same computation for the life of its graph and a
recorded step means on replay what it meant when it landed. How the
prover keeps a record replayable — what it holds across steps, how it
speculates, how it names a box — is a set of choices about the record's
format, listed below.

## A close is re-checked, fail closed

A `Proof` carries its full record — every step each drive landed, the
inline's target, the cut's waypoint — and `Prover::prove` re-checks the
whole tree against the goal *as stated* before answering. Where a node
records nothing, it is because the move is a function of the goal and the
checker re-performs it: `inline` re-opens, and a `select-same` split
re-carves the two blocks off the left side's own `select`, refusing a
proof whose left side does not answer with one. The checking is the same
either way: every step
replayed through the table, every isomorphism asked again. A proof that
does not re-check comes back stuck, named as the prover bug it is. A
citation (`by name`) stands **given the corpus**: the citation order is a
DAG or the corpus refuses to run, an unproved claim is never citable, and
`prove --expand` cashes every citation into the cited proof's own steps —
the check that the shorthand was honest.

## Choices that hold today

Everything below is how the prover stands, with the reason it stands
that way. None of it is load-bearing for the list above: each was the
simplest thing that worked, and reworking one is a design decision to
take on its merits rather than a broken commitment.

### The driver decides nothing about what is provable

No driver opens a call or invents a case analysis today: `inline` and
`cases` are a proof's decisions, stated in the `.hant`. Rows that grow a
graph — the two hoists, the two unpackings — are on no driven list; a
strategy names them, and a driver run to fixpoint spends only rows that
shrink, which is what makes the fixpoint cheap to reach. A case split is
three of them in a row (`rules::case_split`), which is why it is a
strategy's act and not a law of its own. A driver that did open calls or
lay out cases would still land nothing but checked steps, so the trust
boundary is indifferent; what would change is what a close costs and how
much of a proof gets written down.

### Hypotheses are structure

The checker has no turnstile today. "Assume the condition holds" is the
branch itself: a case split introduces it, the specializing rows spend it
(anchored on the select, which holds both the condition and the discard
that licenses reasoning from it), `select-same` discharges it — as a row
the branch layer drives, and as the proof step of that name, which
spends a branch the goal already holds by asking each block to answer
for itself — and `Proof::check` replays the chain with no idea a case
analysis happened. Only guard-shaped hypotheses compile away this way —
"this wire's answer is `true`" for a wire the instruction set promises is
a bool — and that boundary is a theorem (hypothesis elimination, in the
Kleene-algebra-with-tests literature): an arbitrary semantic fact with no
wire to branch on cannot be spent by a split. A checker that wants such a
fact needs a second mechanism — a hypothesis context the checker
carries, or a custom equation admitted with a warrant, the
`Rule::Lemma { lhs, rhs, warrant }` seam whose stored derivation checks.
Neither exists yet and nothing admits an equation pair today; which
comes first is open, with the re-check property above the thing to keep
whichever way it goes.

### One place pays the arity asymmetry

An identity equates **net** stack change, not arity. `Goal::aligned` pads
the narrower side once, when the goal is built, and every downstream
question is arity-exact; nothing else pads, and a `.hant` waypoint whose
halves do not meet is an error where it is written. Paying once at the
top is what lets every law be stated arity-exact, which is a convenience
rather than a necessity.

### Proofs attach both ways

A `.hant` entry naming no stated identity is reported as a problem —
a renamed identity would otherwise silently shed its proof — and so is a
claim discharged twice. A step that finds nothing to do fails rather
than becoming a no-op, so a proof that no longer matches its identity
says so. All three are strictness settings: they make drift loud, and
any of them could be relaxed to a warning if the noise ever outweighs
the catch.

### The record is id-based, and the rest follows

A recorded match names boxes by `NodeId`. Everything below is how the
prover keeps such a record replayable, and each would change with the
record's format — one that recorded addresses or step recipes instead of
ids could backtrack, cache, and speculate in place:

- A box's **address** — the digest of what it computes, in letters,
  which is what a report prints and a proof writes — is content and not
  history, so it is the same in every graph that computes the box, the
  goal's other side and the checker's replay included. A `.hant` proof
  leans on this directly, which is what makes it more than a formatting
  choice.
- `undo` is a valley-closer today rather than a backtracking stack:
  undoing mints new ids, and a history that went forward, undid, and
  went forward again would record matches against ids replay never
  produces.
- Speculation (a tactic's `try`, a failed alternative) runs on clones and
  leaves no trace; the surviving suffix replays onto the real graph.
  This is the backtracking the id-based record allows.
- Bindings and matches are not carried across a rewrite; persistence is
  running the query again, which is cheap because search is untrusted.
  Where a step does carry something — today only `at(#box, law)` — it
  carries a **name** and not an id: as much of a box's address as tells
  it apart, looked up against the live graph at every entry and failing
  by name when nothing answers to it or two boxes do. Nothing says `at`
  has to stay the only step that does.

### Search proposes no reader selection

`sel: None` is all that `find` and `propose` yield: a substitution
re-points every reader, and a found match has no split of a port's
readers to decide. A selection is a proof's stated choice today because
no search has needed to make one; a search that did would carry it as
the same payload, checked the same pointwise way.
