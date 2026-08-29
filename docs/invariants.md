# Invariants of the prover

The commitments everything else is built on. The other pages say how to
use the prover ([docs/proving.md](proving.md)), what the laws mean
([docs/rules.md](rules.md)), and how to drive them
([docs/tactics.md](tactics.md)); this page is the short list of
properties that must survive any refactor, each with where it lives.

## The trust boundary

Trusted, and the whole of it:

- `rules::sides` — builds a law's two graphs from its payload;
- `rules::apply` — holds a claimed embedding to agreeing at every port
  before re-pointing anything (`check_match`, then `Pair::apply`);
- `graph::isomorphic` — answers `true` only after verifying its
  bijection link by link;
- the machine itself, where a law is *about* what an operation computes —
  `fold` and `shannon` consult `run_window`, the real `vm`.

Everything else — `find`, `propose`, drivers, tactics, queries, the
`cases` step's wire-picking, strategy interpretation — is untrusted
search. It mutates a graph through `Derivation::push` and nothing else,
so every step it produces goes through `apply`, and a buggy tactic yields
a refused step, never a wrong graph. `Graph`'s mutation surface stays
crate-private; the tactic layer needs none of it.

## No second semantics

Facts about instructions live **on the instruction** and are measured by
`vm` — `truthy`, `op_arity`, `yields_bool`, `commutative`, `idempotent` —
never restated in the rewriter. A row may read one to stand for a whole
family (`comm`, `idem`, `tested-bool`), which is the same discipline seen
from the other end: the table asks the instruction set which instructions
a law is about instead of naming them itself. `fold` executes its window on a scratch VM rather than
reimplementing any operation. A law that turns on what the machine
computes is tested against `vm`; only pure wiring laws may be judged by
the opaque-operation oracle (`rules::is_wiring` is the split).

## Side conditions are carried by interfaces, never tested

A rule's pattern boundary says what the rule is *about*, and a rule that
wants a shape says it in the pattern rather than testing for it —
`select-hoist` exports its body's outputs, `shannon` carries the region
it pins as payload, `select-literal` carries its arms. Nothing asks a
question a match could answer. New rules follow the same discipline.

What a boundary does **not** say is *and nothing else reads this*. A
rewrite replaces the value a window exports and rebuilds whatever read
it, so a reader the window never mentioned is not a loose end: `not-not`
fires on a first `not` somebody else reads, and that somebody goes on
reading the box it always read.

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

## Derivations are forward-only and replayable

Node ids are handed out in order and never reused, and a box is named by
what it computes and never edited, so a `NodeId` is stable for the life
of a graph and a box's **address** — the digest of what it computes, in
letters, which is what a report prints and a proof writes — is stable
across graphs. A
derivation replays from its original graph and lands identically —
that is the property it exists to have — so:

- `undo` is a valley-closer, never a backtracking stack: undoing mints
  new ids, and a history that went forward, undid, and went forward again
  would record matches against ids replay can never produce.
- Speculation (a tactic's `try`, a failed alternative) runs on clones and
  leaves no trace; the surviving suffix replays onto the real graph.
- Bindings and matches never cross a rewrite. Persistence is running the
  query again; the one exception, `at(#box, law)`, holds a **name** and
  not an id — as much of a box's address as tells it apart — looked up
  against the live graph at every entry and failing by name when nothing
  answers to it or two boxes do.

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

## The driver never decides what is provable

No driver opens a call or invents a case analysis: `inline` and `cases`
are a proof's decisions, stated in the `.hant`. Rows that grow a graph —
`shannon`, `select-hoist`, the two unpackings — are on no driven list;
a strategy names them, and a driver run to fixpoint spends only rows
that shrink.

## Hypotheses are structure, and only guard-shaped ones exist

The checker has no turnstile and is not getting one. "Assume the
condition holds" is the branch itself: `shannon` introduces it, the
specializing rows spend it (anchored on the select, which holds both the
condition and the discard that licenses reasoning from it),
`select-same` discharges it — as a row the branch layer drives, and as
the proof step of that name, which spends a branch the goal already holds
by asking each block to answer for itself — and `Proof::check` replays
the chain with no idea a case analysis happened. Only guard-shaped hypotheses compile away this way —
"this wire's answer is `true`" for a wire the instruction set promises is
a bool. That boundary is a theorem (hypothesis elimination, in the
Kleene-algebra-with-tests literature), not an implementation gap: an
arbitrary semantic fact with no wire to branch on cannot be spent by a
split. The honest seam for such a fact is a custom equation admitted with
a warrant — a `Rule::Lemma { lhs, rhs, warrant }` whose stored derivation
checks — and until that exists, nothing may admit an unvalidated equation
pair.

## One place pays the arity asymmetry

An identity equates **net** stack change, not arity. `Goal::aligned` pads
the narrower side once, when the goal is built; every downstream question
is arity-exact. Nothing else pads, anywhere — a `.hant` waypoint whose
halves do not meet is an error where it is written.

## Proofs attach both ways

A `.hant` entry naming no stated identity is an error — a renamed
identity must not silently shed its proof — and a claim discharged twice
was discharged once too often. A step that finds nothing to do fails
loudly rather than becoming a no-op, so a proof that no longer matches
its identity says so.
