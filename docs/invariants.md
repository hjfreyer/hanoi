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
`vm` — `truthy`, `op_arity`, `yields_bool` — never restated in the
rewriter. `fold` executes its window on a scratch VM rather than
reimplementing any operation. A law that turns on what the machine
computes is tested against `vm`; only pure wiring laws may be judged by
the opaque-operation oracle (`rules::is_wiring` is the split).

## Side conditions are carried by interfaces, never tested

A rule's pattern boundary *is* its side condition. `dead-node`'s left
side exports nothing, so the fullness check forces every port of the
matched box to be reader-less; `not-not`'s middle port is not exported,
so it cannot fire where something else reads the first `not`;
`select-hoist`'s left side exports its body's outputs and never the
select's answers, forcing every answer to be consumed inside the window.
Nothing asks "is this dead" — a match that is not one fails to be a
match. New rules follow the same discipline.

## Totality, purity and determinism are load-bearing

- Discarding work (`dead-node`, and every branch's untaken arm) is
  licensed by **totality and purity**: discarded work cannot fail and
  cannot be observed.
- Sharing work (`dedup`, interning one computation for many readers) is
  licensed by **determinism and purity**: running twice is running once.

If a partial instruction ever arrives, discard stops being sound and
sequencing needs an explicit order; if an effectful or nondeterministic
one arrives, sharing goes. The laws would survive only for the pure
fragment. No instruction may be added without revisiting the table
against this list.

## Derivations are forward-only and replayable

Node ids are handed out in order and never reused; boxes are deleted,
never moved, so a `NodeId` is stable for the life of a graph. A
derivation replays from its original graph and lands identically —
that is the property it exists to have — so:

- `undo` is a valley-closer, never a backtracking stack: undoing mints
  new ids, and a history that went forward, undid, and went forward again
  would record matches against ids replay can never produce.
- Speculation (a tactic's `try`, a failed alternative) runs on clones and
  leaves no trace; the surviving suffix replays onto the real graph.
- Bindings and matches never cross a rewrite. Persistence is running the
  query again; the one exception, `at(#box, law)`, is checked live at
  every entry and fails by name when its box is gone.

## A close is re-checked, fail closed

A `Proof` carries its full record — every step each drive landed, the
inline's target, the cut's waypoint — and `Prover::prove` re-checks the
whole tree against the goal *as stated* before answering: every step
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
`select-same` discharges it, and `Proof::check` replays the chain with no idea a case
analysis happened. Only guard-shaped hypotheses compile away this way —
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
