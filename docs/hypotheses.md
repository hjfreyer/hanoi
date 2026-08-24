# Hypotheses, compiled away

*A design note. Nothing here is implemented; what it designs is an
authoring construct, and the argument of the note is that the construct
costs the checker nothing. [docs/proving.md](proving.md) describes the
machinery this note leans on; [docs/tactics.md](tactics.md) names the
seams it would land in.*

A traditional proof assistant would take the goal

```text
if x { if x { true } else { false } } else { true }   =   true
```

and split it in two, each half carrying an **assumption**:

```text
x = true   ⊢   if x { true } else { false }  =  true
x = false  ⊢   true                          =  true
```

Hanoi has no spelling for the turnstile, and the checker is not getting
one. A close is a linear derivation — named laws, each application held
to its window by `rules::apply` — plus isomorphism at the leaves, and a
hypothesis object in that story would be a second notion of goal, a
context to thread, and a discharge rule to trust. The question this note
answers: can proof *authorship* look like the sequent above anyway —
subgoals, assumptions, one sub-proof per case — while what compiles out
the other end is the linear derivation the checker already replays?

Yes. The construct is standard, the compilation is standard, and the
table already holds every row the compilation spends. What follows is
the argument, the map to the literature it comes from, and the shape of
the authoring layer that would spend it.

## The position already taken: a hypothesis is structure

The engine's answer to "assume the condition holds" is not a context
entry; it is the branch itself. A fork holds its condition at port 0 so
a rule anchored there can *name* it, and "the condition is known true in
this arm" is spent by a rewrite whose window holds both facts it needs:
the fork, which says *this* is the condition, and the select, which
holds the discard that makes reasoning from "the condition held" sound —
the untaken arm is an answer nobody reads. That is the whole of the
specializing layer (`specialize-equal`, `specialize-bool`,
`specialize-choice` in `rewrite/src/diagram2/rules.rs`), and
`rewrite/tests/path_condition.rs` walks the methodology end to end:
widen, hoist, dedup, promise, specialize.

So the primitive moves of hypothetical reasoning are already rows:

| sequent-calculus move | row of the table |
|---|---|
| case split on a boolean wire | `shannon` — η as an equation, fired by the `cases` proof step |
| use `x = true` in the then case | `specialize-bool` / `specialize-equal` / `specialize-choice`, anchored on the fork |
| rewrite inside one case | free — a `Match` is an embedding, so every law fires in any context |
| discharge, both cases proved | `select-same` (`if c { t } else { t } = t`), with `select-view`/`dedup` identifying the blocks first |
| bring a fact into an arm's scope | backward `dead-node` (widen), then `fork-hoist` |

The worked goal above closes without any of this note's machinery — one
drive identifies the two tests as one wire and `specialize-choice`
decides the inner branch — which is the point: the *checker-level* story
is finished. What is missing is only the authoring surface, and the rest
of this note is about that.

## The deduction theorem this language earns

Why should hypothesis-style authorship compile away at all? Equational
logic in general does not allow it: there is no deduction theorem taking
`x = true ⊢ A = B` to an unconditional equation, and a proof calculus
that adds hypothetical judgments genuinely grows. The exception is
exactly a language that can **branch on the hypothesis** — and then the
discharge is a derivation schema, not a new rule:

```text
A  =  if x { A } else { A }          select-same, backward — or shannon,
                                     when the split introduces the branch
   =  if x { A′ } else { A }         the then-case's sub-proof, replayed
                                     inside the arm; each USE of the
                                     hypothesis is a specialize row
                                     anchored on this branch's fork
   =  if x { A′ } else { A″ }        the else-case's sub-proof, likewise
   =  B                              both arms landed on B: select-same
```

Every line is ordinary rewriting. The sub-proofs replay *verbatim*
because congruence is free — their steps fire inside the arm the way
every law fires anywhere — and the only steps that are not verbatim are
the hypothesis uses, each of which compiles to one specializing row.
The hypothesis exists in the derivation only as the fork it anchored
on, and the checker replays the chain with no idea a case analysis
happened. This is McCarthy's conditional-expression calculus doing what
it was built for: if-then-else is precisely the operator that makes
assumption-discharge equationally derivable (McCarthy 1963;
Bloom–Tindell 1983 axiomatize the theory).

The same fact, said in Kleene algebra with tests: a guarded equation
`b → (p = q)` holds iff the plain equation `bp = bq` does — the
hypothesis multiplies into the term as its guard, and reasoning under
it becomes reasoning about the guarded fragment. The KAT literature
calls compiling assumptions away **hypothesis elimination**, and its
results draw the exact boundary this design inherits: hypotheses about
*tests* eliminate; arbitrary hypotheses in general do not, and can cost
decidability (Cohen 1994; Kozen–Smith 1996; Doumane–Kuperberg–Pous–
Pradic 2019 and Pous–Rot–Wagemaker 2024 map which hypothesis shapes
reduce away and which change the theory).

And the architecture — an authoring layer that *presents* hypothetical
judgments while emitting only kernel steps — is the oldest trick in the
book: LCF's derived rules. A tactic that shows the author two subgoals
under assumptions, and whose implementation fires `shannon`, replays
two tactic scripts, and fires `select-same`, is a derived rule in
exactly Milner's sense: the kernel's rule set never grows, so there is
nothing new to trust. The nearest living relatives are the simplifiers:
ACL2's rewriter and Isabelle's simplifier both *present* "rewriting the
then-branch under hypothesis `b`" — contextual rewriting, with a
congruence rule for `if` collecting the guard — while the justification
of each hypothesis use is local to the conditional it came from, which
is the specializing rules' soundness argument told in sequent clothing.

## The boundary, honestly

Only **guard-shaped hypotheses** compile away: facts of the form "this
wire's answer is `true`" (or `false`), where the wire is one the
instruction set promises is a bool — the witness `promised-bool` writes
down, and the shape the `cases` parser already refuses everything but.
That covers more than it first appears to. A hypothesis about a test
the goal never computes can be *paid for*: compute the test and discard
it (backward `dead-node` — computing and discarding is ε, totality and
purity footing the bill), then split on it. That is the
`path_condition.rs` widening, played as introduction.

What stays out of reach is a hypothesis no test in the language
expresses — an arbitrary semantic fact with no wire to branch on. The
KAT results say that is not an implementation gap but the actual edge
of the technique, and the honest instrument for it is different: a
custom equation admitted with a warrant, which is the
`Rule::Lemma { lhs, rhs, warrant }` seam [docs/tactics.md](tactics.md)
already reserves and deliberately leaves out of its first version.

## What authorship would look like

The compilation above fixes the design: hypotheses live in `hant.rs`
and the report printer, and nowhere below.

**A structured `cases`.** Today `cases(op)` fires the Shannon row once
per side and hands the expanded goal to whatever follows — the two
assumptions are simplified *together* by the next drive. The structured
form carries a sub-strategy per case:

```text
cases(equal) {
    true:  both(decide),
    false: fire(select-same) diagram,
}
```

Elaboration: fire `shannon` exactly as today, then run each
sub-strategy **scoped to its arm**, then let the closer collapse the
branch. One new `hant::Step` shape, no new proof-object shape:
`Proof::Cases` already records a flat list of primitive steps per side,
and `Proof::check` already replays them blind.

**`Region::Arm`.** The scoping is the region
[docs/tactics.md](tactics.md) names as the natural next variant and
holds until a tactic needs one — the boxes between a paired fork and
select, computed the way `rules::arm` computes them. A sub-strategy is
a tactic, not a step list, so it re-queries inside the region rather
than carrying matches across rewrites; the addressing discipline —
bindings never cross a rewrite, persistence is running the query again
— is already doctrine, and `Within` already re-scopes at every
evaluation.

**`use_guard`, a library tactic.** The compiled form of "apply the
hypothesis": find the governing fork of the current region, and fire
whichever specializing row matches — `specialize-bool` through the
promise, `specialize-equal` through an `equal`, `specialize-choice`
for an inner branch on the same condition — with `promised-bool` spent
first when the witness is missing. A sibling of `decide` and
`branch_pass` in `tactic.rs`: data a proof can cite, not an ordering an
engine hardcodes.

**The turnstile is a printout.** A stuck sub-strategy's residual should
print as the author thinks of it — `equal(x, t1) = true ⊢ …` above the
goal-as-it-stands — and the prefix is *read off the graph*: the region's
governing fork names the condition, the arm names the polarity. The
graph does not record the presentation; the presentation reads the
graph, the same way `--terms` reads back a residual today.

**Trust, restated.** `rules.rs` and `goal.rs` do not change. Every step
a sub-strategy lands goes through `Derivation::push` and is refused or
recorded like any other; the proof object stays a tree of flat step
lists; re-checking stays a blind replay plus isomorphism. A buggy
elaboration produces a refused step or a stuck goal, never a wrong
close — the same property the tactics layer was designed to and the
reason the construct is free.

## References

- Milner (with Gordon and Wadsworth), *Edinburgh LCF* (1979) — derived
  rules: hypothesis-shaped authorship over an unchanged kernel; the
  architecture this note instantiates.
- McCarthy, *A basis for a mathematical theory of computation* (1963) —
  the conditional-expression calculus; case analysis and discharge as
  equational derivation.
- Bloom–Tindell, *Varieties of "if-then-else"* (1983) — the equational
  theory of the conditional, axiomatized; what the discharge schema
  leans on.
- Cohen, *Hypotheses in Kleene algebra* (1994); Kozen–Smith, *Kleene
  algebra with tests: completeness and decidability* (1996);
  Doumane–Kuperberg–Pous–Pradic, *Kleene algebra with hypotheses*
  (2019); Pous–Rot–Wagemaker, *On tools for completeness of Kleene
  algebra with hypotheses* (2024) — `b → (p = q)` iff `bp = bq`;
  hypothesis elimination, and the boundary: test-shaped hypotheses
  compile away, arbitrary ones need not.
- Boyer–Moore, *A Computational Logic* (1979); Zhang, *Contextual
  rewriting in automated reasoning* (1995) — rewriting under collected
  assumptions, justified locally by the governing conditional; the
  simplifier tradition (Isabelle's congruence rules for `if`) is the
  living form.
- Nieuwenhuis–Oliveras, *Proof-producing congruence closure* (2005);
  Flatt–Coward–Willsey–Tatlock–Panchekha, *Small proofs from congruence
  closure* (2022) — free-form search emitting linear replayable
  proofs; Singher–Itzhaky, *Colored e-graphs* (2023) — assumptions kept
  in the untrusted search layer only. The same division of labour, in
  the e-graph world this prover retired from.
