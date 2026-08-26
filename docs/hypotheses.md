# Hypotheses, compiled away

*A design note, since landed: the structured `cases` of
[docs/proving.md](proving.md) implements the authoring layer this note
designs, `Region::Arm` in `rewrite/src/diagram2/tactic.rs` is the seam
it took, and the corpus's biggest goal — the barista contract claim —
closes as its worked example. The argument of the note stands as the
argument of the implementation: the construct costs the checker
nothing, and `Proof::check` never learned what a hypothesis is.*

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
entry; it is the branch itself. A `select` holds its condition at port 0
so a rule anchored there can *name* it, and it holds the **discard** —
the untaken block is an answer nobody reads — which is what makes
reasoning from "the condition held" sound. So "the condition is known
true in this arm" is spent by a rewrite whose window is that one box and
whatever made the condition. That is the whole of the specializing layer
(`specialize-equal`, `specialize-bool`, `specialize-choice` in
`rewrite/src/diagram2/rules.rs`), and
`rewrite/tests/path_condition.rs` walks the methodology end to end:
widen, identify, promise, specialize.

So the primitive moves of hypothetical reasoning are already rows:

| sequent-calculus move | row of the table |
|---|---|
| case split on a boolean wire | `shannon` — η as an equation, fired by the `cases` proof step |
| use `x = true` in the then case | `specialize-bool` / `specialize-equal` / `specialize-choice`, anchored on the select |
| rewrite inside one case | free — a `Match` is an embedding, so every law fires in any context |
| discharge, both cases proved | `select-same` (`if c { t } else { t } = t`), with `copy-elim`/`dedup` identifying the blocks first |
| bring a fact into an arm's scope | backward `dead-node` (widen), then `copy-elim`/`dedup` |

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
                                     anchored on this branch's select
   =  if x { A′ } else { A″ }        the else-case's sub-proof, likewise
   =  B                              both arms landed on B: select-same
```

Every line is ordinary rewriting. The sub-proofs replay *verbatim*
because congruence is free — their steps fire inside the arm the way
every law fires anywhere — and the only steps that are not verbatim are
the hypothesis uses, each of which compiles to one specializing row.
The hypothesis exists in the derivation only as the branch it anchored
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

## What authorship looks like

The compilation above fixes the design: hypotheses live in `hant.rs`
and the report printer, and nowhere below. (This section was written
before the implementation and reads as its specification; what landed
follows it, with two findings noted at the end.)

**A structured `cases`.** The bare `cases(op)` fires the Shannon row
once per side and hands the expanded goal to whatever follows — the two
assumptions are simplified *together* by the next drive. The structured
form carries a sub-strategy per case, in the parenthesized-arm spelling
`via` already uses (an arm holds side rewrites and nested `cases`; the
goal is closed outside the split):

```text
cases(equal) (
    true:  both(decide),
    false: both(decide) cases(is_symbol) (true: both(decide)),
)
```

Elaboration: fire `shannon` exactly as today, then run each
sub-strategy **scoped to its arm**, then let the closer collapse the
branch. One new `hant::Step` shape, no new proof-object shape:
`Proof::Cases` already records a flat list of primitive steps per side,
and `Proof::check` already replays them blind.

**`Region::Arm`.** The scoping is the region
[docs/tactics.md](tactics.md) names as the natural next variant and
holds until a tactic needs one — one side of a branch's boxes, computed
from its select. A sub-strategy is
a tactic, not a step list, so it re-queries inside the region rather
than carrying matches across rewrites; the addressing discipline —
bindings never cross a rewrite, persistence is running the query again
— is already doctrine, and `Within` already re-scopes at every
evaluation.

**`use_guard`, a library tactic.** The compiled form of "apply the
hypothesis": find the governing select of the current region, and fire
whichever specializing row matches — `specialize-bool` through the
promise, `specialize-equal` through an `equal`, `specialize-choice`
for an inner branch on the same condition — with `promised-bool` spent
first when the witness is missing. A sibling of `decide` and
`branch_pass` in `tactic.rs`: data a proof can cite, not an ordering an
engine hardcodes.

**The turnstile is a printout.** A stuck sub-strategy's residual should
print as the author thinks of it — `equal(x, t1) = true ⊢ …` above the
goal-as-it-stands — and the prefix is *read off the graph*: the region's
governing select names the condition, the arm names the polarity. The
graph does not record the presentation; the presentation reads the
graph, the same way `--terms` reads back a residual today.

**Trust, restated.** `rules.rs` and `goal.rs` do not change. Every step
a sub-strategy lands goes through `Derivation::push` and is refused or
recorded like any other; the proof object stays a tree of flat step
lists; re-checking stays a blind replay plus isomorphism. A buggy
elaboration produces a refused step or a stuck goal, never a wrong
close — the same property the tactics layer was designed to and the
reason the construct is free.

**Two findings from the implementation.** First, the arm region wants
to be the arm's *cone*, shared context included, not the arm's own
boxes alone: a split duplicates only what lies downstream of its wire,
so the tests a nested split must reach — the hypothesis's remaining
unknowns — sit upstream, shared between the copies, and a region that
evicted them would let an arm spend its hypothesis but never decompose
it. Second, a hypothesis is spent *forward only*: the split pastes its
literal into the readers its wire had at split time, so a reader
created afterwards — say, by `tuple-cancel` taking a shape guard apart
inside an arm — reads the wire undecided, and the move that decides it
is to **split again inside the arm**, where the new readers are
downstream and the drive dedups the re-test into the old wire. The
barista proof does both, and its two `is_symbol` splits sit inside the
`thirsty` arm for exactly this reason, deciding checks that only came
into existence there.

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
