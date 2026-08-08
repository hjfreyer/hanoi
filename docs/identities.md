# Identities

`bin/rewrite` can show that two programs are interchangeable. Until an identity
existed that was all it could do: the showing was printed and lost, nothing
re-checked it when the library changed underneath, and nothing could cite it
later.

An **identity** is the claim, written in the `.hana`. Its **proof** is a tactic,
written in the `.hant` beside it. `bin/prove` holds the two together.

```bash
cargo run --bin prove -- tests
```

```
Proving 9 identities...
identity identities::testing_a_test ... ok (2 steps)
identity identities::a_value_tested_twice ... ok (6 steps)
identity identities::copying_a_constant ... ok (3 steps)
identity identities::discarded_work_on_copies ... ok (3 steps)
identity identities::testing_a_test_by_name ... ok (2 steps + 1 up to inlining)
identity identities::two_spellings_of_one_test ... ok (4 steps meeting in the middle)
identity identities::a_test_inside_an_arm ... ok (4 steps in 2 parts)
identity probes::pair_check ... ok (0 steps)
identity probes::state_check ... ok (0 steps)

identity result: ok. 9 passed; 0 failed; 0 filtered out
```

## Stating one

```hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

Two inline bodies, and **only** two inline bodies. Naming two sentences that
already exist is `{ jump a } = { jump b }`, so one form covers both cases; a
second spelling would buy nothing and cost the consistency between them. A body
is whatever a sentence body is, so `branch { } { }` and `dip 1 { ... }` work
inside one for free.

`#[arity(n, m)]` and `#[total]` are the annotations an identity may carry, each
a claim both sides answer for independently. The rest name properties of a
sentence *being called*, which an identity is not, so they are refused rather
than ignored — an annotation nothing reads is a lie. `export` and `test` are
refused for the same reason: nothing calls an identity and nothing runs it.

### It is core, not sugar

`docs/compilation.md` asks: could a user have written this by hand in terms of
other surface constructs? A `sentence` names code and a `test sentence` runs it,
and neither states an equation. So `identity` lowers to itself, and the
sugar/core seam grows by one variant on each side rather than by a lowering.

### The two sides are sentences

Each side is compiled into the library as an ordinary sentence, named
`<identity>::lhs` and `<identity>::rhs`. Nothing resolves to those names —
`jump foo::lhs` is refused, because an identity is declared into the module
namespace as an identity, not as a sentence — but they are real sentences, and
two things rest on that. `--step` walks a derivation by rebuilding the left-hand
side and applying a prefix, which needs a `SentenceIndex` and has one; and the
applier can regenerate either side from the library rather than being handed a
copy.

## Writing one

`rewrite` addresses the identity, so the goal is one command away:

```bash
$ rewrite tests copying_a_constant
$ rewrite tests copying_a_constant -t 'must(once(inv(share { push 9 })))'
$ rewrite tests copying_a_constant -t '<the whole proof>' --show-script
```

Bare, it prints the two sides against each other. With `-t`, it runs a strategy
and prints either `closed` or **the residual** — the smallest part of the claim
still standing, which is what says what to try next. A goal left open is the
answer rather than an error; `prove` is the tool whose job is to say no.

**`-t` is a proof body, resolved exactly as a `proof` is.** A bare tactic is the
blind reading and `normalize(cleanup)` is a strategy, so what closes on the
command line is what goes in the `.hant`, character for character. That is the
loop a proof gets written in, and nothing has to be translated on the way into
the file.

Their being sentences is also the decision the next feature rests on. When a
derivation may cite an identity, the applier will regenerate both sides from
the library on every application — exactly as it already regenerates an unfolded body — so no copy of
a program ever travels inside a script, and a script written against a library
that has since changed fails at the step that stopped fitting rather than
rewriting by a stale claim.

### What the compiler checks

One thing, and it is the one property of an identity that is about the
*statement* rather than about a proof: **the two sides must leave the stack the
same**.

Net change, not full arity. `pick 1 ; drop` = nothing is `(2 -> 2)` against
`(0 -> 0)` — both leave the stack as they found it, but the left needs a value
to look at where the right does not. Every counit reads this way, and so does
every annihilation, which lowers the input requirement on purpose. `--check` in
the rewriter allows the same asymmetry for the same reason; refusing it here
would refuse exactly the equations the rewriter is built out of.

Deliberately *not* checked by the compiler: non-recursive, and unable to fail.
Those are the preconditions the rewriter's equations are stated under —
conditions on provability rather than on well-formedness — and asking for them
in `assemble_source` would tie the language to a particular rule set. `prove`
asks, in the words `rewrite` uses.

## Proving one

```
// tests/identities.hant
proof testing_a_test = cleanup;

proof copying_a_constant =
    must(once(inv(share { push 9 })));
    must(at(0, sink));
    must(at(0, flatten));
```

A `.hant` is the tactic language of `docs/tactics.md` with two definition forms
added:

```text
def := "tactic"   ident "=" expr ";"
     | "strategy" ident "=" expr ";"
     | "proof"    path  "=" expr ";"
```

so a file may define its own tactics and then prove with them. A proof body is a
**strategy**, and a bare tactic is the strategy that runs it blind — see
"Strategies: proving a goal".

### Why the proof is not in the `.hana`

A proof is not part of the program. It depends on the rewriter's rule set,
which is not part of the language, and it changes when that rule set does while
the claim it establishes does not. Keeping it out means an identity reads as a
statement rather than as a script.

### One-sided, up to inlining

The tactic rewrites the **left-hand side**; the result must be the right-hand
side. Every step is an equation, so what a run leaves behind is a derivation
LHS ⇒ RHS: one linear script, which is a thing that can be replayed, printed,
stepped through and diffed.

Requiring the tactic to land on the right-hand side *as written* was too much.
It meant the right-hand side had to be written in whatever form the tactic
happened to reach — `{ jump foo }` on the right only worked when the proof left
the left as an unopened call. So the comparison is **up to inlining**: if the
two do not match as written, both are unfolded and compared again.

That is sound because unfolding is an equation like any other — the axiom the
library contributes by defining a sentence — so two terms with the same fully
inlined form are equal.

**And it makes the derivation longer rather than the check weaker.** The
fold-back is generated by running the *forward* unfold on the right-hand side
and inverting the resulting script, so the derivation runs
`LHS ⇒ … ⇒ (inlined) ⇐ … ⇐ RHS` and **ends at the right-hand side**. Replaying
it lands there, which the old shape could not say: its script stopped at what
the tactic reached, and the last hop was an equality test rather than a splice
the applier had to accept.

```
$ prove tests --filter by_name --show-script
identity identities::testing_a_test_by_name ... ok (2 steps + 1 up to inlining)

  the proof — 2 step(s)
     0  bool_result -> @0      is_bool ; is_bool ⇒ is_bool ; drop ; push true
     1  annihilate -> @0       is_bool ; drop    ⇒ drop

  inlining what it reached — 0 step(s)

  folding the right-hand side back up — 1 step(s)
     0  unfold <- @0           drop ; push true  ⇒ jump → #38
```

A proof that lands exactly still takes the short route: one derivation, no
inlining segment. The machinery only runs when it is needed.

**What inlining does not reconcile is a *frame*-shape mismatch.** A proof that
says `dips` leaves frames collapsed and sunk, and a naturally-written right-hand
side will not match that however much either side is unfolded. Nor does it help
when neither side is the normal form: rewriting the left reaches it and the
right is still sitting where it was written. That is what strategies are for.

## Strategies: proving a goal

`docs/tactics.md` describes two layers — equations and an applier below,
matchers and combinators above. A proof adds a third.

A **rule** rewrites a window. A **tactic** places rules in a term. A
**strategy** discharges a *goal*: two terms, and the claim that they are equal.
The layering is strict, and it is one-way — a strategy calls tactics, and
nothing below it knows a goal exists.

A strategy is a sequence of **moves**. Each rewrites one side of the goal and
leaves a goal behind, so they compose the way tactics do — and the sequence
closes when the two sides agree by effect.

| move | which side it drives |
|---|---|
| `<tactic>`, `exact(t)` | the left |
| `rhs(t)` | the right |
| `normalize(t)` | both, with the same tactic |

```
proof foo = cleanup ; rhs(unfold_all);
```

That is the shape most claims want: the two sides rarely need the same work. A
right-hand side written the way a person would write it often needs one step to
meet a left-hand side that needed ten, and saying so beats driving both with a
tactic that suits neither.

The rest take the remaining proof as an argument rather than leaving a goal, so
they are not moves and cannot be sequenced — `peel(a ; rhs(b))`, not
`peel(a) ; rhs(b)`:

| strategy | what it does |
|---|---|
| `<tactic>` alone | run it on the left and compare, exactly or after unfolding both sides |
| `peel(s)` | strip the common prefix and suffix, then `s` on what is left |
| `descend(body: s)` | congruence into a frame |
| `descend(then: s, else: s)` | congruence into the arms of a branch |
| `inline(s)` | unfold every call on both sides, then `s` |
| `s1 \| s2` | try, and fall back |

**A bare tactic keeps its meaning.** A proof that names no strategy at all is
the last table's first row — one-sided, compared up to inlining, which is what
`prove` has always done — so every `.hant` written before strategies existed
says and does exactly what it did. Name one anywhere in the expression and the
whole thing reads as a sequence of moves, whose close is exact. The two readings
agree on everything but that fallback, and `cleanup ; rhs(unfold_all)` is how you
ask for it out loud.

Congruence is not a new equation. A `Location` *is* a context and
`Location::under` *is* the rule `A = B ⟹ C[A] = C[B]`; what was missing was
something to read it backwards. So a sub-proof found inside a branch arm comes
back out addressed to the whole term, the script stays a flat `Vec<Step>`, and a
decomposed proof emits and replays like any other:

```
$ prove tests --filter a_test_inside_an_arm --show-script
identity identities::a_test_inside_an_arm ... ok (4 steps in 2 parts)

  derivation — 4 step(s)
     0  bool_result -> [0.then] @0
        is_bool ; is_bool
     ⇒  is_bool ; drop ; push true
     ...
```

`descend` given one arm and not the other is a claim that the other needs no
proof, and the claim is checked rather than assumed.

### Why there is no `auto`

There is deliberately no default ladder — nothing that decomposes on its own
initiative when a tactic falls short.

Decomposition can take a garden path. Peeling is **incomplete**: `push 1 ; drop`
and `push 2 ; drop` are equal, and stripping the shared `drop` leaves the false
`push 1 ⇒ push 2` behind. Descending commits just as hard. A prover that reached
for those whenever the plain tactic came up short would sometimes turn a
provable goal into an unprovable one and then report a residual that is not the
author's mistake — with no way to say "not there" except by learning which rung
fired and writing around it.

So which route a proof takes is written in the proof, reviewed with it, and
diffable when it changes. `strategy NAME = ...;` names one, which is where a
shape that keeps coming up belongs: in the corpus, readable and changeable,
rather than built in. Strategies do not recurse, for the reason tactics do not —
nothing here measures a goal getting smaller — so the depth is written out.
`peel` and `descend` **fail when they decompose nothing**, so a strategy that no
longer matches the term says so instead of quietly becoming a no-op.

None of this is trusted. A strategy picks which sub-goals to attack; it does not
get to decide what is true. Every step still comes from a matcher, the applier
still re-derives every side condition, and `prove` still replays the whole
assembled script onto the right-hand side before calling an identity proved.

#### Why `inv(unfold)` having no matcher costs nothing

`docs/tactics.md` calls folding a body back into a call "the real gap": nothing
can read a window and say which sentence to fold into. That is a limitation on
*searching*, not on the equation. Every recorded step is two-sided —
`applier::sides` swaps on `step.dir` for every step kind, `Unfold` included —
so a fold step is perfectly applicable once something has written it down. And
we never search for one: the fold script *is* the right-hand side's own unfold
script, read backwards.

`rule::invert` is that reading, and it rests on three things worth knowing
about, all of them checked by
`tests::inverting_a_corpus_derivation_returns_it_to_where_it_started` over the
real corpus rather than argued:

- every step is two-sided, per above;
- a side condition does not depend on direction — `Rule::check` takes no
  `Direction`, so a step validated forward is validated backward;
- a location addresses the same window before and after its own splice, since
  `at` is the window's start either way and the descent names indices in
  enclosing sequences that the splice cannot renumber.

### Where a proof lives

One `.hant` beside each `.hana`, checked as a bijection in both directions.

| the `.hana` | the sibling `.hant` |
|---|---|
| states identities, no `.hant` | error, listing what it must prove |
| states identities, `.hant` present | must prove exactly those, no more and no fewer |
| states none, `.hant` present | error — a renamed `.hana` orphans its proofs, and nothing else would notice |
| states none, no `.hant` | fine, which is nearly every file |

The rule governs where a proof is *declared*, not what it may reference. That
distinction is deliberate: when a proof may cite an identity stated in another
file — which is the point of building up a library of them — nothing about this
changes.

### Tactic definitions are file-local

A `tactic` defined in one `.hant` is invisible to every other. A proof has to be
readable beside the identity it proves, and a name that could have come from any
of a dozen files is not. A corpus-wide prelude is `prove --tactics <file>`,
which is the same mechanism said out loud.

A **tactic** name shadows, because the prelude is meant to be overridable. A
**proof** does not: a claim discharged twice was discharged once too often, and
that is an error naming both.

### One thing a `.hant` can do that a `--tactics` file cannot

A term in a `.hant` may name a sentence — `share { jump helper }` works in a
proof, and in a tactic defined beside it. That is not a special case but a
consequence of *when* each is read: a `--tactics` file is loaded before a corpus
is chosen, and a `.hant` only ever after one.

## What `prove` checks

Per identity, in order:

1. **Both sides** are non-recursive and unable to fail. Both, not only the side
   that gets rewritten: the right-hand side is the term the claim is measured
   against, so it has to be one the equations can speak about too.
2. The proof compiles, against its own file's definitions.
3. The tactic runs on the left-hand side.
4. **A miss fails it.**
5. The proof's own steps **replay exactly**: applying them to a fresh build
   reproduces the run, `==`. This is what makes a derivation a derivation rather
   than a log written alongside one, and it is checked here, on the segment
   where `==` is available.
6. The result equals the right-hand side by `same_effect_seq` — as written, or
   after both sides are inlined.
7. The **whole** derivation replays onto the right-hand side. By effect rather
   than `==`, and it has to be: after the fold-back the origins on the right are
   inherited from the left's provenance, and provenance is not part of a term's
   identity.

### Two deliberate differences from `rewrite`

Both are the same difference: `rewrite` explores, and `prove` decides.

- **A miss fails a proof**, where in `rewrite` it is a diagnostic that still
  prints the tree. `at(9, sink)` is a claim that there is something at 9; when
  there is not, the proof is aimed at a tree it no longer describes, and that is
  wrong even where the goal happened to be reached anyway. `try(...)` is how a
  proof says a miss is acceptable.
- **`--check` is on by default**, and `--no-check` turns it off. In `rewrite` it
  is opt-in because the listing is the answer and the check only costs time.
  Here the answer is *yes* or *no*, and a wrong yes is worse than a slow run.

### The failure output is the point

```
identity a_value_tested_twice ... FAILED

  the proof ran, but did not reach the right-hand side.

  proof: all
   --> tests/identities.hant:2

    what it reached            ┃   the right-hand side
  ─────────────────────────────╂─────────────────────────────
    ⋮ 2 unchanged lines        ┃
    0 │      1 │ branch then { ┃   0 │      1 │ branch then {
    0 │      0 │   push 1      ┃   0 │      0 │   push 1
      │        │ } else {      ┃     │        │ } else {
  - 0 │      0 │   push 4      ┃ + 0 │      0 │   push 3
      │        │ }             ┃     │        │ }
```

Two things had to be split apart to get that down to the line that matters.
`render_body` carries a header — index, name, annotations — which differs
between two sentences and would open every diff with two lines that always
disagree; `render_nodes` is the listing without it. And a `<inline>` label says
which sentence phase 4 put a block in, which never matches across two sentences,
so a listing being compared suppresses provenance the way `same_effect` already
ignores it. A `Call`'s label stays either way: there the target *is* the term.

### Exit codes

`0` every identity proved. `1` a claim is unproved, unproven, orphaned or
missing. `2` the corpus would not build, or the arguments were wrong. Three
rather than two because in CI those want different reactions.

## The corpus states five

`tests/identities.hana` already checked the rewriter's axioms *by executing
both sides on sample values*. It now states some of them as identities too, so
the same file answers two different questions: does the law hold on these
values, and does the rewriter's own equation set reach it.

Three of the five are worth reading for what they demonstrate rather than for
what they claim.

**`copying_a_constant`** — `push c ; pick 0` = `push c ; push c`. The proof
never uses the `copy_const` matcher, which would answer in one step. It reads
naturality backwards to put the second `push` inside a frame and then takes the
frame away, which is the argument that `copy_const` is a lemma and not an axiom.

**`discarded_work_on_copies`** — compute on copies, discard the results, and the
originals were never touched. It is the law that looked essential and turned out
to be derivable: one annihilation and two counits. It is also the identity whose
two sides need different amounts of stack, which is why an identity is held to
its net change.

**`testing_a_test_by_name`** — the same law as `testing_a_test`, with the
right-hand side written as the call it is rather than pasted out. Nothing the
tactic does could land on that, so it is the identity that exercises the
comparison being up to inlining.

The other two had lived as Rust tests that ran a derivation by hand
(`applier::tests::copy_const_is_derivable_from_copy_nat`,
`vacuous_is_derivable_from_annihilate_and_counit`). Those stay — they check
something else, that the derivation is reversible step for step — but the claims
themselves are now in the language.

## What is not here yet

- **Identities as rewrite rules.** The point of writing claims down is to build
  on them: a proven identity should be citable in another proof, so a `.hant`
  can reach for a library of statements rather than for the axioms every time.
  The shape is a `StepKind::Identity { id }` beside `Unfold`, whose `sides()`
  regenerates both from the library; a matcher `identity(<path>)` whose width is
  the left-hand side's node count; and — unlike `unfold`, whose backward reading
  is the known gap because a window does not say which sentence to fold into —
  a free `inverse()`, since an identity's other side is written down.
- **Acyclicity.** With that in place a proof of A could cite B whose proof cites
  A. `prove` already collects every proof before checking any, which is where
  the topological order goes.
- **A trust boundary to write down.** Once `identity(...)` is a matcher,
  `rewrite -t 'each(identity(foo))'` will rewrite by a claim nobody has proved.
  Soundness comes from `prove`'s whole-corpus pass, not from the applier —
  which is an accepted asymmetry, `rewrite` being a debugging aid whose output
  does not even parse.
- **Node-level alignment.** `peel` strips what the two sides share at their
  ends, and stops there. When what is left is two multi-node sequences with no
  common ends, nothing pairs up the interior — a branch at position 3 of one and
  position 4 of the other are not the same node, and guessing is a search
  `peel` deliberately does not do. `diff::align` is not reusable, since it
  aligns rendered lines rather than nodes; a Myers-style diff over `same_effect`
  to find interior anchors is the obvious next strategy, and should wait until
  the corpus asks for one.

- **Combinators that consult the goal, and matchers that read a second window.**
  Deliberately after strategies, if ever. A strategy is an outer driver and
  nothing below it knows a goal exists, which is what keeps the position-blind
  invariant intact; pushing the goal downwards spends that. If the latter ever
  lands it should take **the goal window at the same position**, never the whole
  goal — that keeps `plan` a pure function of its windows.

- **A `find` binary** that writes a proof to a `.hand` file rather than a
  strategy to a `.hant`. The prover makes it a thin wrapper, but a found
  derivation checked into the repo churns whenever the rule set moves, where a
  `.hant` is small and stable. Worth having as an authoring aid, not as where
  proofs live.

## The derivation is a file too

A `.hant` saves the *tactic* that finds a proof. What the proof leaves behind is
a derivation, and that has a format of its own:

```bash
prove tests --emit derivations.hand    # what the search found
replay tests derivations.hand          # checked again, with the search gone
```

`./run_proofs.sh` does both, so every commit exercises the whole path. The
second run shares no code with the tactic engine — it parses the file and hands
each step to the applier — which is what makes a proof something other than a
tactic can produce. See [docs/derivations.md](derivations.md).
