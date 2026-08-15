# Proving identities

`bin/prove` discharges the claims `identity A = B;` states. It replaces the
tactic-and-matcher rewriter that was deleted in the reboot, and it is built
the other way up: instead of a script steering a term toward a goal, both
sides of the goal go into one **e-graph** and every equation fires until the
two sides land in the same class — or the budget runs out and the smallest
thing each side reached is printed instead.

```bash
cargo run --bin prove -- tests
cargo run --bin prove -- tests --filter two_spellings --explain
```

```
Proving 14 identities...
identity identities::testing_a_test ... ok (saturated (8 iters, 5 classes))
identity identities::a_test_inside_an_arm ... ok (descend (then: saturated (13 iters, 56 classes); else: as written))
identity identities::testing_a_test_by_name ... ok (inline; saturated (8 iters, 5 classes))
...
identity result: ok. 13 passed; 0 failed; 0 orphaned hints; 0 filtered out
```

Exit codes keep the old contract: `0` every identity proved, `1` a claim
unproved or a hint orphaned, `2` the corpus would not build or the arguments
were wrong.

## The shape of the thing

Three layers, in `rewrite/src/`:

| layer | module | what it does |
|---|---|---|
| goals | `goal.rs`, `strategy.rs` | a goal is two [terms](../rewrite/src/term.rs) padded to one arity; a small pipeline of moves narrows it before and after the engine runs |
| engine | `lang.rs` | the term model as an egg language, with a per-class analysis carrying the facts rules condition on |
| equations | `rules.rs` | every law, as a rewrite the e-graph applies in both directions where both are bounded |

### Goals, and where the net-change asymmetry lives

The compiler holds an identity to equal **net** change, not equal arity —
`pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`. In the term model that
asymmetry is resolved in exactly one place: `Goal::aligned` pads the narrower
side with `id(k) *` until the arities agree. Every rule instance after that is
arity-preserving as a term, which buys the engine its soundness net: **arity
is invariant across an e-class**, and the analysis asserts it on every merge.
A rule that united two classes with different stack effects would panic on the
spot rather than prove something false.

### The pipeline

A goal runs through five moves, each of which exists to keep the e-graph
small and the failure readable:

1. **Trivial** — the sides are one term as written.
2. **Peel** — strip what the two compose spines share at either end, prove
   what is left. Peeling is *incomplete* (`push 1 ; drop` = `push 2 ; drop`,
   and stripping the `drop` leaves a false claim), so a peeled goal that
   sticks falls back to the whole one.
3. **Descend** — two branches are equal exactly when their arms are equal
   pairwise, so each differing arm becomes its own goal. Unlike peeling this
   is complete: the stack under a condition is arbitrary, so there is no
   context an arm could have used.
4. **Saturate** — both sides into one e-graph, every rule fires. Closing
   means the two roots unify; the proof records iterations and class count,
   and `--explain` prints egg's step-by-step account of the meeting.
5. **Inline** — a stuck goal that still holds calls is reopened with every
   call unfolded and tried once more. Unfolding is a goal-level decision, not
   a rule: opened calls multiply the term, and only the goal level knows the
   cheap route already failed. This is "comparison up to inlining" reborn —
   `testing_a_test_by_name` is the identity that exercises it.

The old system's hardest cases are the e-graph's easiest. `two_spellings_of_
one_test` needed "driving both sides and meeting in the middle" — a whole
strategy layer — and is now just what saturation does. `the_guard_a_split_
leaves` needed copy-naturality *backwards*; an e-graph does not have a
backwards.

### The equations

The rule set is the algebra of [docs/algebra.md](algebra.md) made executable,
and the map between the two is written there. Three kinds of rule:

- **Pattern rules** state both sides syntactically — associativity, the
  branch laws, `swap` sliding past a drop.
- **Fact rules** match a small window and read the analysis of what they
  bound. The facts are: the class's arity; `is_id` / `is_drop` / `is_copy`
  (it contains that structural leaf); `yields_bool` (its top output is a
  `Bool` — `Instruction::yields_bool`, lifted through composition); and
  `literal` (it behaves as `id(n) *` a run of pushes). A width cannot appear
  in a pattern, so anything the algebra indexes by width reads it off a fact.
- **The evaluation rule** builds a scratch one-sentence library — the pushed
  operands and the instruction — and runs the real `vm` on it. Folding owes
  the interpreter exact agreement, junk included, and this way there is no
  second implementation to drift.

Two readings are deliberately absent. **Unfolding** is the pipeline's move,
per above. And nothing **conjures work** — `drop(n) = X ; drop(m)` read
backwards would have to invent `X`. When a proof needs that direction, the
term it needs is written down as a stepping stone instead.

One scheduling fact worth knowing, learned the expensive way: egg's backoff
scheduler bans rules by *match* count, and a fact rule matches everywhere
precisely because its pattern is small — it declines almost every match. Ban
one and you silence exactly the rare application it exists for. So only the
shape rules that actually grow the graph (associativity, the staircases, the
block expansions) are left bannable; every fact rule is exempted.

## Stepping stones: the `.hant` file

A goal the rules cannot bridge is helped by seeding the e-graph with an
intermediate term both sides can reach. The stone is a program, so it is
written as one, in a `.hant` beside the `.hana`:

```text
// identities.hant
hint identities::some_claim via { drop 0 push true };
```

An identity may have several stones; one with none runs the default pipeline;
an entry naming no stated identity is an error, since a renamed identity
would otherwise shed its hints silently. Bodies are compiled by appending
scratch sentences to the corpus source — the whole parser and resolver are
reused — with one caveat: paths in a body resolve from the crate root.

The current corpus needs no stones: all thirteen identities in
`tests/identities.hana` close on the rules alone. The mechanism exists for
the day one does not.

## The failure output is the point

```
identity types_test::number_does_pre_and_post_is_constant ... FAILED

  what the left came to   │ copy(1) ; (id(1) * (...) ; branch { ... } { drop(1) ; push true })
  what the right came to  │ drop(1) ; push true
  the search stopped      │ TimeLimit(10.0)
  rule firings
      1436  par-fuse
      1155  stair-deep-first
```

A stuck goal prints the smallest spelling saturation found for each side —
the **residual**, which is what says what to try next — plus why the search
stopped and which rules did the work. That output is the deliverable of a
failed run, and it is how every rule gap found so far was diagnosed.

## What is not here yet

- **A case split on a value.** The one stuck identity,
  `types_test::number_does_pre_and_post_is_constant`, is a path-condition
  claim: its then arm is reached only when `is_tag` held, and *that* fact is
  a disjunction (`v = t1` or `v = t2`) no single rule window can use. The
  move it needs is goal-level case analysis on the tested value — split the
  goal per case, specialize, prove each — which is the next strategy to
  build. `rewrite/tests/corpus.rs` names it as the expected straggler, so
  the day it closes is the day a test says so.
- **A replayable derivation.** A close currently answers with egg's
  explanation (`--explain`); nothing independent re-checks it yet. The next
  milestone translates explanations into the flat derivation format a small
  applier can replay, restoring the old system's "finding and checking are
  different jobs" property.
- **Block operators at width n.** `copy(2)` is bridged to the frame spelling
  `pick 1 ; pick 1` lowers to by an explicit rule; the general `copy(n)`
  bridge should be derived, not enumerated, when a corpus term wants one.
