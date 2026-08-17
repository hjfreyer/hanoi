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

Three moves, and the shortness is a finding, not an economy:

1. **Trivial** — the sides are one term as written.
2. **Saturate** — both sides into one e-graph, every rule fires. Closing
   means the two roots unify, and a hook checks for that **every iteration**
   — saturation would otherwise happily keep exploring an already-closed
   goal to the end of the budget, and did: `discarded_work_on_copies` grew
   to 23,000 classes finding a proof it had at 51. The proof records
   iterations and class count, and `--explain` prints egg's step-by-step
   account of the meeting. Explanation tracking taxes every union, so the
   e-graph only carries it when `--explain` asks.
3. **Inline** — a stuck goal that still holds calls is reopened with every
   call unfolded and tried once more. This is "comparison up to inlining"
   reborn — `testing_a_test_by_name` is the identity that exercises it.

#### Why peeling and descending are not search moves

Two decompositions that looked essential — strip the prefix and suffix the
two sides share, descend into the arms of a branch pair — are
**congruences**, and performing congruences is precisely what an e-graph
does on its own: the moment saturation unites `A` with `B`, the parents
`P ; A` and `P ; B` are one e-node and merge for free, and two branches
merge the moment their arms do. Running the moves *before* saturation could
only ever save graph size, and in practice it cost instead: a peeled
subgoal can be **false** (`push 1 ; drop` = `push 2 ; drop`, minus the
shared `drop`), and a false goal saturates to the end of its budget —
`two_spellings_of_one_test` once spent fourteen seconds failing to prove
`is_bool = is_int`, a claim its own peel had manufactured, before closing
the real goal in milliseconds. Removing both moves changed no verdict on
the corpus and simplified the prover to the three moves above.

The one goal-level move that survives is the one that is *not* a
congruence: inlining spends the library's defining equations, which
saturation is deliberately not allowed to do by itself.

Peel and descend still exist — after the search rather than before it.
A stuck goal's residual is **narrowed**: shared affixes stripped, branch
pairs with matching other arms entered, each step recorded, so the report
points at where the difference lives. The same moves are the natural
vocabulary for a human or agent directing a proof by hand, which is where
they belong.

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
the **residual**, which is what says what to try next — narrowed to where
the two differ (a `the difference is │ in the then arm` line walks past
shared context), plus why the search stopped and which rules did the work.
That output is the deliverable of a failed run, and it is how every rule
gap found so far was diagnosed.

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
  `pick 1 ; pick 1` lowers to by a recognizer — one direction, frames to
  block, since two `copy@2` leaves are one e-node and the classes meet
  without ever expanding a block into frames. The general `copy(n)` bridge
  should be derived, not enumerated, when a corpus term wants one.
