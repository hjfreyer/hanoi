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
identity identities::testing_a_test ... ok (saturated (4 iters, 6 classes))
identity identities::testing_a_test_by_name ... ok (inline; saturated (4 iters, 6 classes))
identity identities::specializing_a_tested_value ... ok (saturated (7 iters, 87 classes))
identity types_test::number_does_pre_and_post_is_constant ... ok (cut (left: inline; ...
...
identity result: ok. 14 passed; 0 failed; 0 problem(s); 0 filtered out
```

Exit codes keep the old contract: `0` every identity proved, `1` a claim
unproved or a hint orphaned, `2` the corpus would not build or the arguments
were wrong.

## The shape of the thing

Four layers, in `rewrite/src/`:

| layer | module | what it does |
|---|---|---|
| proofs | `hant.rs`, `corpus.rs` | the strategy language a proof is written in, and the loader that attaches each `.hant` entry to the identity it names |
| goals | `goal.rs`, `strategy.rs` | a goal is two [terms](../rewrite/src/term.rs) padded to one arity; the interpreter runs a strategy over one |
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

### The strategy language

A proof is a strategy: steps juxtaposed, manipulations first, a closer
last, written in the `.hant` beside the `.hana` that states the identity.
An identity with no entry gets the default — `egraph` alone — so the file
holds exactly the claims that need a human's direction:

```text
// identities.hant
proof identities::testing_a_test_by_name = inline egraph;
proof identities::something_harder =
    peel
    via { drop 0 push true } (left: inline egraph);
```

| step | does | fails when |
|---|---|---|
| `peel` | strips what the two compose spines share at either end | nothing is shared |
| `inline` | unfolds every call, all the way down | there are no calls |
| `symm` | swaps the two sides | never — but two in a row are refused |
| `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B` | the waypoint’s net stack change is not the goal’s, or a side fails |
| `solve (f: 1 -> 1) { … ?f … } (right: s)` | **cuts at a waypoint the engine fills in** | the template’s net is not the goal’s, nothing matches at the declared arities, or the right half fails |
| `egraph` | saturates; the sides meet or the gas runs out | it runs out of gas |
| `descend(then: s, else: s)` | forks a branch-vs-branch goal into its arms | the sides are not branches, or an omitted arm is not already equal |

A strategy acts on **one goal**, and the proof mirrors a tree of goals.
The manipulations transform the current goal; a splitter — `via` or
`descend` — replaces it with independent subgoals, each carrying its own
strategy inside the splitter; `egraph` closes it. So the closers end a
strategy, and what follows a split is written *inside* it. An omitted
`descend` arm is a *checked* claim that those arms already match, not a
shrug. A goal that becomes syntactically equal at any point closes on the
spot. And a step that finds nothing to do — `peel` with nothing shared,
`inline` with no calls — fails loudly rather than becoming a no-op, so a
proof that no longer matches its identity says so.

`via` is the transitivity cut. The author claims the waypoint sits between
the sides, and the goal splits into `A = C` and `C = B` — **fully
independent from that moment**: peel one, inline the other, cut one again;
proving both proves the whole. A wrong waypoint fails its half, *named*,
rather than being quietly ignored; a chain is nested cuts,
`via { c1 } (right: via { c2 })`, each link free to take a different road.
The two splitters default an omitted side differently, on purpose: a
`descend` arm was supplied by the goal, and equal arms are common, so
omission is a checked equality claim; a cut's sides are the author's own
construction and a trivially-equal side is a degenerate cut, so an omitted
`via` side gets `egraph` — handing the engine easier halves is what a cut
is *for*. (The alternative `via` design — seeding the waypoint into one
shared e-graph as a third root — was tried first and is strictly more
forgiving, which is exactly what is wrong with it *as `via`*: a wrong
stone is silently ignored instead of failing the proof, and a stuck run
cannot say which half of the journey failed. The forgiving behavior is a
coherent different step — see `egraph-hint` under "what is not here
yet".)

`symm` is the one step that claims nothing: equality is symmetric, so `A =
B` and `B = A` are the same goal. What it moves is which side the
*asymmetric* steps read — `solve` matches its template against the left
side, and a cut's halves are named for their sides — so it is how a proof
says "the interesting side is the other one" instead of restating the
identity backwards. Two in a row are the goal unchanged, and refused.

**A case split is a chain of cuts.** That is what discharges the corpus's
one path-condition claim, `types_test::number_does_pre_and_post_is_constant`
— see `tests/types_test.hant`. Its then arm is reached only when `is_tag`
held, and *that* fact is a disjunction (`v = t1` or `v = t2`) no rule window
can spend. So the proof writes the analysis out: one waypoint is the case
tree the test is, the next has the tested literal written into each arm —
which is what `specialize-equal` says and what the engine checks — and the
leaves are then a constant each, which folding reaches. Nothing conjures the
cases; the author names them and every hop is a checked claim.

`solve` is `via` with the waypoint under-specified — the cut with
metavariables. Its `?vars` stand for unknown subprograms at declared
arities; the engine saturates the goal and **e-matches** the template
against the left side's class. A match both finds the fills and *is* the
proof of the left half: the instantiated template's nodes live in that
class, put there by rule applications. The first match at the declared
arities wins, the fills are recorded in the proof (`solve (?f = drop(1);
…)`) so a different match after a rule-set change is visible rather than
mysterious, and only the right half — `C[fills] = B` — remains as a goal.
Declared-but-unmentioned and mentioned-but-undeclared variables are load
errors; a template that does not mean what it says must not quietly search
for something else. This is also the seed of lemma application: a template
with variables is the left-hand side of a lemma, and the matching machinery
built here is what citing a proven identity inside another proof will use.

Inside `egraph`: both sides go into one e-graph and
every rule fires, with a hook that stops the run the moment the two roots
unify — saturation has no goal of its own and would otherwise explore a
closed goal to the end of the budget (`discarded_work_on_copies` once grew
to 23,000 classes finding a proof it had at 51). `--explain` prints egg's
step-by-step account of the meeting; explanation tracking taxes every
union, so the e-graph only carries it when asked.

#### Why the default is the engine alone

The manipulations the language offers are not run automatically, and the
reason splits in two:

- **Peel and descend are congruences**, and an e-graph performs congruences
  intrinsically: unite `A` with `B` and the parents `P ; A` and `P ; B` are
  one e-node, merging for free; two branches merge the moment their arms
  do. When this crate ran these moves automatically they bought nothing and
  cost real money — a peeled subgoal can be **false** (`push 1 ; drop` =
  `push 2 ; drop`, minus the shared `drop`), and a false goal saturates to
  the end of its budget: `two_spellings_of_one_test` once spent fourteen
  seconds failing to prove `is_bool = is_int`, a claim its own peel had
  manufactured. As *directed* moves they are a different thing — the author
  who writes `peel` asserts the narrowed claim is the true one, and a wrong
  assertion fails loudly in a small goal.
- **Inline and via spend something.** `inline` spends the library's
  defining equations and multiplies the term; `via` spends an author's
  claim about the middle. Saturation is deliberately allowed neither on its
  own, which is why `testing_a_test_by_name` carries the corpus's first
  written proof.

So the working assumption is the one the tool is built around: the engine
closes what the equations reach, and for anything non-trivial a human
manipulates the goal a little and lets the engine close what is left.

When the engine gives up, the same decomposition moves run *backwards over
the wreckage*: the residual is narrowed — shared affixes stripped, the one
differing arm entered, each step recorded — so the report points at where
the difference lives instead of printing two whole terms.

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
term containing the work is written down as a `via` waypoint instead, and
the forward rules connect it to both sides of its links.

One scheduling fact worth knowing, learned the expensive way: egg's backoff
scheduler bans rules by *match* count, and a fact rule matches everywhere
precisely because its pattern is small — it declines almost every match. Ban
one and you silence exactly the rare application it exists for. So only the
shape rules that actually grow the graph (associativity, the staircases, the
block expansions) are left bannable; every fact rule is exempted.

## The `.hant` file

One file beside each `.hana` that states identities, holding `proof` entries
in the strategy language above. Attachment is checked both ways: an entry
naming no stated identity is an error — a renamed identity must not
silently shed its proof — and a claim discharged twice was discharged once
too often. `via` bodies are programs, compiled by appending scratch
sentences to the corpus source so the whole parser and resolver are reused,
with one caveat: paths in a body resolve from the crate root.

The current corpus needs two entries. `identities.hant` holds one line —
`proof identities::testing_a_test_by_name = inline egraph;` — and
`types_test.hant` holds the corpus's one real proof: the case split of
`number_does_pre_and_post_is_constant`, written as a chain of cuts. Every
other identity closes on the rules alone.

## The failure output is the point

This is what that identity printed before its proof was written, and the two
lines it starts from are why the proof looks the way it does:

```
identity types_test::number_does_pre_and_post_is_constant ... FAILED

  what the left came to   │ copy(1) ;
                          │ (id(1) *
                          │  (copy(1) * push t1 ;
                          │   (id(1) * equal ;
                          │    branch { drop(1) ; push true } { id(1) * push t2 ; equal })) ;
                          │  branch {
                          │    copy(1) * push t1 ; id(1) * equal ;
                          │    (branch { … } { … } ;
                          │     (copy(1) * push (t1, 1) ; …))
                          │  } {
                          │    drop(1) ; push true
                          │  })
  what the right came to  │ drop(1) ; push true
  the search stopped      │ IterationLimit(40)
  rule firings
      1341  par-fuse
      1169  stair-deep-first
```

A stuck goal prints the smallest spelling saturation found for each side —
the **residual**, which is what says what to try next — narrowed to where
the two differ (a `the difference is │ in the then arm` line walks past
shared context), plus why the search stopped and which rules did the work.
That output is the deliverable of a failed run, and it is how every rule
gap found so far was diagnosed.

A term that does not fit the width breaks at every `;` of its spine, indents
a branch's arms inside their braces, and lines a parenthesized group up under
its paren; anything that still fits stays on one line. The parentheses are
the same ones the one-line spelling uses, so a broken term still says which
tree it came from — the layout only chooses where the newlines go.

## What is not here yet

- **A case split as a *step*.** The corpus's path-condition claim closes
  today, but by hand: `tests/types_test.hant` writes each state of the
  analysis out as a waypoint, and the cases come from the author rather than
  from the goal. A `cases` step would read the tree off the test itself —
  enter each arm, carry its condition, specialize, prove the leaves — and
  the four waypoints that proof spells out would be four it derived. Unlike
  peel and descend it is not a congruence, so it will earn its keyword. What
  it needs first is a way to *state* the condition an arm carries, which is
  the same machinery `solve`'s templates began.
- **A replayable derivation.** A close currently answers with egg's
  explanation (`--explain`); nothing independent re-checks it yet. The next
  milestone translates explanations into the flat derivation format a small
  applier can replay, restoring the old system's "finding and checking are
  different jobs" property.
- **`egraph-hint { body }`.** The seeding semantics `via` deliberately does
  not have, as its own step: drop a term into the closing `egraph`'s graph
  as a third root, claiming nothing. A hint can help *catalytically* — its
  subterms hash-cons into classes the sides share, and rewrites discovered
  on its material carry over — without ever being equal to either side,
  which a cut cannot express. The cost is exactly the forgiveness: a
  useless hint is silently ignored. Worth adding the day a goal wants a
  nudge rather than a milestone; the plumbing (`via`'s body compilation)
  is already the hard part and is built.
- **Block operators at width n.** `copy(2)` is bridged to the frame spelling
  `pick 1 ; pick 1` lowers to by a recognizer — one direction, frames to
  block, since two `copy@2` leaves are one e-node and the classes meet
  without ever expanding a block into frames. The general `copy(n)` bridge
  should be derived, not enumerated, when a corpus term wants one.
