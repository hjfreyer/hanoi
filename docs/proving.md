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

Five layers, in `rewrite/src/`:

| layer | module | what it does |
|---|---|---|
| proofs | `hant.rs`, `corpus.rs`, `parse.rs` | the strategy language a proof is written in, the loader that attaches each `.hant` entry to the identity it names, and the reader that turns a waypoint's text into a term |
| goals | `goal.rs`, `strategy.rs` | a goal is two [terms](../rewrite/src/term.rs) padded to one arity; the interpreter runs a strategy over one |
| engine | `lang.rs` | the term model as an egg language, with a per-class analysis carrying the facts rules condition on |
| equations | `rules.rs` | every law, as a rewrite the e-graph applies in both directions where both are bounded |
| diagrams | `diagram.rs` | the string-diagram engine: programs as wiring in an interned arena, canonicalized into ordered, shared case trees — the decision procedure the cartesian layer's completeness theorem promises, spent by the `norm` steps |

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
    via { drop(1) ; push true } (left: inline egraph);
```

| step | does | fails when |
|---|---|---|
| `peel` | strips what the two compose spines share at either end | nothing is shared |
| `inline` | unfolds every call, all the way down | there are no calls |
| `inline(name)` | unfolds the calls to that one sentence | it is not called here |
| `symm` | swaps the two sides | never — but two in a row are refused |
| `exact` | closes the goal if the sides are one term as written | they differ — and the residual is the goal untouched, which is what the step is usually for |
| `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B` | the waypoint’s net stack change is not the goal’s, or a side fails |
| `solve (f: 1 -> 1) { … ?f … } (right: s)` | **cuts at a waypoint the engine fills in** | the template’s net is not the goal’s, nothing matches at the declared arities, or the right half fails |
| `egraph` | saturates; the sides meet or the gas runs out | it runs out of gas |
| `descend(then: s, else: s)` | forks a branch-vs-branch goal into its arms | the sides are not branches, or an omitted arm is not already equal |
| `norm (left: s, right: s)` | **cuts at the left side's normal form**: `A = B` splits into `A = NF(A)` and `NF(A) = B`, with the case tree reified back into a term as the waypoint | a half fails |
| `norm_trusted (right: s)` | the same cut with `A = NF(A)` closed on the normalizer's word | the right half fails |

A strategy acts on **one goal**, and the proof mirrors a tree of goals.
The manipulations transform the current goal; a splitter — `via` or
`descend` — replaces it with independent subgoals, each carrying its own
strategy inside the splitter; `egraph` closes it. So the closers end a
strategy, and what follows a split is written *inside* it. An omitted
`descend` arm is a *checked* claim that those arms already match, not a
shrug. A goal that becomes syntactically equal at any point closes on the
spot. And a step that finds nothing to do — `peel` with nothing shared,
`inline` with no calls, `inline(name)` where nothing calls it — fails loudly
rather than becoming a no-op, so a proof that no longer matches its identity
says so.

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

`inline` takes an optional label, and the label is usually what you want.
Unlabelled it opens every call on both sides, all the way down — which means
the *other* side of the next cut has to spell out everything that came open,
and the engine pays for all of it. `inline(is_tag)` opens the calls to that
one sentence and leaves the rest shut, so a waypoint can go on naming them:
the corpus's contract proof opens the function under test and its
precondition, keeps `number` and `is_numbered` as calls through four cuts,
and its first hop went from 336 e-classes to 79 when it stopped opening them.
Recursion is forbidden, so one pass opens every instance of the label; a
label naming a sentence the library does not have is a load error, and one
that is simply not called here fails the step, loudly, like any other step
that found nothing to do.

`exact` is the closer that searches nothing: it claims the two sides are
already one term, syntactically. As a proof step it is the strongest and
cheapest claim there is, but its everyday use is the *failure*: every other
report is post-mortem material — `egraph`'s residual is the smallest spelling
saturation found, narrowed to the difference — while a failed `exact` prints
the goal exactly as it stands. `proof x = exact;` shows an identity as
lowered and aligned, and `inline(f) exact` shows what the inline left, in the
language a waypoint is written in — which makes it the way to *start* a
proof: write `exact`, read the goal, replace `exact` with the real strategy.

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

`norm` and `norm_trusted` spend the decision procedure the algebra sheet
promises ([docs/algebra.md](algebra.md), "a cheap oracle"), and its home is
`diagram.rs` — the **string-diagram engine**. A program there is wiring,
not a term: operations are boxes with ordered ports, values are wires in an
interned arena, and the whole structural layer is representation rather
than rules — `id` is a wire, `;` and `*` are not stored, `swap` is a
crossing the data structure does not remember, `copy` is a wire read
twice, `drop` a wire nobody reads. Interning makes `copy-nat` automatic
and reachability makes `drop-nat` automatic, so for branch-free programs
the wiring *is* the free cartesian category's normal form, and agreement
is complete for layer 1. Branches take the decision-diagram discipline:
the canonical form is an **ordered, shared case tree** — conditions in one
global order along every path, so programs that test independent
conditions in different orders reach one spelling; equal subtrees are one
node, so reconverging check chains stay small. What remains outside is
genuinely semantic: η — inventing a case split on an opaque value — is the
pinned boundary (`eta_stays_beyond_the_diagram`). Along the way the
evaluator picks up, for free, much of what the rules state one window at a
time: literal windows run on the machine itself (the same `run_window` the
`eval` rule uses), a literal condition takes its arm, a retested condition
is decided, a value that tested `equal` to a literal *is* that literal in
the then arm, commutative operands sort, and equal arms never branch.
Calls stay opaque — `inline` remains the step that spends a definition.

Both spellings are the **same cut**: `A = B` splits at the left side's
normal form, reified back into a canonical term, into `A = NF(A)` and
`NF(A) = B`. One side only, on purpose — that is what makes the step
compose. A right side that needs normalizing too writes `symm norm…`
inside itself, and when both sides normalize to one tree the chain's last
goal is one term as written and closes on the spot:
`norm_trusted (right: symm norm_trusted)` is "normalize both sides and
meet in the middle", with no saturation anywhere. Where the two spellings
differ is **who answers for the left half**. `norm` hands `A = NF(A)` to a
strategy (`egraph` by default), so nothing new is trusted — and the half
can still fail on a true claim when the rules cannot reach the reified
spelling. `norm_trusted` closes that half on the normalizer's word,
recorded as such in the proof (`norm (left: trusted; …)`), so a report can
always say which claims lean on it. The trade is real and measured, on the
corpus's contract claim `types_test::number_does_pre_and_post_is_constant`,
whose written proof is a page of hand-derived cuts: the trusted chain
closes it in milliseconds, plain `inline norm_trusted` a few more (its
right half, `NF(A)` against the small stated answer, is an easy
saturation), and checked `inline norm` times out — `A = NF(A)` across a
whole inlined case analysis is as hard as the original claim. The intended
trajectory is that of a proof-producing normalizer: today's `norm_trusted`
is scaffolding for finding workable strategies, and every use of it is a
claim the checked machinery should eventually reach — via `norm`'s cut, a
`cases` step, or a replayable trace out of the evaluator itself.

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
too often. A body — a `via` waypoint or a `solve` template — is a **term**, read by
`rewrite/src/parse.rs`, which is the inverse of the printing residuals use.
That is the point: a residual says `copy(1) ; id(1) * push t1 ; equal`, the
waypoint answering it is written the same way, and nothing is translated by
hand. Two consequences worth knowing. Nothing pads — the term language says
what it means, so a body whose halves do not meet is `cannot compose 1 -> 2
with 1 -> 1` where it is written, rather than something quietly widened. And
a call is named (`call types_test::number`, or any unambiguous tail of that),
which is also how a residual prints one when the report has the library to
hand; `Display` alone can only say `call #3`.

Bodies used to be Hana sentences, appended to the corpus source so the real
parser and resolver did the work. It cost the author a translation of every
waypoint out of the language the report had just printed, and it cost `solve`
a scratch **hole sentence** per variable, written to have the declared arity
so the lowering's padding arithmetic had something to chew on. Now the arity
is on the variable and `?f` is a leaf of the term.

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
