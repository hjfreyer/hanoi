# Proving identities

`bin/prove` discharges the claims `identity A = B;` states. It is built on a
**decision procedure** rather than a search: both sides of a goal lower into
the string-diagram engine of `rewrite/src/diagram.rs`, normalize into one
arena, and either they are one diagram or they are not. There is no rule
set to steer and no budget to run out of; what a written proof directs is
the handful of moves the engine deliberately never makes on its own —
opening a call, above all.

```bash
cargo run --bin prove -- tests
cargo run --bin prove -- tests --filter two_spellings
```

```
Proving 14 identities...
identity identities::testing_a_test ... ok (the two sides are one diagram)
identity identities::testing_a_test_by_name ... ok (inline; the two sides are one diagram)
identity types_test::number_does_pre_and_post_is_constant ... ok (inline; the two sides are one diagram)
...
identity result: ok. 14 passed; 0 failed; 0 problem(s); 0 filtered out
```

Exit codes keep the old contract: `0` every identity proved, `1` a claim
unproved or a hint orphaned, `2` the corpus would not build or the arguments
were wrong.

An earlier incarnation of this pipeline ran equality saturation over the
term model (the `egg` library), with the algebra sheet written out as a
rule set. It worked, and it taught the lesson that retired it: ~95% of its
work was translating between paddings and groupings of the *same* wiring so
that the semantically meaningful rules could find their fixed windows. The
diagram engine makes that entire layer *representation* — there is nothing
to translate — and what is left of "proving" is the part that was always
real: which definitions to spend, and where a claim actually fails.

## The shape of the thing

Four layers, in `rewrite/src/`:

| layer | module | what it does |
|---|---|---|
| proofs | `hant.rs`, `corpus.rs`, `parse.rs` | the strategy language a proof is written in, the loader that attaches each `.hant` entry to the identity it names, and the reader that turns a waypoint's text into a term |
| goals | `goal.rs`, `strategy.rs` | a goal is two [graphs](../rewrite/src/diagram2/mod.rs), lowered and padded to one arity before they build; the interpreter runs a strategy over one |
| engine | `diagram.rs` | the string-diagram engine: programs as wiring in an interned arena, canonicalized into ordered, shared case trees — the decision procedure the algebra's completeness theorem promises |

### Goals, and where the net-change asymmetry lives

The compiler holds an identity to equal **net** change, not equal arity —
`pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`. In the term model that
asymmetry is resolved in exactly one place: `Goal::aligned` pads the narrower
side with `id(k) *` until the arities agree. Every downstream question is
then arity-exact, which is what lets a diagram's leaves be tuples of a fixed
width.

### The engine

A program in `diagram.rs` is wiring, not a term: operations are boxes with
ordered ports, values are wires in an interned arena, and the whole
structural layer of [docs/algebra.md](algebra.md) is representation rather
than rules — `id` is a wire, `;` and `*` are not stored, `swap` is a
crossing the data structure does not remember, `copy` is a wire read twice,
`drop` a wire nobody reads. Interning makes `copy-nat` automatic and
reachability makes `drop-nat` automatic, so for branch-free programs the
wiring *is* the free cartesian category's normal form, and equality is
complete for the structural layer.

Branches take the decision-diagram discipline: the canonical form is an
**ordered, shared case tree** — conditions in one global order along every
path, so programs that test independent conditions in different orders
reach one spelling; equal subtrees are one interned node, so reconverging
check chains stay small; the arm that tested a value `equal` to a literal
holds the literal. Every law of the algebra sheet with a bounded, confluent
reading is folded in as the diagram builds: literal windows run on the real
`vm` (one `run_window`, no second semantics), a literal condition takes its
arm, a retested condition is decided, commutative operands sort, the tuple
laws and coercion idempotences apply, a `yields_bool` answer passes its
test. What remains outside is genuinely semantic: η — inventing a case
split on an opaque value — is the pinned boundary
(`eta_stays_beyond_the_diagram`), and claims that need it stay open until
there is a step that spends it.

Two things the engine deliberately never does: it never opens a
[call](../rewrite/src/term.rs) (`inline` is a proof's decision), and it
never invents a case split. Everything else it decides outright, in one
pass, with no budget.

### The strategy language

A proof is a strategy: steps juxtaposed, manipulations first, a closer
last, written in the `.hant` beside the `.hana` that states the identity.
An identity with no entry gets the default — `diagram` alone — so the file
holds exactly the claims that need a human's direction:

```text
// identities.hant
proof identities::testing_a_test_by_name = inline diagram;
```

| step | does | fails when |
|---|---|---|
| `lhs(tactic)` / `rhs(tactic)` / `both(tactic)` | runs a [graph tactic](tactics.md) on that side of the goal, every rewrite a named law checked by `rules::apply` | the tactic fails — and the residual shows the goal **as it now stands**, the last rewrite that landed still standing |
| `inline` | opens every call in both graphs, all the way down | there are no calls |
| `inline(name)` | opens the calls to that one sentence | it is not called here |
| `symm` | swaps the two sides | never — but two in a row are refused |
| `exact` | claims the sides are one diagram — **isomorphic** — which the auto-close has already checked, so a reached `exact` fails and shows the goal exactly as it stands | always, when reached |
| `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B`, the waypoint built as a graph | the waypoint's net stack change is not the goal's, or a side fails |
| `diagram` | reads both sides back as terms and normalizes them into one arena; they are one diagram or they are not | they are not — and the residual is both sides reified, narrowed to the difference |

Inside `lhs(…)`, `rhs(…)` and `both(…)` is the rewrite language of
[docs/tactics.md](tactics.md), juxtaposed like steps are: `saturate` (the
structural laws to fixpoint), `saturate(law, …)`, `branches` (the branch
layer with its cleanup), `fire(law, …)` (one directed firing), `repeat(…)`
and `try(…)` — laws named as the algebra sheet names them, `copy-elim`,
`select-view`, `dead-node`, with `structural` and `branching` naming the
two lists.

A strategy acts on **one goal**, and the proof mirrors a tree of goals.
The manipulations transform the current goal; the splitter — `via` —
replaces it with independent subgoals, each carrying its own strategy
inside the split; `diagram` closes it. So the closers end a strategy, and
what follows a split is written *inside* it. A goal whose sides become
**isomorphic** at any point closes on the spot — which is the second road
to a proof: rewrite a side until the two are one graph, and the isomorphism
is the closure. And a step that finds nothing to do — `inline` with no
calls, a `fire` no law matches — fails loudly rather than becoming a no-op,
so a proof that no longer matches its identity says so.

Beside a decision procedure the steps carry a different weight than they
did beside a search. `inline` is the one that **changes what is provable**:
the engine treats a call as an opaque box, so an identity that holds
because of what a sentence *does* needs its definition spent, and the proof
says exactly which ones (`inline(is_tag)` opens one sentence and leaves the
rest closed, so the report keeps naming what it does not care about). The
rest direct and report: the tactic steps spend named laws where the author
points them; `via` so a failure can say which half of a journey it lives
in and be checked against a named midpoint; `exact` to show a goal exactly
as it stands — write `proof x = exact;`, read the goal as built and
aligned, then replace `exact` with the real strategy. `symm` claims
nothing: equality is symmetric, and what it moves is which side the
asymmetric steps read.

An omitted `via` side gets `diagram`: a cut's sides are the author's own
construction, and handing the decision procedure the halves is what a cut
is for. `peel` and `descend` are retired — both read the goal as a term,
and a graph goal has no compose spine to strip and no branch node to fork;
the residual's own narrowing still shrinks what a report prints, and the
branch layer's laws are how arms get reasoned about now.

**A case split is not a chain of cuts anymore.** The corpus's
path-condition claim, `types_test::number_does_pre_and_post_is_constant`,
used to be a page of hand-derived waypoints — the case tree written out
state by state, because its then arm is reached only when `is_tag` held,
and that fact is a disjunction no rewrite window could spend. The diagram
engine builds the case tree itself: branches become ordered decisions, the
arm that tested equal to a literal holds the literal, each leaf folds on
the machine. The whole proof is now `inline diagram` — the one thing left
to say is which definitions to spend.

**Trust.** The engine produces no derivation: `diagram` closing a goal is
this one module's word, held to the machine by `run_window` (folding runs
the real `vm`) and to the corpus by tests. That is a smaller trusted base than the previous stack — a rule set,
a saturation engine, and a separate normalizer, each of which could
disagree with the others — but it is one judge, and the "replayable
derivation" milestone below is what turns its verdicts into checkable
artifacts.

## The `.hant` file

One file beside each `.hana` that states identities, holding `proof` entries
in the strategy language above. Attachment is checked both ways: an entry
naming no stated identity is an error — a renamed identity must not
silently shed its proof — and a claim discharged twice was discharged once
too often. A body — a `via` waypoint — is a **term**, read by
`rewrite/src/parse.rs`, which is the inverse of the printing residuals use.
That is the point: a residual says `copy(1) ; id(1) * push t1 ; equal`, the
waypoint answering it is written the same way, and nothing is translated by
hand. Two consequences worth knowing. Nothing pads — the term language says
what it means, so a body whose halves do not meet is `cannot compose 1 -> 2
with 1 -> 1` where it is written, rather than something quietly widened. And
a call is named (`call types_test::number`, or any unambiguous tail of that),
which is also how a residual prints one when the report has the library to
hand; `Display` alone can only say `call #3`.

The current corpus needs two entries, and they are the same line: `inline
diagram` for `identities::testing_a_test_by_name` (its right side is
written as a call) and for
`types_test::number_does_pre_and_post_is_constant` (the contract claim).
Every other identity closes with no entry at all.

## The failure output is the point

A stuck goal prints its **residual**: what each side became — for a failed
`diagram`, the two sides reified from their normal forms back into the term
language — narrowed to where the two differ (a `the difference is │ in the
then arm` line walks past shared context), plus why the step gave up. A
false claim buried in one branch arm behind a shared prefix prints as the
two leaves that disagree, not as two whole programs. That output is the
deliverable of a failed run: the reified normal form is written in the same
language a `via` waypoint is, so answering a residual is copying and
editing rather than translating.

A term that does not fit the width breaks at every `;` of its spine, indents
a branch's arms inside their braces, and lines a parenthesized group up under
its paren; anything that still fits stays on one line. The parentheses are
the same ones the one-line spelling uses, so a broken term still says which
tree it came from — the layout only chooses where the newlines go.

## What is not here yet

- **Rewriting on diagrams** landed: goals are graphs, the tactic steps
  are the moves — each rewrite an instance of a named law of
  [rewrite/src/diagram2/rules.rs](../rewrite/src/diagram2/rules.rs),
  checked by `apply`, run into a replayable `Derivation` — and a goal
  rewritten until its sides are isomorphic is closed. See
  [docs/tactics.md](tactics.md). What remains of the old bullet is
  **reach**: the law table covers the structural and branch layers, so
  claims the `diagram` closer decides by *computing* (the value folds)
  still have no tactic spelling, and the two roads meet by using both.
- **A case split as a step.** A `cases` step that splits a goal on a
  boolean-valued wire, carrying the condition into each half — η spent
  deliberately, the way `inline` spends a definition. The branch layer's
  laws are the pieces it would be assembled from.
- **A derivation for the `diagram` closer.** A tactic close replays; a
  `diagram` close is still the engine's verdict, nothing independent
  re-checks it. The milestone stands: a normalizer that emits its steps —
  every fold and reorder an instance of a named law — so that finding and
  checking become different jobs again.
- **Reify for the giants.** A diagram shares branch subtrees and a term
  cannot, so a handful of state-machine test sentences tree-expand past any
  reasonable term. A reify that emits shared subtrees as scratch
  definitions would close that gap if a residual ever needs one of them
  printed.
