# Proving identities

`bin/prove` discharges the claims `identity A = B;` states. It is built on
**checked rewriting**: both sides of a goal build into the literal graphs
of `rewrite/src/diagram2`, a driver spends the law table on each until
nothing more fires, and either they land on one diagram — isomorphic — or
they do not. Every step on the way is an instance of a named law, verified
by `rules::apply` before it lands, so a close is a derivation's worth of
checked rewrites and one final isomorphism rather than any engine's word.
What a written proof directs is the handful of moves the driver
deliberately never makes on its own — opening a call, and splitting a case
on an opaque answer, above all.

```bash
cargo run --bin prove -- tests
cargo run --bin prove -- tests --filter two_spellings
```

```
Proving 14 identities...
identity identities::testing_a_test ... ok (the two sides are one diagram)
identity identities::testing_a_test_by_name ... ok (inline; the two sides are one diagram)
identity types_test::number_does_pre_and_post_is_constant ... ok (inline; both: 62 rewrite(s); cases (true: …; false: …))
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
| engine | `diagram2/` | the literal graph, the law table (`rules.rs`, every law a pair of graphs and every rewrite checked), the tactic language that drives it (`tactic.rs`, see [docs/tactics.md](tactics.md)), and the isomorphism that says two graphs are one diagram |

### Goals, and where the net-change asymmetry lives

The compiler holds an identity to equal **net** change, not equal arity —
`pick 1 ; drop` = ε is `(2 -> 2)` against `(0 -> 0)`. In the term model that
asymmetry is resolved in exactly one place: `Goal::aligned` pads the narrower
side with `id(k) *` until the arities agree. Every downstream question is
then arity-exact, which is what lets a diagram's leaves be tuples of a fixed
width.

### The engine

A program in `diagram2` is a **literal** graph: one box per term leaf,
`id`, `swap`, `copy` and `drop` included, and a branch as a `fork`/`select`
pair with its arms flattened between them. Nothing is simplified by
representation; everything is simplified by *rewriting*, against a table
(`diagram2/rules.rs`) whose every law is a pair of graphs `sides` builds
from a payload and whose every application `apply` verifies port by port.
The layers of [docs/algebra.md](algebra.md) are all rows: the structural
laws (`id-elim`, `swap-elim`, `copy-elim`, `dead-node`, `dedup`), the
branch layer (`select-literal` and its kin, the specializing rules,
`view-value` held to last), and the value layer — a literal window runs on
the real `vm` (one `run_window`, no second semantics, `fold`), a promised
bool tests true (`tested-bool`), retupling is the coercion (`retuple`).

The `diagram` closer drives the whole table to fixpoint on each side
(`tactic::decide`) and asks one final question: are the two graphs
**isomorphic** — the same boxes wired alike, dead slots and id numbers not
counting? An earlier engine (`diagram.rs`, an interned value-DAG under
ordered case trees) decided the same fragment by canonicalization; it is
gone, and what it decided by construction the table now spends as named,
checked, replayable steps.

Two things the driver deliberately never does: it never opens a
[call](../rewrite/src/term.rs) (`inline` is a proof's decision), and it
never invents a case split (`cases` is a proof's decision — η, spent
deliberately on a wire the instruction set promises is a bool). Everything
else it decides by running the table dry.

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

**A case split is a rewrite, and the proof says where.** The corpus's
path-condition claim, `types_test::number_does_pre_and_post_is_constant`,
was once a page of hand-derived waypoints, then one `inline diagram` under
the old canonicalizing engine. It is now what the claim actually is: a
case analysis, written out —

```text
proof types_test::number_does_pre_and_post_is_constant =
    inline both(decide) cases(equal) both(decide) cases(equal) diagram;
```

— open the definitions, drive the table (`view-value` and `dedup` are what
identify the retests of one condition as one wire), expand on `equal(x,
t1)`, expand on `equal(x, t2)`, and the closer folds every arm shut. Each
`cases` is **one checked rewrite**: the table's Shannon law, `body(w) = if
w then body(true) else body(false)`, sound because the instruction set
promises the wire a bool, refused by `sides` otherwise. The introduced
branch dissolves inside the graph — `select-const` where a pinned copy
decided, `dedup` and `select-same` where both arms agree — so the
disjunction `is_tag` carries is spent exactly where the proof says η is
spent, as steps a checker verified.

**Trust.** `sides` and `apply` are the whole of it — plus the machine
itself, where a law is *about* what an operation computes (`fold` and the
Shannon expansion consult `run_window`, the real `vm`, so there is no
second semantics to drift). Search, drivers, tactics, queries and the
`cases` step's wire-picking are all untrusted: every step they produce
goes through `apply`, a wrong one is refused, and a close is the
isomorphism check on what the checked steps left. And a close is **not
the prover's word**: a `Proof` carries its full record — every step each
drive landed, the inline's target, the cut's waypoint — and
`Prover::prove` re-checks the whole tree against the goal as stated
before answering, replaying every step through the table and asking
every isomorphism again. A proof that does not re-check comes back
*stuck*, fail closed, named as the prover bug it is. What remains one
module's word is `isomorphic` itself, and it is held to answering `true`
only after verifying its bijection link by link.

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

The current corpus needs three entries: `inline diagram` for
`identities::testing_a_test_by_name` (its right side is written as a
call), `both(decide) cases(equal) diagram` for
`identities::specializing_a_tested_value` (an arm recomputing the very
test its branch decided — a case split, once the driver has identified the
two computations as one wire), and the two-`cases` proof above for the
contract claim. Every other identity closes with no entry at all.

## The failure output is the point

A stuck goal prints its **residual**: what each side became — for a failed
`diagram`, the two rewritten graphs read back into the term language —
narrowed to where the two differ (a `the difference is │ …` line strips
shared context), plus why the step gave up. A
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

- **The proof object lives in memory only.** Every close carries its
  full record and is re-checked before it is reported — but nothing yet
  *persists* a `Proof` to disk, so re-checking without re-proving means
  serializing the artifact (its steps, matches, waypoint terms) beside
  the corpus. The shape is ready; the file format is not chosen.
- **Reach.** The value layer folds literal windows, promised bools and the
  tuple round trip; the old engine also sorted commutative operands and
  collapsed coercion idempotences, and no law spells those yet. A claim
  that needs one fails honestly, and the row is a `sides` construction
  away.
- **`cases` names an operation, not a wire.** The step expands the
  outermost box of the named prim, which is right until a goal holds two
  equally outermost tests of the same operation; the query language of
  [docs/tactics.md](tactics.md) is the vocabulary a sharper `cases` would
  take.
- **Reify for the giants.** A read-back shares nothing a term cannot, so a
  handful of state-machine test sentences would print past any reasonable
  size if a residual ever needed one; scratch definitions for shared
  subgraphs would close that gap.
