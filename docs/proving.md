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
Proving 15 identities...
identity identities::testing_a_test ... ok (the two sides are one diagram)
identity identities::testing_a_test_by_name ... ok (inline; the two sides are one diagram)
identity barista::customer_impl::emit_does_pre_and_post_is_constant ... ok (inline; both: 299 rewrite(s); cases: 1 split(s) (true: 209 rewrite(s); false: 0 rewrite(s)); the two sides are one diagram)
...
identity result: ok. 15 passed; 0 failed; 0 problem(s); 0 filtered out
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
`view-value` held to last, `select-hoist` held off every list), and the
value layer — a literal window runs on
the real `vm` (one `run_window`, no second semantics, `fold`), a promised
bool tests true (`tested-bool`), retupling is the coercion (`retuple`), a
value already coerced survives that round trip (`as-tuple-round-trip`), and a
tuple the window watched being built answers what shape it is
(`is-tuple-built`).

Three rows sit outside every list, because they **grow** a graph. Two are the
unpackings: `as-bool-branch` (`as_bool` is the branch it makes) and
`coercion-guard` (a coercion is the guarded identity the instruction set
describes it as, the width part of the guard for `as_tuple n`). A driver run to
fixpoint wants rows that shrink, and *whether to unpack a coercion* is a
decision of the same kind `inline` is — so a proof names the one it wants:
`lhs(fire(coercion-guard)) diagram` is the whole of three corpus identities.
What they buy is the direction the rest of the table cannot read: a coercion is
opaque to every rule that asks what a value *is*, and these put the test that
decides it where a case split can spend it.

The third is `select-hoist`, and it is what lets a branch grow **forwards**.
`fork-hoist` moves work across the fork in either direction, so a branch could
always swallow what fed it; nothing said the same at the select, so everything
downstream of one was out of the branch layer's reach and a select could be
deleted but never moved. The row is the commuting conversion — what runs after
a branch runs inside whichever arm the branch takes — and it carries the region
it moves the branch over as payload, the way `shannon` carries its body. The
two are worth keeping apart: `shannon` *makes* a branch out of a wire by
pinning that wire to `true` and `false` in its two copies, which is why it is
refused unless the instruction set promises the wire is a bool. `select-hoist`
pins nothing and makes no branch — the condition reaches the moved select
untouched — so it holds of **any** branch, whatever computed the condition.

The `diagram` closer drives the whole table to fixpoint on each side
(`tactic::decide`) and asks one final question: are the two graphs
**isomorphic** — the same boxes wired alike, dead slots and id numbers not
counting? An earlier engine (`diagram.rs`, an interned value-DAG under
ordered case trees) decided the same fragment by canonicalization; it is
gone, and what it decided by construction the table now spends as named,
checked, replayable steps.

Two things the driver deliberately never does: it never opens a
[call](../rewrite/src/term.rs) (`inline` is a proof's decision), and it
never reasons by case analysis on an unknown value (`cases` is a proof's
decision). Everything else it decides by running the table dry.

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
| `cases(op)` | **case analysis** on an intermediate result: an `op` answer can only be `true` or `false`, so everything that depends on it is replaced by a branch holding one copy per case, the assumed answer pasted in as a literal — one checked rewrite per side, which the ordinary laws then simplify under each assumption (see below) | no side computes `op`, or nothing depends on its answer |
| `cases(op(lit))` | the same split, with the wire addressed by what it tests: the outermost `op` one of whose operands is the pushed literal `lit` names — by any tail of its spelling, the way `inline` names a sentence | no such test |
| `cases(op) (true: s, false: s)` | the same split, with a sub-strategy per case, each run with its rewrites scoped to its side of the fresh branch — hypothesis-style authorship, compiled to ordinary checked steps in the split's own record (see [docs/hypotheses.md](hypotheses.md)). An arm holds side rewrites and nested `cases`; either is omissible, and a goal side whose branch is already gone skips its arms quietly | the split fails, or an arm's tactic does — and the residual names whose case it stood in |
| `diagram` | rewrites both sides by the whole table to fixpoint and asks whether they landed on one diagram — isomorphic | they did not — and the residual is both sides as they stand, listed box by box (or, with `--terms`, read back and narrowed to the difference) |

Inside `lhs(…)`, `rhs(…)` and `both(…)` is the rewrite language of
[docs/tactics.md](tactics.md), juxtaposed like steps are: `saturate` (the
structural laws to fixpoint), `saturate(law, …)`, `branches` (the branch
layer with its cleanup), `fire(law, …)` (one directed firing),
`at(#box, law)` (one firing at a **named box**), `repeat(…)` and `try(…)`
— laws named as the algebra sheet names them, `copy-elim`, `select-view`,
`dead-node`, with `structural` and `branching` naming the two lists.

`at` is the step that answers the report in the report's own words. `fire`
takes the first match it is offered anywhere on the side; when that is the
wrong one, `at(#41, fork-hoist)` names the box the residual listing printed
beside the line, and fires the law in a match that holds *that* box —
anywhere in the match, not only where the law's pattern happens to anchor.
A third field is the direction, `forward` when it is left out:
`at(#41, select-same, backward)` reads the law's equation right to left,
which is how a proof says "put this back", and it finds something wherever
the law's right-hand side names enough boxes to be looked for. An id is an
exact address and a brittle one: it means one box of one graph at one
moment, so an `at` is written by reading a report and holds only against
the goal that report described — change a step in front of it and the ids
behind it move. A proof whose named box is gone fails saying so, by name,
rather than firing somewhere else.

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

### `cases`: proving what depends on a value

Some true equations are out of the rewriter's reach, because the two
sides only agree once you consider what some intermediate result **is**,
and the rewriter treats every computed value as opaque. The corpus's
plainest example:

```text
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

Whatever `is_bool` answers is a boolean, so asking `is_bool` of *that*
answers `true` — a fact about the operation's range, not about any wiring
a rewrite window could see. That particular fact is common enough to be
its own law (`tested-bool`); the general situation is not, and `cases` is
the general instrument.

`cases(op)` picks an intermediate result — a wire — produced by an
operation the instruction set guarantees answers a boolean (`equal`,
`is_int`, `not`, …; the parser refuses anything else). That answer is
`true` or it is `false`, and there is no third case. So the following is
an ordinary equation, and a row of the table (the Shannon expansion,
`shannon` in [rewrite/src/diagram2/rules.rs](../rewrite/src/diagram2/rules.rs)):

```text
everything downstream of the wire
    =  branch on the wire {
           the same computation, with the answer assumed true
       } {
           the same computation, with the answer assumed false
       }
```

The right side duplicates the downstream computation, once per case, with
the assumed answer pasted in as a literal, and a branch keeps whichever
copy agrees with the actual answer. Running both copies and discarding
one is sound here for the same reason every branch in this language is:
operations are total and pure, so the untaken copy is an answer nobody
reads.

The step itself does almost nothing: on each side of the goal that
computes `op`, it fires that row **once**, at the earliest such wire —
the one with the least computation feeding it — and that firing is an
ordinary rewrite, checked like any other. The power is in what the rest
of the table does *afterwards*, inside the copies, where the assumption
is now a literal: a branch on it resolves (`select-const`), a test
against it computes (`fold`), untouched code falls away (`dead-node`).
When both copies simplify to the same thing, the introduced branch
collapses too (`dedup`, then `select-same`), and the goal closes by plain
rewriting — the case analysis happened, and every step of it is in the
proof's record.

Two practical notes. *Earliest matters*: splitting on a result computed
late says nothing usable about the computations feeding it, so the step
always takes the earliest test and leaves later ones to be decided along
the way — or split in turn, which is what chaining does:
`cases(equal) cases(equal)` is a two-variable case analysis, four leaves,
all folded shut by the closing `diagram`. And *identification comes
first*: a program often retests one condition in several places (through
copies and branch views), and the split only helps once the driver has
recognized those as a single wire — which `both(decide)` does, via
`view-value` and `dedup` — so `cases` almost always follows a drive.

The corpus's contract claim is the worked example. It was once a page of
hand-derived waypoints, then one `inline diagram` under the old
canonicalizing engine; it is now written as what the claim actually is —
a case analysis over the two tags an input might be:

```text
proof types_test::number_does_pre_and_post_is_constant =
    inline both(decide) cases(equal) both(decide) cases(equal) diagram;
```

Open the definitions, drive, split on `equal(x, t1)`, drive, split on
`equal(x, t2)`, and the closer folds every leaf shut. (For readers who
know the literature: this is η — the case split on an opaque value that
canonical forms cannot make — spent deliberately, as a checked rewrite.)

The hypothesis-style surface over this step — one sub-strategy per
case, its rewrites scoped to that case's side of the fresh branch — is
designed in [docs/hypotheses.md](hypotheses.md), together with the
argument that it compiles to the derivations this page describes and
costs the checker nothing; it has since landed, and the corpus's biggest
goal is its worked example. `barista::customer_impl::
emit_does_pre_and_post_is_constant` — the contract claim over a
four-state machine, 351 boxes against 2 once `inline` has opened it —
closes as a decision tree of three hypotheses:

```text
proof barista::customer_impl::emit_does_pre_and_post_is_constant =
    inline both(decide)
    cases(equal(state::thirsty)) (
        true: both(decide) cases(is_symbol) (
            true: both(decide) cases(is_symbol) (
                true: both(decide),
                false: both(decide)),
            false: both(decide)),
        false: both(decide))
    diagram;
```

The addressed split is what makes the tree writable at all: the goal
holds two dozen `equal`s, and the outermost is the tuple-shape guard —
splitting there is a fixpoint that decides nothing. `cases(equal(state::
thirsty))` splits the one test `emit` dispatches on, which the drive has
already identified with the precondition disjunction's own; its false
case closes vacuously (the emitted flag is false, so the postcondition
holds whatever the precondition said), and its true case resolves `emit`
outright, leaving the nested `is_symbol` splits to decide the payload
checks — by then the very boxes the precondition tested. The whole tree
lands in one flat record per side, replayed blind by the checker.

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

The current corpus needs four entries: `inline diagram` for
`identities::testing_a_test_by_name` (its right side is written as a
call), `both(decide) cases(equal) diagram` for
`identities::specializing_a_tested_value` (an arm recomputing the very
test its branch decided — a case split, once the driver has identified the
two computations as one wire), the two-`cases` proof above for
`types_test`'s contract claim, and the structured tree for `barista`'s.
Every other identity closes with no entry at all.

## The failure output is the point

A stuck goal prints its **residual**: the two sides as they stand, plus why
the step gave up. That output is the deliverable of a failed run, and it
comes in two spellings because reading a goal and answering one are
different jobs.

**The graphs are what it shows.** One line per box — its id, what it reads,
what reads it — with a branch written as the block it is: `if <condition>`
at the `fork` where there is one, `else` where the second arm begins, and
`endif <condition>` at the `select`, the arms indented between them. The
condition is named on all three lines, so a block deep in a nest says which
wire it turns on; a line with an empty id column is one the listing drew
rather than a box. This is what the tactics acted on, so a next
step names the boxes it names — literally, with `at(#41, law)`, which is
the one address in the tactic language that is a name rather than a
description; and a `NodeId` is stable for the life of a graph (nodes are
only deleted, never moved), so two reports of one proof compare, which is
what watching a proof means. Four things make a large one
legible, and `rewrite/src/diagram2/render.rs` states each: branch
membership is *computed* (downstream of the fork ∩ upstream of the select)
rather than guessed from what sits between two lines; the order stays
inside a branch once it enters one, instead of hoisting an arm's constants
out of the arm; a box that reads nothing is placed just before the box that
reads it, so an operand sits with its `equal`; and `id` and `copy` are read
through, since they are what the structural laws delete and a `copy` says
what the links already say. `--boxes` shows them.

**The terms are what it answers with.** `--terms` prints the two sides read
back into the term language and narrowed to where they differ (an `as
terms, they differ │ …` line strips shared context), so a false claim
buried in one branch arm behind a shared prefix prints as the two leaves
that disagree rather than as two whole programs. This is the spelling to
ask for when writing a `via`: the reified form is in the same language a
waypoint is, so answering a residual is copying and editing rather than
translating.

A term that does not fit the width breaks at every `;` of its spine, indents
a branch's arms inside their braces, and lines a parenthesized group up under
its paren; anything that still fits stays on one line. The parentheses are
the same ones the one-line spelling uses, so a broken term still says which
tree it came from — the layout only chooses where the newlines go. What it
does *not* do is spell the width it was written across: `read_back` emits
every step over the whole live stack, and the two unit laws — `id(a) * id(b)
= id(a + b)` over the flattened product, `id(n) ; t = t` — take that back
off before anything prints it.

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
- **Reify for the giants.** A read-back shares nothing a term cannot, so a
  handful of state-machine test sentences would print past any reasonable
  size if a residual ever needed one; scratch definitions for shared
  subgraphs would close that gap.
