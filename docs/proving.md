# Proving identities

`bin/prove` discharges the claims `identity A = B;` states. Both sides of
a goal build into literal graphs, a driver spends the law table on each
until nothing more fires, and either they land on one diagram —
isomorphic — or they do not. Every step on the way is an instance of a
named law, verified before it lands, so a close is a derivation's worth
of checked rewrites and one final isomorphism rather than any engine's
word. What a written proof directs is the handful of moves the driver
deliberately never makes on its own — opening a call, and splitting a
case on an opaque answer, above all.

Companions: [docs/rules.md](rules.md) is the reference for the laws,
[docs/tactics.md](tactics.md) for the rewrite language that drives them,
and [docs/invariants.md](invariants.md) for the commitments underneath —
what is trusted, and why a close can be believed.

## Running it

```bash
cd lang
cargo run --bin prove -- ../hana
cargo run --bin prove -- ../hana --filter two_spellings
```

```
Proving 24 identities...
identity identities::testing_a_test ... ok (the two sides are one diagram)
identity identities::testing_a_test_by_name ... ok (inline; the two sides are one diagram)
identity barista::customer_impl::emit_does_pre_and_post_is_constant ... ok (inline; both: 299 rewrite(s); cases: 1 split(s) (true: 209 rewrite(s); false: 0 rewrite(s)); the two sides are one diagram)
...
identity result: ok. 24 passed; 0 failed; 0 problem(s); 0 filtered out
```

Exit codes: `0` every identity proved, `1` a claim unproved or a hint
orphaned, `2` the corpus would not build or the arguments were wrong.
`--expand` additionally cashes every citation (see below); `--boxes`
chooses how much of a stuck goal is printed (see the failure output,
below).

## The pieces

Four layers, in `lang/rewrite/src/`:

| layer | module | what it does |
|---|---|---|
| proofs | `hant.rs`, `corpus.rs`, `parse.rs` | the strategy language a proof is written in, the loader that attaches each `.hant` entry to the identity it names — ordering them, since `by name` cites another identity and needs it proved first — and the reader that turns a waypoint's text into a term |
| goals | `goal.rs`, `strategy.rs` | a goal is two [graphs](../lang/rewrite/src/graph.rs), lowered and padded to one arity before they build; the interpreter runs a strategy over one |
| engine | `diagram2/` | the literal translation of a term into a graph, the law table (`rules.rs`), the tactic language that drives it (`tactic.rs`, see [docs/tactics.md](tactics.md)), and the listing a stuck graph is read as (`render.rs`) |
| graphs | `graph.rs` | boxes and the links between them, well-formedness, the isomorphism that says two graphs are one diagram, and the rewrite itself — a `Pair` of graphs spliced in at a checked `Match` |

A program in the engine is a **literal** graph: one box per term leaf —
`id`, `swap`, `copy` and `drop` included — and a branch as a `select`
with its arms flattened in front of it. Nothing is
simplified by representation beyond what the wiring cannot say
([docs/rules.md](rules.md) opens with that list); everything else is
simplified by *rewriting*, against the table.

A goal's two sides are padded to one arity exactly once, when the goal is
built: the compiler holds an identity to equal **net** stack change, and
`Goal::aligned` pays that asymmetry by padding the narrower side. Every
downstream question is arity-exact.

## What closes on its own

The `diagram` closer drives the whole table to fixpoint on each side
(the `decide` drive of [docs/tactics.md](tactics.md)) and asks one final
question: are the two graphs **isomorphic** — the same boxes wired alike,
dead slots and id numbers not counting? An identity with no `.hant` entry
gets exactly this, and most of the corpus closes that way; the `.hant`
file holds only the claims that need a human's direction.

Two things the driver deliberately never does: it never opens a call
(`inline` is a proof's decision), and it never reasons by case analysis
on an unknown value (`cases` is a proof's decision). Everything else it
decides by running the table dry.

## The strategy language

A proof is a strategy: steps juxtaposed, manipulations first, a closer
last, written in the `.hant` beside the `.hana` that states the identity:

```text
// identities.hant
proof identities::testing_a_test_by_name = inline diagram;
```

| step | does | fails when |
|---|---|---|
| `lhs(tactic)` / `rhs(tactic)` / `both(tactic)` | runs a [graph tactic](tactics.md) on that side of the goal | the tactic fails — and the residual shows the goal **as it now stands**, the last rewrite that landed still standing |
| `lhs(by name)` / `rhs(by name)` | spends another identity where its left side occurs on this one — a **citation**, carrying that identity's own proof (see below) | the named claim is not proved, its proof is not a run from one side to the other, or its left side does not occur here |
| `inline` | opens every call in both graphs, all the way down | there are no calls |
| `inline(name)` | opens the calls to that one sentence | it is not called here |
| `symm` | swaps the two sides | never — but two in a row are refused |
| `exact` | claims the sides are one diagram — which the auto-close has already checked, so a reached `exact` fails and shows the goal exactly as it stands | always, when reached |
| `via { body } (left: s, right: s)` | **cuts**: `A = B` splits into the goals `A = C` and `C = B`, the waypoint built as a graph | the waypoint's net stack change is not the goal's, or a side fails |
| `cases(op)` | **case analysis** on an intermediate result: an `op` answer is `true` or `false` and nothing else, so everything depending on it becomes a branch holding one copy per case, the assumed answer pasted in as a literal (see below) | no side computes `op`, or nothing depends on its answer |
| `cases(op(lit))` | the same split, with the wire addressed by what it tests: the outermost `op` one of whose operands is the pushed literal `lit` names — by any tail of its spelling, the way `inline` names a sentence | no such test |
| `cases(is_tuple n)` | the same, on the one test that takes an operand: `is_tuple` asks whether a value is a tuple at all, `is_tuple n` whether it is one of exactly that width — two different questions | likewise |
| `cases(op) (true: s, false: s)` | the same split with a sub-strategy per case, each run scoped to its side of the fresh branch (see below) | the split fails, or an arm's tactic does — and the residual names whose case it stood in |
| `diagram` | rewrites both sides by the whole table to fixpoint and asks whether they landed on one diagram | they did not — and the residual is both sides as they stand |

A strategy acts on **one goal**, and the proof mirrors a tree of goals:
the manipulations transform the current goal, the splitter — `via` —
replaces it with independent subgoals each carrying its own strategy
inside the split, and `diagram` closes it. So the closers end a strategy,
and what follows a split is written *inside* it. A goal whose sides
become isomorphic at any point closes on the spot — the second road to a
proof: rewrite a side until the two are one graph. And a step that finds
nothing to do — `inline` with no calls, a `fire` no law matches — fails
loudly rather than becoming a no-op, so a proof that no longer matches
its identity says so.

Which steps carry which weight: `inline` and `cases` **change what is
provable** — the engine treats a call as an opaque box and a computed
value as opaque, and these are the two ways a proof spends what the
driver will not. The tactic steps direct and report: they spend named
laws where the author points them. `via` lets a failure say which half of
a journey it lives in, checked against a named midpoint. `exact` is the
way to *read* a goal: write `proof x = exact;`, look at the goal as built
and aligned, then replace `exact` with the real strategy. `symm` claims
nothing — equality is symmetric — it moves which side the asymmetric
steps read.

An omitted `via` side gets `diagram`: a cut's sides are the author's own
construction, and handing the decision procedure the halves is what a cut
is for.

### The tactic language, in brief

Inside `lhs(…)`, `rhs(…)` and `both(…)` is the rewrite language of
[docs/tactics.md](tactics.md), juxtaposed like steps are: `saturate` (the
structural laws to fixpoint), `saturate(law, …)`, `branches` (the branch
layer with its cleanup), `decide` (the whole table — what `diagram`
drives), `fire(law, …)` (one directed firing), `at(#box, law)` (one
firing at a **named box**), `repeat(…)` and `try(…)`. Laws are named as
[docs/rules.md](rules.md) names them — `copy-elim`, `select-same`,
`dead-node` — and `structural` and `branching` name the two lists.

`at` is the step that answers a report in the report's own words. `fire`
takes the first match it is offered anywhere on the side; when that is
the wrong one, `at(#41, dedup)` names the box the residual listing
printed beside the line, and fires the law in a match that holds *that*
box — anywhere in the match, not only where the law's pattern happens to
anchor. A third field is the direction, `forward` when left out:
`at(#41, select-same, backward)` reads the law's equation right to left,
which is how a proof says "put this back". An id is an exact address and
a brittle one — it means one box of one graph at one moment, so an `at`
is written by reading a report and holds only against the goal that
report described; change a step in front of it and the ids behind it
move. A proof whose named box is gone fails saying so, by name, rather
than firing somewhere else.

## Citing one claim in another

`lhs(by identities::a_lemma)` is how a proof uses a proof: one rewrite by
the claim named, its two sides a pair like the table's own rows, the
match checked like any other.

```text
proof identities::a_double_negative_is_the_branch_it_makes =
    lhs(fire(not-not)) lhs(fire(as-bool-branch));

proof identities::three_negatives_are_a_branch_and_a_negative =
    lhs(by identities::a_double_negative_is_the_branch_it_makes);
```

What a citation does **not** check is whether the claim is true — that
argument is made once, where the claim is. The corpus proves every
identity it states, the citation order is a DAG or the corpus refuses to
run, and a claim that did not close is never citable. A `Proof` holding a
citation therefore stands *given the corpus*, and `Proof::cites` reads
off exactly which claims that is.

Any closed claim may be cited, however it closed. And a citation can be
cashed: `prove --expand` spends every `by` in full — the cited proof's
own steps carried into this goal and re-checked as ordinary rewrites,
with no citation left in the record. Expanding asks more of the cited
proof than citing does: it must be a run from one side of its claim to
the other, and the corpus is held to closing both ways.

## `cases`: proving what depends on a value

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
`true` or it is `false`, and there is no third case, so the goal's
downstream computation equals a branch holding one copy per case with the
assumed answer pasted in as a literal — the `shannon` row of the table
([docs/rules.md](rules.md)). The step fires that row **once** per side
that computes `op`, at the earliest such wire, and that firing is an
ordinary checked rewrite. The power is in what the rest of the table does
*afterwards*, inside the copies, where the assumption is now a literal: a
branch on it resolves (`select-literal`), a test against it computes
(`fold`), untouched code falls away (`dead-node`). When both copies
simplify to the same thing, the introduced branch collapses too (`dedup`,
then `select-same`), and the goal closes by plain rewriting — the case
analysis happened, and every step of it is in the proof's record.

Two practical notes. *Earliest matters*: splitting on a result computed
late says nothing usable about the computations feeding it, so the step
takes the earliest test and leaves later ones to be decided along the
way — or split in turn: `cases(equal) cases(equal)` is a two-variable
case analysis, four leaves, all folded shut by the closing `diagram`.
And *identification comes first*: a program often retests one condition
in several places (through copies, and in both arms of a branch), and the
split only helps once the driver has recognized those as a single wire —
which `both(decide)` does, via `copy-elim` and `dedup` — so `cases`
almost always follows a drive.

The first worked example, the `types_test` contract claim — a case
analysis over the two tags an input might be:

```text
proof types_test::number_does_pre_and_post_is_constant =
    inline both(decide) cases(equal) both(decide) cases(equal) diagram;
```

Open the definitions, drive, split on `equal(x, t1)`, drive, split on
`equal(x, t2)`, and the closer folds every leaf shut.

### Structured `cases`: a sub-proof per case

The structured form carries a sub-strategy per case, in the
parenthesized-arm spelling `via` already uses:

```text
cases(equal) (
    true:  both(decide),
    false: both(decide) cases(is_symbol) (true: both(decide)),
)
```

Each arm's rewrites are scoped to its side of the fresh branch, so this
reads the way a proof assistant's case split does — assume the condition,
prove the case — while what compiles out the other end is ordinary
checked rewriting: the split is the branch itself, "the condition holds
here" is spent by the specializing rows anchored on that branch, and the
checker replays the flat record with no idea a case analysis happened
(see [docs/invariants.md](invariants.md) — the checker has no turnstile,
and only guard-shaped assumptions exist). An arm holds side rewrites and
nested `cases`; either arm is omissible, the goal is closed outside the
split, and a goal side whose branch is already gone skips its arms
quietly. A stuck arm's residual names whose case it stood in.

Two things to know when writing one:

- **An arm can reach upstream.** The arm's scope is its *cone* — shared
  context included — because a split duplicates only what lies downstream
  of its wire, and the tests a nested split must decompose sit upstream,
  shared between the copies.
- **A hypothesis is spent forward only.** The split pastes its literal
  into the readers its wire had at split time. A reader created
  afterwards — say, by `tuple-cancel` taking a shape guard apart inside
  an arm — reads the wire undecided, and the move that decides it is to
  **split again inside the arm**: the new readers are downstream there,
  and the drive dedups the re-test into the old wire.

A hypothesis the goal never computes can still be had: compute the test
and discard it (a backward `dead-node` — computing and discarding is
free, totality and purity footing the bill), then split on it. What
stays out of reach is a fact no test in the language expresses — see
[docs/invariants.md](invariants.md) for that boundary.

The corpus's biggest goal is the worked example.
`barista::customer_impl::emit_does_pre_and_post_is_constant` — the
contract claim over a four-state machine, 351 boxes against 2 once
`inline` has opened it — closes as a decision tree of three hypotheses:

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
splitting there is a fixpoint that decides nothing.
`cases(equal(state::thirsty))` splits the one test `emit` dispatches on,
which the drive has already identified with the precondition
disjunction's own; its false case closes vacuously (the emitted flag is
false, so the postcondition holds whatever the precondition said), and
its true case resolves `emit` outright, leaving the nested `is_symbol`
splits to decide the payload checks — by then the very boxes the
precondition tested, and each created inside the `thirsty` arm, which is
why the splits sit there. The whole tree lands in one flat record per
side, replayed blind by the checker.

## The `.hant` file

One file beside each `.hana` that states identities, holding `proof`
entries in the strategy language above. Attachment is checked both ways:
an entry naming no stated identity is an error — a renamed identity must
not silently shed its proof — and a claim discharged twice was
discharged once too often.

A body — a `via` waypoint — is a **term**, read by
`lang/rewrite/src/parse.rs`, which is the inverse of the term model's own
printing: a waypoint is written `copy(1) ; id(1) * push t1 ; equal`,
in the language the model says rather than in Hana's. Two consequences
worth knowing. Nothing pads — the term language says what it means, so a
body whose halves do not meet is `cannot compose 1 -> 2 with 1 -> 1`
where it is written, rather than something quietly widened. And a call is
named (`call types_test::number`, or any unambiguous tail of that).

## The failure output is the point

A stuck goal prints its **residual**: the two sides as they stand, plus
why the step gave up. That output is the deliverable of a failed run — it
is what says what to try next.

**The graphs are what it shows.** One line per box — its id,
what it reads, what reads it — with a branch written as the block it is:
`if <condition>` where its first arm begins, `else` where the second
does, `endif <condition>` at the `select`, the arms indented between
them. Only the `endif` is a box; the other two lines the listing draws,
which is what their empty id column says. The condition is named on all
three lines, so a block deep in a nest says which wire it turns on. This is what the tactics acted on, so a next step
names the boxes it names — literally, with `at(#41, law)` — and a
`NodeId` is stable for the life of a graph (nodes are only deleted, never
moved), so two reports of one proof compare, which is what watching a
proof means. Four things keep a large listing legible, each stated in
`lang/rewrite/src/diagram2/render.rs`: branch membership is *computed*
(upstream of the select's blocks, less what feeds its condition, less
whatever something outside reads) rather than guessed from what sits
between two lines; the order stays inside a branch once it
enters one; a box that reads nothing is placed just before the box that
reads it, so an operand sits with its `equal`; and `id` and `copy` are
read through, since a `copy` says what the links already say.

The sides are shown as graphs and only as graphs. A graph is a DAG and a
term is a spine, so anything spelling one back out has to reimpose a
stack and pay for it in routing, and a term has no name for a box, so two
reports of one proof could not be compared. `--boxes` is the only dial:
it stops reading through the `id` and `copy` boxes the structural laws
would delete. A `via` answering the report is written by hand off the
boxes the listing names.

## Trust, in one paragraph

`sides` and `apply` are the whole of it — plus the machine itself, where
a law is *about* what an operation computes. Search, drivers, tactics and
the `cases` step's wire-picking are all untrusted: every step they
produce goes through `apply`, a wrong one is refused, and a close is the
isomorphism check on what the checked steps left. A close is also not the
prover's word: a `Proof` carries its full record, and `Prover::prove`
re-checks the whole tree against the goal as stated before answering —
fail closed. [docs/invariants.md](invariants.md) is the full statement.

## What is not here yet

- **The proof object lives in memory only.** Every close carries its full
  record and is re-checked before it is reported — but nothing yet
  *persists* a `Proof` to disk, so re-checking without re-proving means
  serializing the artifact beside the corpus. The shape is ready; the
  file format is not chosen.
- **Reach.** A handful of true equations are not rows yet — commutative
  operand sorting and coercion idempotence among them; the list is in
  [docs/rules.md](rules.md). A claim that needs one fails honestly, and
  the row is a `sides` construction away.
