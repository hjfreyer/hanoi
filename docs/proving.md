# Proving identities

`bin/prove` discharges the claims `identity A = B;` states. Both sides of
a goal build into literal graphs, a driver spends the law table on each
until nothing more fires, and either they land on one diagram —
isomorphic — or they do not. Every step on the way is an instance of a
named law, verified before it lands, so a close is a derivation's worth
of checked rewrites and one final isomorphism rather than any engine's
word. What a written proof directs is the handful of moves the driver
does not make on its own today — opening a call, and splitting a
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
cargo run --bin prove -- ../hana --color | less -R
```

```
Proving 25 identities...
identity identities::testing_a_test ... ok (the two sides are one diagram)
identity identities::testing_a_test_by_name ... ok (inline; the two sides are one diagram)
identity barista::customer_impl::emit_does_pre_and_post_is_constant ... ok (inline; both: 5 rewrite(s); cases: 3 expansion step(s) (true: both: 30 rewrite(s); cases: 3 expansion step(s) (...); false: the two sides are one diagram))
...
identity result: ok. 25 passed; 0 failed; 0 problem(s); 0 filtered out
```

Exit codes: `0` every identity proved, `1` a claim unproved or a hint
orphaned, `2` the corpus would not build or the arguments were wrong.

A stuck goal's residual emphasises the telling prefix of each address in
bold, which only a terminal shows: piped, the escapes would land in a log
as themselves, so the default is plain, and `NO_COLOR` keeps it plain on a
terminal too. `--color` emphasises regardless — a pager reads escapes as
well as a terminal does, and nothing but the reader can tell that pipe
from a log file, so `--color | less -R` is how a long residual is read.

## The pieces

Four layers, in `lang/rewrite/src/`. The line between the first two and
the last two is the **trust boundary**: everything under `kernel/` is
what a proof's truth rests on, so a bug there could let a false identity
through; everything outside it only ever finds a step, and a bug there
produces a step the kernel refuses or a proof that fails to check.

| layer | module | what it does |
|---|---|---|
| proofs | `hant.rs`, `corpus.rs`, `parse.rs` | the strategy language a proof is written in, the loader that attaches each `.hant` entry to the identity it names — ordering them, since `by name` cites another identity and needs it proved first — and the reader that turns a waypoint's text into a term |
| driving | `strategy.rs`, `proof.rs`, `tactic.rs`, `query.rs`, `render.rs` | the interpreter that runs a strategy over a goal and writes a *draft* of the proof; `flatten`, which reads the one run the kernel is handed off that draft; the tactic language that drives the table (see [docs/tactics.md](tactics.md)); the queries a tactic points with; and the listing a stuck graph is read as |
| kernel | `kernel/goal.rs`, `kernel/mod.rs`, `kernel/rules.rs` | a goal is two [graphs](../lang/rewrite/src/kernel/graph.rs), lowered and padded to one arity before they build, and `certify` is the one judgement of a proof: a flat run of steps, replayed on the left side, lands on the right; `mod.rs` is the literal translation of a term into a graph; `rules.rs` is the law table, and `apply` the one way a graph is rewritten |
| graphs | `kernel/graph.rs`, `kernel/term.rs` | boxes and the links between them, well-formedness, the isomorphism that says two graphs are one diagram, and the rewrite itself — a `Pair` of graphs spliced in at a checked `Match`; and the term model a claim is stated over |

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

Two things the driver does not do today: it does not open a call
(`inline` is a proof's decision), and it does not reason by case analysis
on an unknown value (`cases` is a proof's decision). Everything else it
decides by running the table dry. Neither is a limit on what a driver may
do — it lands only checked steps either way — so much as a choice about
how much of a proof is written down.

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
| `select-same (then: s, else: s)` | **splits a branch**: the left side answers with a `select`, so `select(c, T, E) = B` becomes the goals `T = B` and `E = B` (see below) | the left side's answer is not one `select`, or a block fails |
| `cases(#nk) (true: s, false: s)` | **case analysis**, which is η on a wire and then `select-same`: the box is named by [address](tactics.md), the instruction set promises its answer is `true` or `false` and nothing else, so the left side's downstream becomes a branch holding one copy per case with the assumed answer pasted in as a literal — and that branch is then split into the two goals (see below) | the left side does not name that box, nothing promises its answer is a bool, nothing depends on it, or a case fails — and the residual says which |
| `cases-equal(#nk) (true: s, false: s)` | the same on an `equal`, with the **substitution** the true case licenses: every other reader of the deep operand comes to read the top one there (see below) | the box is no `equal`, nothing but the test reads its deep operand, or the split fails |
| `by-cases` / `by-cases(n)` | the same tree **searched for**: `diagram`, and where that stops a split on a wire the goal's own tests offer, and the same again on each case. `n` is the whole search's budget of splits, 32 by default (see below) | nothing is left to split on, a case fails, or the budget runs out — and the residual names the case it stopped in |
| `diagram` | rewrites both sides by the whole table to fixpoint and asks whether they landed on one diagram | they did not — and the residual is both sides as they stand |

A strategy acts on **one goal**, and the proof mirrors a tree of goals:
the manipulations transform the current goal, a splitter — `via`,
`select-same`, `cases` — replaces it with independent subgoals each
carrying its own strategy inside the split, and `diagram` closes it. So the closers end a strategy,
and what follows a split is written *inside* it. A goal whose sides
become isomorphic at any point closes on the spot — the second road to a
proof: rewrite a side until the two are one graph. And a step that finds
nothing to do — `inline` with no calls, a `fire` no law matches — fails
loudly rather than becoming a no-op, so a proof that no longer matches
its identity says so.

Which steps carry which weight: `inline` and `cases` (and the `by-cases`
that searches for one) **change what is provable** — the engine treats a call as an opaque box and a computed
value as opaque, and these are the two ways a proof spends what the
driver will not. The tactic steps direct and report: they spend named
laws where the author points them. `via` lets a failure say which half of
a journey it lives in, checked against a named midpoint, and
`select-same` lets it say which block of a branch. `exact` is the
way to *read* a goal: write `proof x = exact;`, look at the goal as built
and aligned, then replace `exact` with the real strategy. `symm` claims
nothing — equality is symmetric — it moves which side the asymmetric
steps read.

An omitted `via` side gets `diagram`: a cut's sides are the author's own
construction, and handing the decision procedure the halves is what a cut
is for. An omitted `select-same` block gets `diagram` for the same
reason, and a block that is already the right side closes before any step
runs, so its arm is usually left out.

## `select-same`: proving a branch block by block

A goal whose left side **answers with a branch** — every one of its
boundary outputs an output of one `select`, which is what "the last box
is a `select`" means — is a goal about two programs at once, and
`select-same` is how a proof says so:

```text
proof identities::a_branch_whose_blocks_agree =
    select-same (then: lhs(fire(as-bool-branch)));
```

`select(c, T, E) = B` becomes `T = B` and `E = B`, each an independent
goal under its own strategy. What licenses putting them back together is
the law the step is named for ([docs/rules.md](rules.md)): a branch both
of whose blocks are `B` *is* `B`, and the condition goes with the branch,
discarded the way every untaken arm is. Carving a block out deletes
nothing — the block's goal is the same graph closed on that block's
sources, so the condition and the other block become boxes no output
reaches.

It is half of `cases`. `cases` **makes** the branch first — that is the
η — and then does exactly this to it; `select-same` **spends** a branch
the goal already has. Either way a proof stops having to find one
rewriting that suits both blocks and can name a step at the block that
wants it. A block failing says which block it was, and shows that
block against the right side rather than the branch it came out of.

Two things to know. It reads the **left** side, and `symm` is how a proof
says the branch is on the other one. And a side answering with a branch
*and something else besides* is two answers rather than one, which the
law has nothing to say about: the step refuses it rather than guessing.

### The tactic language, in brief

Inside `lhs(…)`, `rhs(…)` and `both(…)` is the rewrite language of
[docs/tactics.md](tactics.md), juxtaposed like steps are: `saturate(law,
…)` (those laws to fixpoint), `branches` (the branch layer), `decide`
(the whole table — what `diagram` drives), `tree` (`select-hoist` past
everything but another branch and `cond-hoist` out of every condition,
until the selects are all at the output and no condition holds one),
`fire(law, …)` (one directed firing), `at(#box, law)` (one firing at a
**named box**), `on(#wire …, law)` (a law stated onto **named wires** —
the introduction no search anchors, `on(in0 in1, tuple-cancel)` putting
the cancelling pair in), `repeat(…)` and `try(…)`. Laws are named as
[docs/rules.md](rules.md) names them — `fold`, `select-same`, `not-not`
— and `branching` names the list. Wherever commas separate — a law list, an
`at`'s or an `on`'s fields, the sides of a `via` or a `cases` — the last
one is optional, so a list written down the page gains a line without
touching the one above it.

Tactics are juxtaposed, and no tactics is a run of none: `lhs()` leaves
its side exactly as it stands, as do `repeat()` and `try()`, and an empty
strategy — `proof p = ;`, or an arm written empty — runs nothing and
closes only if the goal's sides are already one diagram. That is what a
proof has while what it is going to say is commented out. A missing
argument is not a run of none, and stays an error: `fire()` names no law,
`inline()` no sentence, `for()` no reader.

`at` is the step that answers a report in the report's own words. `fire`
takes the first match it is offered anywhere on the side; when that is
the wrong one, `at(#nkz, fold)` names the box the residual listing
printed beside the line, and fires the law in a match that holds *that*
box — anywhere in the match, not only where the law's pattern happens to
anchor. A third field is the direction, `forward` when left out:
`at(#nkz, select-same, backward)` reads the law's equation right to
left, which is how a proof says "put this back".

A rewrite ordinarily re-points **every** reader of what its window
leaves. Where a proof wants only some of them, a `for(…)` or
`except(…)` clause on an `at` or an `on` names the readers that follow
the law — or all but them — a box by address, `outN` for a boundary
output: `on(in0, tuple-cancel, for(out1))` sends one reading of a
shared wire through the pair and leaves the other on the wire. Each
named reader must actually read a wire the law leaves, or the step
fails naming it; the choice is resolved when the step fires and
recorded in the match, so — like a `cases` split — it covers the
readers the wire has then, not ones a later step creates.

**A box's name is what it computes** — a digest of its kind and of the
names of what it reads, written in twelve letters and printed by the
listing beside every line, the way Jujutsu writes a change id. A proof
writes as much of one as tells that box from the others on the page,
which is exactly the part the listing prints in bold and the part it
prints wherever one box refers to another: two or three letters, in
practice. Because the name is a fact about the computation rather than
about the graph holding it, it means the same box on both sides of the
goal and in the goal the next step leaves — what it does not survive is
a rewrite underneath it, since a value made of different values is a
different value. A proof whose named box is gone fails saying so, by
name, rather than firing somewhere else; so does one whose prefix has
come to mean two boxes, and it says which two.

## Citing one claim in another

`lhs(by identities::a_lemma)` is how a proof uses a proof: the claim
named has a certified run of its own — the steps that take its left side
onto its right — and a `by` carries that run in, re-applied through the
embedding of the claim's left side where it occurs here.

```text
proof identities::a_double_negative_is_the_branch_it_makes =
    lhs(fire(not-not)) lhs(fire(as-bool-branch));

proof identities::three_negatives_are_a_branch_and_a_negative =
    lhs(by identities::a_double_negative_is_the_branch_it_makes);
```

What lands is a run of ordinary rewrites, and the kernel cannot tell a
`by` from a `lhs(…)` that spent the same steps: nothing is taken on the
corpus's word, and what a citation *means* is what every use pays for.
What a citation needs of the corpus is order — the claim has to be proved
before this one, which the corpus arranges, and two claims that lean on
each other are refused by name. Any closed claim may be cited, however it
closed: every close is a flat run by the time it is certified.

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

`cases(#nk) (true: …, false: …)` is one composite, and saying it as the
composite is the shortest true description: **η on a wire, and then
`select-same` on the branch that makes.**

It picks the wire by naming the box that answers with it, in the same
[addresses](tactics.md) an `at` and an `on` are written in: as much of
the box's name as tells it from the others on the page, which is what a
residual listing prints in bold on its line. The box has to be one the
instruction set guarantees answers a boolean (`equal`, `is_int`, `not`,
…); the kernel is what asks, at the wire rather than at a spelling, and a
box nothing promises a bool of simply offers no second case.

That answer is `true` or it is `false`, and there is no third case, so
the left side's downstream computation equals a branch holding one copy
per case with the assumed answer pasted in as a literal. That is not a
row of its own: it is three rows of the table spent in order —
`promised-bool`, `as-bool-branch` and `select-hoist`
([docs/rules.md](rules.md)) — each an ordinary checked rewrite. Then the
branch is split the way `select-same` splits one a goal already had:
`select(w, T, E) = B` becomes the goals `T = B` and `E = B`, each on its
own road, and the law of that name puts them back together.

So the hypothesis is never a context the checker has to know about. It is
the **block** each case stands in, with the literal pasted into it — and
inside that block the rest of the table does the work: a branch on the
assumption resolves (`select-literal`), a test against it computes
(`fold`), untouched code falls away by not being reached. The checker
replays a flat record and has no idea a case analysis happened (see
[docs/invariants.md](invariants.md) — it has no turnstile, and only
guard-shaped assumptions exist).

Being a splitter has the consequences every splitter has. `cases` **ends
a strategy**: the cases are written inside it, each is a whole strategy —
closers, cuts, `symm`, nested splits and all — and an omitted one gets
the default, `diagram`. A case that fails says which case it was, and
shows that block against the right side rather than the branch it came
out of.

Three practical notes.

*It is the left side that expands*, because the left side is where the
blocks are carved — `select-same`'s rule, inherited whole. A wire only
the right side computes is a `symm` away, and the report says so rather
than leaving you to guess.

*What each case is proved against is the whole right side*, untouched. So
the reach of the step is: goals whose right side does not itself turn on
the wire. Where it does, neither case is true on its own and the split is
the wrong instrument — `specialize-bool` and its neighbours in the branch
layer are the rows for a right side that tests what the left tests.

And *identification is free*: a program often retests one condition in
several places, and the split only helps once those are recognized as a
single wire. They are, from the moment the graph is written — a box is
its kind and what it reads, so two spellings of one test are one box, and
one address. `cases` still usually follows a drive, for the ordinary
reason: the wire it wants may only appear once a branch has folded — and
for a second reason now, that the address is read off the goal *as the
drive leaves it*.

Which is how a split is written at all: reach the point the split belongs
at, put an `exact` there, and read the wire's name off the listing the
failure prints. A rewrite **under** a box renames it — a value made of
different values is a different value — so an address is good exactly as
long as the steps in front of it leave its box computing what it
computed, and a name that has gone stale fails loudly rather than
splitting somewhere else.

The first worked example, the `types_test` contract claim — a case
analysis over the two tags an input might be:

```text
proof types_test::number_does_pre_and_post_is_constant =
    inline both(decide)
    cases(#zl) (
        true: diagram,
        false: both(decide) cases(#y) (true: diagram, false: diagram));
```

Open the definitions, drive, split on `#zl` — which is `equal(x, t1)`.
Its true case folds shut on the machine outright. Its false case is where
the second tag is still open, so the second split lives there: drive
again, split on `#y`, which is `equal(x, t2)`, and both leaves fold. The
goal holds four `equal`s, and which of them each split means is not
something the shape of the step could decide: the outermost is the
postcondition's own tuple guard, and splitting there decides nothing.

### `cases-equal`: the substitution a test licenses

Where a test held, the two things it compared **are one value**, and the
code in that case can be read with either. Nothing in the table says so
where you want it said: the specializing rows are stated at a select and
reach a *block*, not the inside of an arm ([docs/rules.md](rules.md)),
because a branch's arms are the boxes only that side's blocks reach — a
fact about the whole graph rather than about a window.

`cases-equal` is the way to have it anyway, and it needs no new law.
Before the η it **states** `specialize-equal` onto the test's two
operands:

```text
on(a b, specialize-equal, except(#test))
```

which puts `select(equal(a, b), b, a)` into the graph and sends every
reader of `a` through it — every one but the test itself, which reads `a`
too, and a test reading the branch that turns on it would be a box
reaching itself. That claims nothing at all: `select(equal(a, b), b, a)`
is `a` on any wires whatever, which is exactly why the row has a bare
side to state ([docs/tactics.md](tactics.md)).

The introduced branch turns on the very wire about to be split, so the η
decides it along with everything else downstream: `b` in the true case,
`a` in the false one. Which is the substitution — the true case now reads
the value it was tested against, and the false case is untouched, as it
must be, since all it knows is that the two differ.

Which operand goes which way is the graph's own record and not a choice:
readers of the **deep** operand come to read the top one. A test is
written `value push lit equal`, so that is the useful direction — the
computed wire specialized to the literal it was compared against.

The corpus's example is the smallest claim that needs it:

```text
identity a_tested_value_is_what_it_was_tested_against
    { pick 0 push 7 equal branch { push 1 add } { drop 0 push 8 } }
  = { drop 0 push 8 };

proof identities::a_tested_value_is_what_it_was_tested_against =
    cases-equal(#t) (true: diagram, false: diagram);
```

Plain `cases` gets as far as `x + 1` against `8` in the true case and
stops, with nothing to say that `x` is `7` there. `cases-equal` closes
it, and the record the checker replays is a stated row and a case
analysis with no idea either was about the other.

### The decision tree

Because a case is a whole strategy, a case may split again — which is how
a proof writes a decision tree, and the nesting says *where* each
hypothesis is spent:

```text
cases(#nk) (
    true:  diagram,
    false: both(decide) cases(#zy) (true: diagram, false: diagram),
)
```

Two things to know when writing one:

- **A hypothesis is spent forward only.** The split pastes its literal
  into the readers its wire had at split time. A reader created
  afterwards — say, by `tuple-cancel` taking a shape guard apart inside a
  case — reads the wire undecided, and the move that decides it is to
  **split again inside that case**: the new readers are downstream there,
  and a re-test of the old wire *is* the old wire. What the nesting says
  is where the hypothesis is spent, not which wire is meant — the address
  says that, and says it the same inside a case as out.
- **The blocks share their context.** Carving a block out deletes
  nothing: the case's goal is the same graph closed on that block's
  sources, so a nested split can name a box upstream of the branch, where
  the two copies still share what they read.

A hypothesis the goal never computes can still be had: compute the test
— an unread box costs nothing, totality and purity footing the bill —
and split on it. What stays out of reach is a fact no test in the
language expresses — see [docs/invariants.md](invariants.md) for that
boundary.

The corpus's biggest goal is the worked example.
`barista::customer_impl::emit_does_pre_and_post_is_constant` — the
contract claim over a four-state machine, 351 boxes against 2 once
`inline` has opened it — closes as a decision tree of three hypotheses.
Written out, it is this:

```text
inline both(decide)
cases(#uk) (
    true: both(decide) cases(#lq) (
        true: both(decide) cases(#oz) (true: diagram, false: diagram),
        false: diagram),
    false: diagram)
```

The addressing is what makes it writable at all: the goal holds two dozen
`equal`s, and which one a split means is not something the shape of a step
could decide. `#uk` is the one test `emit` dispatches on,
`equal(x.2, state::thirsty)`, which the drive has already identified with
the precondition disjunction's own. Its false case closes outright — the
emitted flag is false, so the postcondition holds whatever the
precondition said. Its true case resolves `emit`, and the two `is_symbol`
splits — `#lq`, then `#oz` inside its true case — decide the payload
checks, which are by then the very boxes the precondition tested. Every
leaf is a bare `diagram`, and the whole tree lands in one flat record,
replayed blind by the checker.

The corpus does not write that out any more; it says `inline by-cases`
and lets the search find a tree of its own (below). Reading this one is
still how you learn what the search is looking for — and how you write the
next one it cannot find.

## `by-cases`: the tree, searched for

A decision tree is a shape, and finding it is a search — so the corpus
does not write barista's out. `by-cases` is the whole of that proof, and
the tree it finds is not quite the one above: it takes the tuple guard
first, then spends `cases-equal` on the state test, and the substitution
that buys leaves one `is_symbol` split to do rather than two.

```text
proof barista::customer_impl::emit_does_pre_and_post_is_constant =
    inline by-cases;
```

What it does on each goal it reaches is `diagram`, and where that stops, a
split, and then the same again on each case. What it splits on is the
heuristic, and it is three questions asked in turn of every live box the
instruction set promises answers a bool and something reads:

- **Is it primitive?** A test no other candidate feeds beats one built out
  of others. Deciding `and(a, b)` says nothing about `a` or `b`, while
  deciding both of those decides the `and` — and a split on a derived test
  is exactly how a search paints itself into a case that is no longer
  true. (A split is *sufficient*, not necessary: each case has to be true
  on its own, and a badly chosen wire makes a case that is not.)
- **Does a branch turn on it?** Among equals, a wire the goal already
  branches on, since deciding it resolves that branch outright rather than
  only feeding the rows below.
- **How far upstream is it?** Then the outermost, which is the goal's own
  first decision.

It spends `cases-equal` wherever the substitution has something to say and
`cases` otherwise, so an author gets it without asking.

**Termination** is an argument, not a theorem, which is why there is a
budget. The argument: the η pastes its literal into every reader the wire
had, so in each case nothing reads that box any more and it leaves the
candidate set — while every box a split leaves was already there or is a
copy of one, so nothing new enters. The set shrinks by at least one per
split and a goal has finitely many boxes. What the argument does not cover
is the drive between splits, which is free to reshape the goal. So
`by-cases` spends at most 32 splits over the whole search, `by-cases(n)`
as many as you say, and running out is a failure like any other.

Two things it will not do. It will not `inline` — that changes what is
provable, and opening a definition is a proof's decision, which is why the
barista proof still says so. And it only ever splits the **left** side, so
a goal whose right side turns on the wire is out of its reach exactly as
it is out of `cases`'s.

What it leaves is what a written tree leaves, step for step: the same
proof object, the same flat record, the same blind replay. A search that
answers wrong is a proof the kernel refuses, never a wrong graph — which
is what makes searching admissible here at all.

## The `.hant` file

One file beside each `.hana` that states identities, holding `proof`
entries in the strategy language above. Attachment is checked both ways:
an entry naming no stated identity is an error — a renamed identity would
otherwise silently shed its proof — and a claim discharged twice was
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

**The graphs are what it shows.** One line per box — its address,
what it reads, what reads it — with a branch written as the block it is:
`if <condition>` where its first arm begins, `else` where the second
does, `endif <condition>` at the `select`, the arms indented between
them. Only the `endif` is a box; the other two lines the listing draws,
which is what their empty name column says. The condition is named on all
three lines, so a block deep in a nest says which wire it turns on. This is what the tactics acted on, so a next step
names the boxes it names — literally, with `at(#nkz, law)` — and a box
is named by what it computes, so two reports of one proof compare, which is what watching a
proof means. On a terminal each line's address is printed with its
shortest telling prefix in bold, and every reference to a box is that
prefix; a piped run gets the letters and no escapes. Three things keep a large listing legible, each stated in
`lang/rewrite/src/render.rs`: branch membership is *computed*
(upstream of the select's blocks, less what feeds its condition, less
whatever something outside reads) rather than guessed from what sits
between two lines; the order stays inside a branch once it
enters one; a box that reads nothing is placed just before the box that
reads it, so an operand sits with its `equal`.

The sides are shown as graphs and only as graphs. A graph is a DAG and a
term is a spine, so anything spelling one back out has to reimpose a
stack and pay for it in routing, and a term has no name for a box, so two
reports of one proof could not be compared. Every box the boundary
reaches is listed — every box is an operation, so there is nothing a
reader would rather look through. A `via` answering the report is
written by hand off the boxes the listing names.

## Trust, in one paragraph

`sides`, `apply` and `certify` are the whole of it — plus the machine
itself, where a law is *about* what an operation computes. Search,
drivers, tactics, the address a `cases` names its wire by and the shape of the
argument itself are all untrusted: a strategy writes a *draft* — the tree
of goals it carved and the steps each spent — and `flatten` turns the
draft into one flat run of steps from the goal's left side to its right,
which is the only thing the kernel is handed. `certify` replays that run
through `apply`, a wrong step is refused, and the close is the
isomorphism check on what the replayed steps left. A draft that does not
flatten, or a run that does not land, comes back stuck as the prover bug
it is — fail closed. [docs/invariants.md](invariants.md) is the full
statement.

## What is not here yet

- **The run lives in memory only.** Every close is a flat list of steps
  the kernel certified before it was reported — but nothing yet
  *persists* a run to disk, so re-checking without re-proving means
  serializing the list beside the corpus. The shape is ready; the file
  format is not chosen.
- **Reach.** The list of true equations that were not rows yet — commutative
  operand sorting and coercion idempotence among them — is empty:
  [docs/rules.md](rules.md) says where each landed. A claim that needs a
  row the table still lacks fails honestly, and the row is a `sides`
  construction away.
