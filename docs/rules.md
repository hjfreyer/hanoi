# The rules

A reference for the law table in
[`lang/rewrite/src/diagram2/rules.rs`](../lang/rewrite/src/diagram2/rules.rs).
Every rewrite `bin/prove` makes is an instance of one of these rows: a law
is a pair of open graphs built from a payload (`sides`), and every
application is verified port by port (`apply`) before it lands. This page
says what each row means, which driver list carries it, and how a proof
names it.

Companions: [docs/proving.md](proving.md) is the guide to writing proofs
that spend these laws, [docs/tactics.md](tactics.md) is the language that
drives them, and [docs/invariants.md](invariants.md) holds the commitments
the table is built on — what is trusted, and what licenses the laws that
discard or share work.

## Reading the equations

Programs are graphs: one box per operation, wires carrying values between
them, a branch as a single `select` with its arms laid out in front of
it. The equations below are stated in the term language as
pseudocode, because a linear spelling reads better than a wiring list —
but the graph is what a law actually is, and the term spelling is a
picture of it.

- `;` is composition in program order — the left factor runs first.
- `*` is the tensor: `A * B` is A and B side by side, A on the deeper
  stack region. `dip { A }` is `A * id(1)`.
- `id(n)`, `copy(n)`, `drop(n)`, `swap` — a wire, a fan-out, a discard, a
  crossing. **None of these is a box.** They are how a stack program
  spells things a graph of values says by naming: a fan-out is one source
  named twice, a discard is a source named nowhere, a crossing is two
  names in the other order, and a wire is nothing at all.
- `if c { T } else { E }` — a branch. In the graph that is one `select`
  box: the condition at port 0, then the two blocks. Both arms are handed
  the same sources, so whatever they compute alike they compute *once*.

Two facts about windows apply to every row. A law is stated in its
minimal window and congruence is free: a match is an embedding, so every
law fires in any context. And a box inside a window may have readers
outside it, in any row at all: a rewrite replaces the *value* the window
exports and rebuilds whatever read it, so a reader the window never
mentioned goes on reading the box it always read. Where a proof wants a
row spent for **some** of a value's readers only, it says so on the
step — a stated reader selection (`for`/`except` at the surface) that
re-points exactly the named readers and leaves the rest the box they
have; each named reader is checked to read the very wire the row
leaves, and an unselected reader is no more a loose end than an
unmentioned one.

## What needs no rule

A box is its kind and the sources it reads, and asking for one twice
answers with the one that is already there. So the wiring theory is not a
set of laws that fire — it is a set of things the representation cannot
say:

- associativity and units of `;` and `*` — sequencing is one box's output
  wire being another's input; there is no `;` node to re-associate;
- the interchange laws — with no `;` or `*` stored there is nothing to
  interchange;
- everything about `swap` — a crossing is not recorded, so
  `swap ; swap = id(2)`, naturality of the crossing, and the braid
  relation are all one wiring. What *is* recorded is which operand of a
  box is which, so `swap ; op = op` for a commutative `op` is a row after
  all, and `comm` is it: the equation is about the operand order, not
  about the crossing;
- coassociativity and cocommutativity of `copy` — fan-out has no shape;
- **δ-naturality** — `push c ; copy(1) = push c ; push c` is not a law
  either way round, because both sides are the one box read twice;
- **discarding** — work no boundary output reaches is not in the program,
  so there is nothing to delete;
- **`branch { A } { A } = drop-top ; A`** — the two arms are handed the
  same sources, so they *are* one box, and `select-same` is the whole
  of it.

None of these is a row waiting to be written, and the reason is
stronger than "unnecessary": each is **unstatable**. There is no graph
for either side of `copy-elim` or `dedup` to be, so there is nothing for
a driver to spend and nothing for a proof to name.

## The two driven lists

Two lists group the rows a driver can run to fixpoint:

| list | rows | what they are |
|---|---|---|
| `branching` | `select-literal`, `select-same`, `not-branch`, `specialize-equal`, `specialize-bool`, `specialize-choice` | the branch layer, every row stated at the `select` |
| `folding` | `fold`, `tested-bool`, `as-tuple-round-trip`, `retuple`, `is-tuple-built`, `not-not`, `and-literal`, `or-literal`, `idem`, `tuple-cancel`, `as-tuple-built`, `equal-refl` | the value layer — what specific instructions compute, with the machine as the judge |

The `decide` drive — what the `diagram` closer runs — spends both lists
to fixpoint. Seven rows are on **no** list at all: `promised-bool`,
`shannon`, `select-hoist`, `cond-hoist`, `comm`, `as-bool-branch` and
`coercion-guard`.
Each is held out on purpose, and a proof names the one it wants —
`fire(law)`, `at(#box, law)` — the way it names `inline`.

What holds a row off a list is that a driver could not run it to
fixpoint. Six of the seven **grow** a graph. `comm` does neither: it
permutes, and a driver would exchange the same two operands forever.

## The branch layer (`branching`)

Every row here is stated at the `select`, and there is nowhere else to
state one: a branch is that box, and its arms are ordinary boxes in front
of it. A `select` carries **one answer** — the condition, the two blocks
it chooses between, and nothing else — so a source `branch` leaving `n`
values is `n` of them reading one condition. That is what a branch
*means*: the opaque reading of a graph is a choice per output, so a box
grouping `n` choices carried a width the meaning has no room for, and
two graphs saying one thing could differ in nothing but the grouping.
The width is gone rather than quotiented by a law, and the listing reads
the grouping back off the condition when it draws the brackets. That
placement is also what licenses the rows that reason from the
condition — the **discard** the select performs is what makes "the
condition held" sound in a block (the untaken arm is an answer nobody
reads), and the discard is at the select.

`not-branch` is the one row here that spends no discard: it reads the box
that *made* the condition rather than the blocks, and what it concludes is
about the blocks as a pair. That is why it is also the one that shrinks
without deciding anything.

What a window reaches is therefore a *block*, not the inside of an arm:
the bool a branch turned on becomes `true` where the select reads it,
while the boxes of the then arm go on reading the value itself. Saying
more would mean naming which boxes are an arm's own, and nothing in the
graph records that — an arm is the boxes only that side's blocks read,
which is a fact about the whole graph rather than about a window.

| law | statement |
|---|---|
| `select-literal` | β: `push c ; if { T } else { E }` = the blocks `truthy(c)` chooses. Sound on **every** value, not only bools: `truthy` is total, `false` the one falsy value. The untaken arm is outside the window: its boxes lose their reader when the select goes, and a box the boundary does not reach is not in the program. |
| `select-same` | `if c { x } else { x } = x`: a block the select answers with either way is what it answers, and the select goes with it — a branch answering one thing either way is not a branch. The condition loses its reader and drops out of the program with it. The strategy step of the same name ([docs/proving.md](proving.md)) is this row read as a proof: a goal whose left side answers with a branch becomes one goal per block, and this is what puts them back together. |
| `not-branch` | `not ; if { A } else { B } = if { B } else { A }`: a negation in front of a branch is the branch with its arms exchanged, and the negation is spent. `not v` is truthy exactly where `v` is falsy — `false` being the one falsy value — so the two selects pick opposite blocks of the same pair. Sound on **every** value, for `select-literal`'s reason: truthiness is all a branch reads, and answering it is all `not` does. |
| `specialize-equal` | `select(equal(x, y), y, x) = x`: a branch answering with one operand of its own test where the test held and the other where it did not is answering with the second, whatever the test said. `equal` is structural identity and answers `Bool(a == b)`, so a truthy condition is `x == y` and nothing weaker — where the then block is reached the two operands are one value, and the branch is choosing between a value and itself. The select goes, like `select-same`'s, and the `equal` in a host goes on standing for whatever else reads it. The mirror `select(equal(x, y), x, y) = y` is the same row read with the operands the other way round. Its answer side is bare wiring, which is what lets `on(a b, specialize-equal)` state the branch onto two named wires ([docs/tactics.md](tactics.md)). |
| `specialize-bool` | the very value a branch tested, when it is a bool, is what the branch decided: `true` in the then block, `false` in the else block. The window holds the `as_bool` that made the condition — that coercion's presence is what says the condition is a bool at all (a condition of `5` is truthy, and its then block reads `5`, not `true`). `promised-bool` is the row that puts the coercion there. |
| `specialize-choice` | a branch inside an arm whose condition is the very value the outer branch tested is already decided: its then block is read in the outer then arm, its else block in the outer else arm — the same value tested twice answers the same. The inner select stays; only the outer block that read its answer comes to read the block it would choose. |

Lifting work both arms do out in front is not a row here, and it is not
a rewrite either: both arms are handed the same sources, so the same
work done in both is one box from the moment it is written.

Neither is **merging two branches on one condition**. Peer selects that
turn on one wire are not something a law puts together: they are what a
branch *is*, so `select(C, [T1, T2], [E1, E2])` and the two selects it
used to be are one graph, and the claim closes before any step runs.

## The value layer (`folding`)

Laws about what specific instructions compute. The discipline that
governs the whole layer: **facts live on the instruction and are measured
by `vm`, never restated**. `truthy`, `op_arity`, `yields_bool`,
`commutative` and `idempotent` are read off the instruction set — and the
last three are what let one row stand for a family, since the row asks the
set which instructions it is about rather than listing them. `fold` goes
one further — it executes the
literal window on a scratch VM (`run_window`), so there is no second
implementation of the semantics anywhere in the rewriter.

| law | statement |
|---|---|
| `fold` | an operation on literal operands is the answer the machine gives, junk included: `push v̄ ; op` = the pushes of what `vm` answers. The answer side is *built from the run*, so a payload cannot lie about it. An operation reading **no** operand meets the condition vacuously, so `tuple 0` folds to `push ()` — the one window with nothing in it, and the one that anchors at its own box rather than at a literal behind it. |
| `tested-bool` | `op ; is_T` = `op` and `push (T is Bool)` side by side, for any `op` the instruction set promises answers a bool (`yields_bool`) and any type test `is_T`. One row for the whole family, because one fact answers all of it: a codomain says which test succeeds *and* which fail, and the failures fold a shape guard that asked the wrong question. The rewrite replaces only the test's answer; `op` goes on standing for its other readers. |
| `as-tuple-round-trip` | `as_tuple n ; untuple n ; tuple n = as_tuple n`: a value already coerced survives the round trip — the coercion's codomain *is* "a tuple of exactly `n`". `retuple` and `idem` reach the same place in two steps; listed before `retuple` so the longer window wins in one. |
| `retuple` | `untuple n ; tuple n = as_tuple n`: rebuilding what `untuple` took apart is the coercion, not the identity — the slots may have been junk-filled. Whole or not at all. |
| `is-tuple-built` | `tuple m ; is_tuple n` = `tuple m ; push (m == n)`: a shape the window watched being built answers a test of that shape. This is the row the `type`/`enum` sugar's guard (`pick 0 ; is_tuple n`) needs. |
| `not-not` | `not ; not = as_bool` — the coercion spelled the long way round. |
| `and-literal` | `and` with a literal operand is decided by `truthy` alone — short-circuiting as an equation. A truthy literal contributes only the coercion: the answer is `as_bool` of the other operand. The one falsy value decides everything: `push false`, the other operand discarded. This is the row that lets a case split spend a **conjunction** one conjunct at a time. |
| `or-literal` | the dual of `and-literal`, with the poles exchanged: the one **falsy** value contributes only the coercion — the answer is `as_bool` of the other operand — and a truthy literal decides everything: `push true`, the other operand discarded. This is what lets a case split spend a **disjunction** one disjunct at a time. |
| `idem` | `op ; op = op`, for any `op` the instruction set says is `idempotent`. One row for a family, and the family is the three coercions: a coercion's whole content is its **codomain**, so what it leaves is already of the type it forces. Backwards it is the clone, which is what a proof wants when the shape it is heading for spells the coercion twice. |
| `tuple-cancel` | `tuple n ; untuple n = id(n)`: taking apart what `tuple n` built answers the built elements. The tuple is not part of the equation — a substitution deletes nothing, so one something else reads stays standing. |
| `as-tuple-built` | `tuple n ; as_tuple n` answers the tuple itself: the coercion is a no-op on a value the window watched being built. |
| `equal-refl` | `equal` on one wire read twice is `true`: `equal` is structural identity and the language is deterministic and pure. |

## Rows no list drives

Each of these is deliberately on no list; a proof (or a hand-rolled
tactic) names it.

**`promised-bool`** — `op` = `op ; as_bool` for any `op` the instruction
set promises answers a bool. `as_bool` is `truthy` made into an
instruction, so on a bool it is the identity and the equation is exact.
What it buys: the promise stops being a fact about the instruction set
and becomes a **box**, standing where `specialize-bool` can see it.

**`shannon`** — case analysis as an equation: for a wire `w` the
instruction set promises is a bool,

```text
body(w)  =  if w { body(true) } else { body(false) }
```

The right side runs both pinned copies and keeps one with a select —
sound because operations are total and pure, so the untaken copy is an
answer nobody reads. The region downstream of the wire rides as payload.
Refused on any wire not promised to be a bool: a third case would make
the pin a lie. No driver may loop on this row — the expansion re-creates
the shape it fires on — and the `cases` proof step is what spends it
([docs/proving.md](proving.md)).

**`select-hoist`** — the commuting conversion: what runs *after* a branch
runs inside whichever arm the branch takes,

```text
select(C, T, E) ; A  =  select(C, T ; A, E ; A)
```

Stated as a composition on purpose: the answers are read inside the
window, and what the rewrite replaces is what `A` leaves — an answer
read from outside the carried region keeps the select it always
read. `A` rides as payload. Unlike `shannon`,
nothing is pinned: the condition reaches the moved select untouched, so
this holds of **any** branch, whatever computed its condition. It is the
row that lets a branch grow *forwards*. Backwards is free — work in front
of a branch is shared by both arms as a matter of naming, and doing it
twice is having it once; this is the same freedom at the other end. It duplicates the region it moves over, so no list drives
it. The region rides as payload and *which* region it is, is the
naming strategy's: the `tree` tactic of [docs/tactics.md](tactics.md)
spends this row to a fixpoint over a body that stops at every other
branch, which is what leaves the selects bunched at the output.

**`cond-hoist`** — the same conversion at the one port `select-hoist`
cannot reach without carrying the branch it moves, the **condition**:

```text
select(select(C, T1, E1), T2, E2)
  =  select(C, select(T1, T2, E2), select(E1, T2, E2))
```

A branch whose condition is what another branch answered runs under that
branch instead, once per block it chooses between — and each copy turns
on the block itself, which is the value the inner select was going to
hand over anyway. On a truthy `C` both sides are `select(T1, T2, E2)`
and on a falsy one both are `select(E1, T2, E2)`, which is the whole
proof: nothing is pinned, nothing is promised about any wire, and this
holds of **any** two branches.

The sibling of `select-hoist`, and a **narrower window** than one, which
is why it is a row rather than a payload. `select-hoist` carries a
region, and the region `propose` reads is the select's whole downstream
cone: hoisting past a branch that way copies everything after it as
well. Here there is no payload at all — both selects are one
answer wide, so there is nothing left to say — the window is two boxes,
and what the far side copies is one select and nothing else. It grows a graph all the same, two boxes into three,
so no list drives it. The `tree` tactic of [docs/tactics.md](tactics.md)
spends it after `select-hoist` has nothing left to move, which is what
leaves every condition select-free.

**`comm`** — the other way round is the same answer, for any `op` the
instruction set says is `commutative`:

```text
swap ; op  =  op
```

No `swap` appears in either graph and none could: a crossing is two names
in the other order, so what this equation relates is one box reading
`(a, b)` and one box reading `(b, a)`. That is also why it needs a row
where the wiring laws do not — the operands are *recorded*, so their order
is something the graph says, and only the instruction set can say it does
not matter. The junk answer commutes too, which is what makes the fact
total: `add` on a symbol and an int answers `0` whichever way round they
arrive. Held off every list because it permutes rather than shrinking; the
search also declines it on a box reading one wire twice, which already is
what the other order would build.

**`as-bool-branch`** — `as_bool` is the branch it is:

```text
as_bool  =  if x { true } else { false }
```

The arms read nothing, so the branch is the select and the two literals.
This is the unpacking that puts a *decision* where a coercion stood:
after it, the branch layer can specialize each arm, and `select-literal`
folds the branch away wherever the condition turns out literal.

**`coercion-guard`** — a coercion is a guarded identity, which is the
instruction set's own sentence about all three of them:

```text
as_T  =  if x is a T { x } else { junk }
```

| coercion | guard | junk |
|---|---|---|
| `as_bool` | `is_bool` | `true` — every non-bool is truthy |
| `as_int` | `is_int` | `0` |
| `as_tuple n` | `is_tuple n` | a tuple of `n` empty tuples |

The width in the tuple guard is part of the type: a tuple of the wrong
length is exactly what `untuple n` could not take apart, and the
width-blind `is_tuple` would claim `as_tuple 2` is the identity on
`(1, 2, 3)`.

The two unpackings — `as-bool-branch` and `coercion-guard` — buy the
direction of reading the rest of the table cannot go: a coercion is
opaque to every rule that asks what a value *is*, and they put the test
that decides it into the graph, where the branch layer and a `cases`
split can spend it. Both grow a graph, and whether to unpack is a
decision of the same kind `inline` is — so a strategy says which one, and
where.

## Rows that were not written

The table above used to end in a list of true equations that were not rows
— held against the junk semantics of [docs/totality.md](totality.md),
spendable by nothing, so a claim that needed one failed honestly. The list
is empty, and where each of them landed is worth saying, because three of
the five landed as *one* row rather than as the family they were described
as:

| was listed as | landed as |
|---|---|
| commutativity | `comm`, one row over the instruction set's own `commutative` fact |
| coercion idempotence | `idem`, one row over a new `idempotent` fact, measured by `vm` the way `commutative` is |
| `not-branch` | a row of its own, in the branch layer |
| `or-literal` | a row of its own, beside `and-literal` |
| type-test family | `tested-bool`, which now carries *which* test and decides it — the family is the one row, not a row per (codomain, test) pair |

The shape of the trade is the same in all three of the general ones: the
fact lives on the instruction, `vm` measures it, and the row reads it. A
row per coercion, or per commutative operator, or per (codomain, test)
pair, would be several copies of one sentence and another to write
whenever the instruction set grew a member.

One equation named in this document is still not a row: `as_bool ; branch`
is `branch`, the coercion a branch already applies to its condition
([docs/totality.md](totality.md)). It is true, and it is not needed yet —
`promised-bool` puts the coercion there on purpose, and
`specialize-bool` is what reads it.

## Further reading

- Fox, *Coalgebras and cartesian categories* (1976); Lafont, *Towards an
  algebraic theory of Boolean circuits* (2003) — the cartesian PROP the
  wiring representation embodies, and why the copy/drop/swap fragment
  needs no rules.
- Bonchi–Sobociński–Zanasi, the *String Diagram Rewrite Theory* series —
  laws as pairs of open graphs, rewriting as checked cut-and-splice; the
  road this table walks.
- Altenkirch–Dybjer–Hofmann–Scott, *Normalization by evaluation for typed
  lambda calculus with coproducts* (2001) — why the branch fragment is
  the hard one, and the shape of its decision procedure.
- Kozen–Smith, *Kleene algebra with tests* (1996) and the hypothesis-
  elimination line after it — why guard-shaped assumptions compile into
  branches and arbitrary ones cannot; the boundary
  [docs/proving.md](proving.md)'s `cases` step lives inside.
