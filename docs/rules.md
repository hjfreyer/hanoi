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
them, a branch as a `fork`/`select` pair with its arms laid out between the
two ends. The equations below are stated in the term language as
pseudocode, because a linear spelling reads better than a wiring list —
but the graph is what a law actually is, and the term spelling is a
picture of it.

- `;` is composition in program order — the left factor runs first.
- `*` is the tensor: `A * B` is A and B side by side, A on the deeper
  stack region. `dip { A }` is `A * id(1)`.
- `id(n)`, `copy(n)`, `drop(n)`, `swap` — a wire, a fan-out, a discard, a
  crossing.
- `if c { T } else { E }` — a branch. In the graph the condition sits at
  port 0 of both the fork and the select, which is what lets a rule
  anchored at either end *name* it.

Two facts about windows apply to every row. A law is stated in its
minimal window and congruence is free: a match is an embedding, so every
law fires in any context. And a box inside a window may have readers
outside it — several rows below keep a box "for its other readers" for
exactly this reason: the rewrite re-points the readers the window owns and
leaves the box standing for anyone else, and `dead-node` collects it once
nobody is left.

## What needs no rule

The wiring representation already identifies programs up to the
structural theory of sequencing and rearranging, so a whole family of
familiar laws has no row — both sides are literally the same data:

- associativity and units of `;` and `*` — sequencing is one box's output
  wire being another's input; there is no `;` node to re-associate;
- the interchange laws — with no `;` or `*` stored there is nothing to
  interchange;
- everything about `swap` — a crossing is not recorded, so
  `swap ; swap = id(2)`, naturality of the crossing, and the braid
  relation are all one wiring;
- coassociativity and cocommutativity of `copy` — fan-out has no shape.

Don't look for rules for these; there is nothing to fire. Likewise some
facts that look primitive are consequences: `push c ; copy(1) = push c ;
push c` is `dedup` read backward, discarded work vanishes under
`dead-node`, and `branch { A } { A } = drop-top ; A` is `fork-dedup`, then
`select-same`, then `dead-node`.

## The three driven lists

Three lists group the rows a driver can run to fixpoint — every row on
them **shrinks** a graph, which is what makes running dry safe:

| list | rows | what they are |
|---|---|---|
| `structural` | `dead-node`, `id-elim`, `swap-elim`, `copy-elim`, `dedup` | wiring facts — they move boxes without asking what any box computes |
| `branching` | `select-literal`, `select-const`, `select-view`, `select-same`, `fork-hoist`, `fork-dedup`, `specialize-equal`, `specialize-bool`, `specialize-choice` | the branch layer, each row stated at an end of a branch |
| `folding` | `fold`, `tested-bool`, `as-tuple-round-trip`, `retuple`, `is-tuple-built`, `not-not`, `and-literal`, `tuple-cancel`, `as-tuple-built`, `equal-refl` | the value layer — what specific instructions compute, with the machine as the judge |

The `decide` drive — what the `diagram` closer runs — spends all three
lists to fixpoint, with `view-value` held behind everything (see below).
Six rows are on **no** list at all: `view-value`, `promised-bool`,
`shannon`, `select-hoist`, `as-bool-branch` and `coercion-guard`. Each is
held out on purpose, and a proof names the one it wants — `fire(law)`,
`at(#box, law)` — the way it names `inline`.

## Structural laws (`structural`)

| law | statement |
|---|---|
| `id-elim` | `id(n)` is a wire: its readers read what it read. |
| `swap-elim` | a crossing is not recorded: the two lines cross by being re-pointed. |
| `copy-elim` | `copy(n)` is a port read twice. The one structural rule that grows a port's readers; read backward, it is how a copy is introduced. |
| `dead-node` | a box nothing reads is deleted, its input links with it. This is also `drop`-elimination: a `drop(n)` has no outputs, so it is always dead. |
| `dedup` | two boxes of one kind reading one set of sources are one box read twice. Refused on `fork` and `select`: a fork *is* a copy, and merging two would destroy the one fact a fork exists to record — which port is an arm's own view of a value. |

Side conditions are carried by the interface rather than tested:
`dead-node`'s pattern has no boundary outputs, so a match only exists
where every port of the box is unread. Nothing asks "is this dead" — a
match that is not one fails to be a match.

`dead-node` (discarding work) is licensed by totality and purity;
`dedup` (sharing work) by determinism and purity. See
[docs/invariants.md](invariants.md) — these licenses are load-bearing.

## The branch layer (`branching`)

A branch's arms lie *between* its two ends, so a rule's window holds one
end — enough to talk about the condition, which sits at port 0 of both —
or it holds the whole branch, arms carried as payload. The difference
matters: a one-ended window cannot see the **discard** the select
performs, and only the discard makes reasoning from "the condition held"
sound (the untaken arm is an answer nobody reads). So the rules that
reason from the condition — `select-literal` and the three `specialize`
rows — hold the select in their window.

| law | statement |
|---|---|
| `select-literal` | β: `push c ; if { T } else { E }` = the arm `truthy(c)` selects, the whole branch — fork, arms, select — going with it. The arms ride as payload, which keeps the two ends together and puts the discard inside the window. Sound on **every** value, not only bools: `truthy` is total, `false` the one falsy value. |
| `select-const` | a literal condition on a select **no fork pairs with**: the select is the blocks the literal chooses. The fork-less sibling of `select-literal` — with no fork end to strand, no arms need carrying. |
| `select-view` | a select block that is one of the views a fork handed out is the value the fork was handed. This is what makes the rest of the layer reach anything: everything an arm passes through arrives at the select *from behind the fork*, so until this fires, `select-same` and the specializing rows find a view where they need a value. |
| `select-same` | `if c { x } else { x } = x`, one block at a time: a block the select answers with either way is what it answers. The select keeps its other blocks and narrows by one. |
| `fork-hoist` | the same operation done in both arms is one operation done **before** the fork — with its answer still handed to the fork as a stack slot of its own, so the value stays inside the branch and rules anchored at the fork can still name it. |
| `fork-dedup` | the same hoist with the answer read from *outside* the fork — `fork-hoist` and `view-value` spent in one step. The shorter road, and it costs the fork: a branch whose arms all read around it has nothing left reading its views, and the specializing rows lose their anchor. |
| `specialize-equal` | a value that tested `equal` to a literal **is** that literal, in the block the test chose: `equal` answers `Bool(a == b)`, so a truthy answer is `a == b` and nothing weaker. |
| `specialize-bool` | the very value a branch tested, when it is a bool, is what the branch decided: `true` in the then block, `false` in the else block. The window holds the `as_bool` in front of the fork — that coercion's presence is what says the condition is a bool at all (a condition of `5` is truthy, and its then block reads `5`, not `true`). `promised-bool` is the row that puts the coercion there. |
| `specialize-choice` | a branch inside an arm whose condition is a view of the very value the outer branch tested is already decided: its then blocks are read in the outer then arm, its else blocks in the outer else arm — the same value tested twice answers the same. |

The list's order matters to a driver: `select-view` pulls blocks out from
behind a fork, and until it has, most of the layer has nothing to match. A
driver should also prefer `fork-hoist` over `fork-dedup` while it is
holding `view-value` back, and for the same reason: both preserve the
specializing rows' anchor or spend it, and spending it is a last resort.

## The value layer (`folding`)

Laws about what specific instructions compute. The discipline that
governs the whole layer: **facts live on the instruction and are measured
by `vm`, never restated**. `truthy`, `op_arity` and `yields_bool` are read
off the instruction set, and `fold` goes one further — it executes the
literal window on a scratch VM (`run_window`), so there is no second
implementation of the semantics anywhere in the rewriter.

| law | statement |
|---|---|
| `fold` | an operation on literal operands is the answer the machine gives, junk included: `push v̄ ; op` = the pushes of what `vm` answers. The answer side is *built from the run*, so a payload cannot lie about it. |
| `tested-bool` | `op ; is_bool` = `op` and `push true` side by side, for any `op` the instruction set promises answers a bool (`yields_bool`). The answer stays exported for its other readers. |
| `as-tuple-round-trip` | `as_tuple n ; untuple n ; tuple n = as_tuple n`: a value already coerced survives the round trip — the coercion's codomain *is* "a tuple of exactly `n`". Not derivable from `retuple`, which would leave two coercions and no idempotence row to collapse them; listed before `retuple` so the longer window wins. |
| `retuple` | `untuple n ; tuple n = as_tuple n`: rebuilding what `untuple` took apart is the coercion, not the identity — the slots may have been junk-filled. Whole or not at all. |
| `is-tuple-built` | `tuple m ; is_tuple n` = `tuple m ; push (m == n)`: a shape the window watched being built answers a test of that shape. This is the row the `type`/`enum` sugar's guard (`pick 0 ; is_tuple n`) needs. |
| `not-not` | `not ; not = as_bool` — the coercion spelled the long way round. |
| `and-literal` | `and` with a literal operand is decided by `truthy` alone — short-circuiting as an equation. A truthy literal contributes only the coercion: the answer is `as_bool` of the other operand. The one falsy value decides everything: `push false`, the other operand discarded. This is the row that lets a case split spend a **conjunction** one conjunct at a time. |
| `tuple-cancel` | `tuple n ; untuple n = id(n)`: taking apart what `tuple n` built answers the built elements. The tuple is kept for its other readers. |
| `as-tuple-built` | `tuple n ; as_tuple n` answers the tuple itself: the coercion is a no-op on a value the window watched being built. |
| `equal-refl` | `equal` on one wire read twice is `true`: `equal` is structural identity and the language is deterministic and pure. |

## Rows no list drives

Each of these is deliberately on no list; a proof (or a hand-rolled
tactic) names it.

**`view-value`** — a fork's view of a value **is** the value: a view is a
copy, so readers of the view may read the original. Plain wiring, and the
mirror of `copy-elim` through the one copy `copy-elim` leaves alone. What
it spends is not soundness but *information*: which port is an arm's own
view is the fact the specializing rows anchor on, so firing it early
takes their anchor with it. `decide` fires it only when nothing else
fires; a proof can name it sooner.

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

Stated as a composition on purpose: `select(…) ; A` is the side condition
as well as the shape, since composing is the claim that the select's
answers go into `A` and nowhere else — and the interface carries it, by
never exporting the answers. `A` rides as payload. Unlike `shannon`,
nothing is pinned: the condition reaches the moved select untouched, so
this holds of **any** branch, whatever computed its condition. It is the
row that lets a branch grow *forwards* — `fork-hoist` moves work across
the fork in either direction, so a branch could always grow backwards
over what fed it; this is the same freedom at the select. It duplicates
the region it moves over, so no list drives it.

**`as-bool-branch`** — `as_bool` is the branch it is:

```text
as_bool  =  if x { true } else { false }
```

The arms read nothing, so the branch needs no fork. This is the unpacking
that puts a *decision* where a coercion stood: after it, the branch layer
can specialize each arm, and `select-literal` folds the branch away
wherever the condition turns out literal.

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

## Rows not yet written

True of the machine, verified against the junk semantics of
[docs/totality.md](totality.md), but not stated as rows — a claim that
needs one fails honestly, and each is a `sides` construction away:

| law | in terms | why it is true |
|---|---|---|
| commutativity | `swap ; op = op` for commutative `op` | the instruction's own `commutative` fact |
| coercion idempotence | `as_X ; as_X = as_X` | a coerced value is already the shape it coerces to |
| `not-branch` | `not ; if { A } else { B } = if { B } else { A }` | `not v` is truthy iff `v = false`, the unique falsy value |
| `or-literal` | the dual of `and-literal` | short-circuiting for `or` |
| type-test family | `op ; is_int` = `op` and `push false` beside it, for a `yields_bool` op, per (codomain, test) pair | `tested-bool`'s siblings: the other tests of the same codomain fact, table-driven off `Instruction::yields_*` |

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
