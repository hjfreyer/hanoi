# The algebra of programs

A reference sheet for the equational theory the prover works in: every
structural law stated symbolically and in the term model's spelling, with its
side conditions, how the machinery embodies it, and what is known about
completeness. The engine is `rewrite/src/diagram2` now — the literal graph
and its law table — and where this page's **How** column says a law held by
representation or by a fold, that reading described the retired
canonicalizing engine (`diagram.rs`); today every non-representational
reading is a *row* of `diagram2/rules.rs`, fired by a driver and checked
per application. [docs/proving.md](proving.md) describes
the machinery; this page is the laws themselves, and the map to the
literature they come from.

The organizing fact: the copy/drop/swap/frame fragment of this language is the
standard finite presentation of the **free cartesian PROP** — the categorical
structure singled out by Fox's theorem — and the branch fragment is the
equational theory of **sum types**. The first has a complete, known axiom set
and a decision procedure; the second is decidable but genuinely hard. The
engine takes both as far as they go without search: the whole first layer is
*representation* (programs are stored as wiring, where these laws have no
spelling), the second is canonicalized into ordered case trees, and every
identity in the corpus closes on that alone — the case split that used to be
a page of hand-written cuts included.

## Conventions

- `;` is composition in program order — the left factor runs first. `*` is
  the tensor, and in `W * X` the **deeper** stack region is on the left, so
  `dip { A }` is `A * id(1)`. Both are the term model's own operators
  (`rewrite/src/term.rs`); objects are stack widths, so on objects `*` is
  `+`.
- Generators: `copy(1) : 1 → 2` (δ, the fresh copy lands on top), `drop(1) :
  1 → 0` (ε), `swap : 2 → 2` (σ). The block forms `copy(n)`, `drop(n)`,
  `id(n)` are their own leaves.
- Every law is stated in its minimal window; congruence embeds it in any
  context.
- **How** column: what made the law hold in the retired canonicalizing
  engine, kept as a map of *kinds* of law. *representation* — the two sides
  were literally the same data (today: the structural rows of
  `diagram2/rules.rs`, spent by rewriting); *fold* — a bounded, confluent
  canonicalization (today: the value rows — `fold`, `tested-bool`,
  `retuple`); *order* — the case-tree discipline (today: the branch layer,
  plus the `cases` proof step for η); *boundary* — true but beyond any
  automatic reading, waiting on a step that spends it; *candidate* — true
  and useful but not yet a row.

## Layer 1: the cartesian core

The structural laws — everything about copying, discarding and rearranging,
with the signature's instructions opaque. This layer has a known complete
presentation: symmetric monoidal structure, a cocommutative comonoid on the
generating object, and naturality of δ and ε (Fox 1976; Lafont 2003 is the
copy-paste-friendly catalogue).

| law | symbolic | in terms | how |
|---|---|---|---|
| associativity of `;` | `(a;b);c = a;(b;c)` | as written | representation — `;` is not stored; sequencing is one box's output wire being another's input |
| associativity of `*` | `(a*b)*c = a*(b*c)` | as written | representation — `*` is not stored; side-by-side is boxes sharing no wires |
| units of `;` | `id ; a = a = a ; id` | `id(n)` of the right width | representation — `id` is a wire passing through, with no node |
| unit of `*` | `id₀ * a = a = a * id₀` | width-0 leaf | representation |
| id blocks fuse | `id(n) * id(m) = id(n+m)` | | representation |
| degenerate blocks | `copy(0) = drop(0) = id(0)` | | representation — all three are no wires at all |
| interchange, both forms | `a * b = (a * id) ; (id * b)`; `(a;c) * (b;d) = (a*b) ; (c*d)` | | representation — with no `;` or `*` stored there is nothing to interchange |
| producer beside a computation | `a ; (id(a.out) * b) = a * b` for `b : 0 → m` | | representation |
| symmetry involutive | `σ ; σ = id₂` | `swap ; swap = id(2)` | representation — a crossing is not recorded |
| naturality of σ | `(a*b) ; σ = σ ; (b*a)` | legs `1 → 1` | representation |
| σ past a dropping leg | `swap ; (id(1)*drop(1)) = drop(1)*id(1)`, and mirror | | representation |
| coassociativity | `δ;(id⊗δ) = δ;(δ⊗id)` | `copy(1) ; id(1)*copy(1) = copy(1) ; copy(1)*id(1)` | representation — fan-out has no shape |
| **cocommutativity** | `δ ; σ = δ` | `copy(1) ; swap = copy(1)` | representation |
| counit, drop the copy | `δ ; (id ⊗ ε) = id` | `copy(n) ; id(n)*drop(n) = id(n)` | representation — the copy that was dropped was never a node |
| counit, drop the original | `δ ; (ε ⊗ id) = id` | `copy(n) ; drop(n)*id(n) = id(n)` | representation |
| naturality of δ | `X ; copy(m) = copy(n) ; (X * X)` for `X : n → m` | copying outputs is running twice on copied inputs | representation — interning: one node per distinct computation, however many wires read it |
| naturality of ε | `X ; drop(m) = drop(n)` for `X : n → m` | discarded work is no work | representation — reachability: unconsumed work has no spelling to survive in; the `n → 0` codomain case is a fold in `apply` |
| drop blocks | `drop(n) * drop(m) = drop(n+m)` | | representation |
| copy blocks | `copy(2)` = the `pick 1 ; pick 1` frame spelling | | representation |

Notes:

1. **Side conditions are discharged globally.** The conditions marked on
   the old axiom sheet — determinism for the naturality of δ, totality for
   the naturality of ε and the interchange — hold because the language has
   no effects, no nondeterminism, and nothing that fails. They are exactly
   what licenses the representation column: interning is only sound because
   running twice is running once, and reachability is only sound because
   discarded work cannot be observed.
2. **The net-change asymmetry lives at the goal.** In the term model, padding
   is explicit, so every law instance above is arity-preserving as written —
   the counit is `copy(1) ; id(1)*drop(1) = id(1)`, `1 → 1` on both sides.
   Only an *identity's statement* needs the old net-change allowance, and
   `Goal::aligned` pays it once, by padding the narrower side.
3. **Yang–Baxter is an instance.** The braid relation
   `swap ; id(1)*swap ; swap = id(1)*swap ; swap ; id(1)*swap` — needed for
   the permutation fragment to be complete — is pure wiring: both sides read
   the same permutation, so the data structure cannot state it.
4. **Totality and determinism are free today, and are the load-bearing
   walls.** An effectful instruction would take `copy-nat` down (the diagonal
   stops being natural), a partial one would take `drop-nat` and the
   interchange (the counit stops being natural and the tensor is merely
   premonoidal). See "if effects arrive", below.

### What completeness means for this layer

In the free cartesian category on a signature, a morphism `n → m` **is** an
m-tuple of first-order terms over n variables. Consequences worth building
on:

- **Normal form.** Every branch-free program is equal to: a
  copy/discard/permute layer, then the operations, with each output a term.
  Two branch-free programs are equal under this layer's laws **iff**
  symbolic evaluation yields the same tuple of terms — dropped inputs and
  discarded work vanish (`drop-nat`), shared work may be copied
  (`copy-nat`).
- **The oracle became the prover, twice.** Symbolic evaluation decides the
  branch-free fragment outright; `diagram.rs` once implemented it as a
  string-diagram engine where this whole layer was representation rather
  than rules, extended over the branch fragment to **ordered, shared case
  trees** (the decision-diagram discipline: independent branches reorder to
  one spelling; sound there,
  complete only here). The `diagram` proof step *is* this procedure applied
  to a goal's two sides. It produces no derivation yet — the replayable-
  derivation milestone in [docs/proving.md](proving.md) is what turns its
  verdicts into checkable artifacts.

## Layer 2: branching — the sum-type fragment

`branch` makes the category bicartesian, and this is the fragment with no
easy complete rewrite system. The reference points from the λ-calculus
literature: β for case, η for booleans, and the commuting conversions.
Deciding equality here needed normalization by evaluation with case trees
(Altenkirch–Dybjer–Hofmann–Scott); expect this layer to stay the hard one.

| law | reading | how |
|---|---|---|
| β | `push c ; branch { A } { B }` = the arm `truthy(c)` selects | fold — a literal condition selects its arm in `branch_on` |
| η (booleans) | ask `is_bool`, branch, push back what branching told you = ε | boundary — seeing it means inventing a case split on an opaque value, which no canonical form here performs; `eta_stays_beyond_the_diagram` pins it |
| commuting conversions (suffix, frame, beside) | what runs after or beside a branch runs inside whichever arm it takes | **a row now** — `select-hoist` in `diagram2/rules.rs`, carrying the region it moves the branch over as payload. It was representation while the engine *evaluated*: grafting every continuation into the arms as it went meant the two spellings built one tree and there was nothing to state. A literal graph states it or cannot say it — `fork-hoist` let a branch grow backwards over what fed it, and until this row nothing let one grow forwards at all |
| branch order | independent case splits commute | order — conditions sort into one global order along every path (`ite`), so both orders are one diagram |
| branch of equal arms | `branch { A } { A } = drop-top ; A` | fold — the tree constructor refuses a node whose arms are one diagram |
| copy absorbed by its branch | `copy(1) ; branch { drop(1);A } { drop(1);B } = branch { A } { B }` | representation — the copy is the same wire, and the dropped one was never a node |
| path condition, truthiness | the arm an outer branch took decides an inner branch on a copy of its condition | fold — the path carries every decided condition; `retest` in `branch_on` and `restrict` |
| path condition, value | a value that tested `equal` to a literal *is* that literal, in the then arm | fold — `specialize`: the literal is written through the arm, joins included |
| codomain fact | `op ; is_bool = op ; drop-top ; push true` for `yields_bool` ops | fold in `apply`; the `yields_bool` fact is measured by `vm` |

Candidates, verified against the junk semantics of
[docs/totality.md](totality.md) but not yet written — none is needed by the
current corpus:

| law | in terms | why it is true |
|---|---|---|
| `not_branch` | `not ; branch { A } { B } = branch { B } { A }` | `not v` is truthy iff `v = false`, the unique falsy value; foldable by branching on the argument of a `not`-shaped condition |
| `or_literal` | the dual of `and-literal`, below | short-circuiting for `or`; arrives the day a proof needs it |
| type-test family | `op ; is_int = op ; drop-top ; push false` for a `yields_bool` op, per (codomain, test) pair | the other five tests of the same codomain fact, table-driven off `Instruction::yields_*` |

Three former candidates are rows now, landed for the contract claim's
proof (see [docs/proving.md](proving.md)):

| law | in terms | why it is true |
|---|---|---|
| `and-literal` | `and` with a literal operand = `as_bool` of the other (truthy literal), or `push false` with the other discarded (the one falsy value) | short-circuiting as an equation; what lets a case split spend a **conjunction**, one conjunct at a time |
| `equal-refl` | `equal` on one wire read twice = `true` | `equal` is structural identity, and the language is deterministic and pure |
| `tuple-cancel`, `as-tuple-built` | `tuple n ; untuple n = id(n)`, and `tuple n ; as_tuple n` = the tuple itself | `untuple` inverts `tuple` exactly, and the coercion is a no-op on a value already the shape it coerces to — stated with the tuple kept for its other readers |

## Layer 3: the signature — evaluation

Laws about what specific instructions compute — today the value rows of
`diagram2/rules.rs`. The discipline that matters more than any individual
law: **facts live on the instruction and are measured by `vm`, never
restated** — `truthy`, `op_arity`, `commutative`, `yields_bool` are the
precedents, and the evaluation fold goes one further: it executes the
literal window on a scratch VM (`run_window`), so there is no second
implementation of the semantics at all.

| law | how |
|---|---|
| evaluation — `push v̄ ; op` = the pushes of what the machine answers, junk included | fold — all-literal arguments run on the machine |
| commutativity — `swap ; op = op` for `Instruction::commutative` | fold — operand wires sort into one canonical order |
| tuple cancellation — `tuple n ; untuple n = id(n)` | fold |
| the coercion — `untuple n ; tuple n = as_tuple n` | fold |
| coercion idempotence — `as_X ; as_X = as_X` | fold — **candidate still**; `as-tuple-round-trip` below is what a proof wanted it for |

Five more are rows now. The first two fold; the last two are **unpackings** —
they say a coercion as the program it is, so they grow a graph, and
[`folding`](../rewrite/src/diagram2/rules.rs) does not carry them. A
strategy names the one it wants (`fire(coercion-guard)`, `at(#7,
as-bool-branch)`), the way `inline` is named: an unpacking changes what is
in front of the other laws, and that is a decision.

| law | in terms | why it is true |
|---|---|---|
| `as-tuple-round-trip` | `as_tuple n ; untuple n ; tuple n = as_tuple n` | the coercion's codomain *is* "a tuple of exactly `n`", so the round trip that junk-normalizes has nothing left to normalize. Not `retuple` twice over: spending `retuple` leaves a second `as_tuple n`, and the idempotence row above is still a candidate |
| `is-tuple-built` | `tuple m ; is_tuple n = tuple m ; push (m == n)` | a value the window watched being built has a shape the window knows, so a test of that shape is decided rather than computed — `as-tuple-built`'s sibling, and stated with the tuple kept for its other readers the same way. It is the row that lets a `type` or `enum` guard be written `pick 0 ; is_tuple n` |
| `as-bool-branch` | `as_bool = if x { true } else { false }` | `as_bool` is `truthy` made into an instruction and a `select` keeps the block `truthy` picks; the arms answer the two values `truthy` can report, and read nothing, so the branch needs no `fork` |
| `coercion-guard` | `as_T = if x is a T { x } else { junk }` — `is_bool`/`true`, `is_int`/`0`, `is_tuple n`/a tuple of `n` empty tuples | the instruction set's own sentence, as an equation: each coercion "is the identity where the value is already of that type, and hands back a default where it is not". The width belongs in the guard, and `is_tuple n` is where it lives: the width-blind `is_tuple` would claim `as_tuple 2` is the identity on `(1, 2, 3)` |

What the unpackings buy is the direction of reading the rest of the table
cannot go. A coercion is opaque to every rule that wants to know what a
value *is*; these put the test that decides it into the graph, where the
branch layer and a `cases` split can spend it.

## Lemmas, never axioms

Laws that looked essential on the old axiom sheet and are nothing at all in
the wiring representation — each held by a test rather than stated anywhere:

| lemma | why it is free | held by |
|---|---|---|
| `copy_const` — `push c ; copy(1) = push c ; push c` | two `push c` wires intern to one node | `diagram::tests::copying_a_constant_is_pushing_it_twice`, and the corpus identity |
| vacuous — copy a block, compute, drop the results = ε | unconsumed work has no spelling | corpus identity `discarded_work_on_copies` |
| the guard a split leaves — `op ; copy(1) ; is_bool = op ; push true` | one wire read twice, plus the `yields_bool` fold | corpus identity `the_guard_a_split_leaves` |
| a frame off — `X * id(1) = swap ; id(1)*X ; swap` | pure wiring | corpus identity `taking_a_frame_off`, `diagram::tests::a_frame_is_a_roll_pair` |

The demotion test is unchanged from the old sheet: read the opaque `X` as a
random oracle (kills the naturality of δ) or as fallible (kills the
naturality of ε and the interchange) and see what else falls. A law that
survives every such reading of the others but fails on its own is
independent; anything else is a lemma — or, here, a fact of the data
structure.

## If effects or partiality ever arrive

The literature already says which rows fall, and it matches the constraints
column exactly:

- **Partiality** (a `panic` returns): the naturality of ε and the
  interchange go — the counit stops being natural and the tensor is merely
  *premonoidal* (Power–Robinson). In the engine that means reachability may
  no longer delete work and boxes acquire an evaluation order: drops and
  sequencing would need explicit nodes again.
- **Nondeterminism or effects**: the naturality of δ goes — the diagonal
  stops being natural, so interning may no longer merge two runs of one
  computation. The recovery notion is Führmann's *thunkability*: the laws
  return for the pure sub-language, which is how an effectful Hanoi would
  keep this page — as the theory of its pure fragment.

## References

- Fox, *Coalgebras and cartesian categories* (1976) — cartesian = symmetric
  monoidal + natural cocommutative comonoids; the spine of layer 1.
- Lafont, *Towards an algebraic theory of Boolean circuits* (2003) —
  explicit finite presentations of these PROPs.
- Bonchi–Sobociński–Zanasi, *Interacting Hopf algebras*; the *String Diagram
  Rewrite Theory* series I–III — rewriting these presentations as hypergraph
  rewriting, which dissolves the padding bureaucracy a term presentation
  pays for; the road `rewrite/src/diagram2` walks in full — laws as pairs
  of open graphs, rewriting as checked cut-and-splice. Kissinger's Chyp is
  the closest working relative of that layer.
- Altenkirch–Dybjer–Hofmann–Scott, *Normalization by evaluation for typed
  lambda calculus with coproducts* (2001) — why layer 2 is the hard one, and
  the shape of its decision procedure.
- Power–Robinson, *Premonoidal categories and notions of computation*
  (1997); Führmann, *Direct models of the computational lambda calculus*
  (1999) — the effects roadmap.
- Willsey et al., *egg: Fast and extensible equality saturation* (POPL 2021)
  — the engine an earlier `bin/prove` was built on, retired when the diagram
  representation made ~95% of its rule firings (measured on the contract
  claim) into padding translation with no spelling left to translate.
