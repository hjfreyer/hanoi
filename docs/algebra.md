# The algebra of programs

A reference sheet for the equational theory the rewriter works in: every
structural law stated symbolically and in the term model's spelling, with its
side conditions, where it lives in `rewrite/src/rules.rs`, and what is known
about completeness. [docs/proving.md](proving.md) describes the machinery
that applies these laws; this page is the laws themselves, and the map to the
literature they come from.

The organizing fact: the copy/drop/swap/frame fragment of this language is the
standard finite presentation of the **free cartesian PROP** — the categorical
structure singled out by Fox's theorem — and the branch fragment is the
equational theory of **sum types**. The first has a complete, known axiom set
and a decision procedure; the second is decidable but genuinely hard, and that
split is exactly where the proof effort goes: every identity in the corpus
closes on the rules alone except the sum-type path-condition claim, and that
one needs its case split written out as a chain of cuts.

## Conventions

- `;` is composition in program order — the left factor runs first. `*` is
  the tensor, and in `W * X` the **deeper** stack region is on the left, so
  `dip { A }` is `A * id(1)`. Both are the term model's own operators
  (`rewrite/src/term.rs`); objects are stack widths, so on objects `*` is
  `+`.
- Generators: `copy(1) : 1 → 2` (δ, the fresh copy lands on top), `drop(1) :
  1 → 0` (ε), `swap : 2 → 2` (σ). The block forms `copy(n)`, `drop(n)`,
  `id(n)` are their own leaves.
- Every law is stated in its minimal window. Congruence embeds it in any
  context — in the e-graph that is just the fact that rewriting is closed
  under node formation.
- **Where** column: the rule's name in `rules.rs`, *emergent* when the law
  needs no rule of its own (it falls out of others plus the e-graph's
  bidirectionality), *candidate* when it is true and useful but not yet
  written.

## Layer 1: the cartesian core

The structural laws — everything about copying, discarding and rearranging,
with the signature's instructions opaque. This layer has a known complete
presentation: symmetric monoidal structure, a cocommutative comonoid on the
generating object, and naturality of δ and ε (Fox 1976; Lafont 2003 is the
copy-paste-friendly catalogue).

| law | symbolic | in terms | where |
|---|---|---|---|
| associativity of `;` | `(a;b);c = a;(b;c)` | as written | `assoc-compose` ⇄ |
| associativity of `*` | `(a*b)*c = a*(b*c)` | as written | `assoc-par` ⇄ |
| units of `;` | `id ; a = a = a ; id` | `id(n)` of the right width | `unit-compose-left/right` (elim only) |
| unit of `*` | `id₀ * a = a = a * id₀` | width-0 leaf | `par-unit-deep/top` |
| id blocks fuse | `id(n) * id(m) = id(n+m)` | | `par-id-fuse` |
| degenerate blocks | `copy(0) = drop(0) = id(0)` | | `copy-nothing`, `drop-nothing` |
| interchange, staircase form | `a * b = (a * id) ; (id * b) = (id * b) ; (a * id)` | | `stair-deep-first`, `stair-top-first`, and the two `stair-read-*` recognizers |
| interchange, middle-four | `(a;c) * (b;d) = (a*b) ; (c*d)` when the split aligns | | `par-fuse` (fusing direction; splitting is the staircases) |
| producer beside a computation | `a ; (id(a.out) * b) = a * b` for `b : 0 → m` | | `compose-to-par` |
| symmetry involutive | `σ ; σ = id₂` | `swap ; swap = id(2)` | `swap-cycle` |
| naturality of σ | `(a*b) ; σ = σ ; (b*a)` | legs `1 → 1` | `swap-nat` ⇄ |
| σ past a dropping leg | `swap ; (id(1)*drop(1)) = drop(1)*id(1)`, and mirror | the `1 → 0` leg naturality cannot say | `swap-drop-top/deep` ⇄ |
| coassociativity | `δ;(id⊗δ) = δ;(δ⊗id)` | `copy(1) ; id(1)*copy(1) = copy(1) ; copy(1)*id(1)` | `coassociative` ⇄ |
| **cocommutativity** | `δ ; σ = δ` | `copy(1) ; swap = copy(1)` | `cocommutative` |
| counit, drop the copy | `δ ; (id ⊗ ε) = id` | `copy(n) ; id(n)*drop(n) = id(n)` | `counit-copy` |
| counit, drop the original | `δ ; (ε ⊗ id) = id` | `copy(n) ; drop(n)*id(n) = id(n)` | `counit-original` |
| naturality of δ | `X ; copy(m) = copy(n) ; (X * X)` for `X : n → m` | copying outputs is running twice on copied inputs | `copy-nat` ⇄ (`copy-nat-rev` reads the shared shape back) |
| naturality of ε | `X ; drop(m) = drop(n)` for `X : n → m` | discarded work is no work | `drop-nat` (forward only — the reverse conjures an `X`; a stepping stone is how that direction is reached) |
| drop blocks | `drop(n) * drop(m) = drop(n+m)` | | `drop-par-fuse`; `drop-split-two` ⇄ for the width the corpus uses |
| copy blocks | `copy(2)` = the `pick 1 ; pick 1` frame spelling | | `copy-block-two` ⇄ |

Notes:

1. **Side conditions became facts.** A width cannot appear in an e-graph
   pattern, so every law indexed by one reads it off the class analysis
   (arity, `is_id`, `is_drop`, `is_copy`). The conditions marked on the old
   axiom sheet — determinism for `copy-nat`, totality for `drop-nat` and
   interchange — are discharged globally: the language has no effects, no
   nondeterminism, and nothing that fails.
2. **The net-change asymmetry lives at the goal.** In the term model, padding
   is explicit, so every rule instance above is arity-preserving as written —
   the counit is `copy(1) ; id(1)*drop(1) = id(1)`, `1 → 1` on both sides.
   Only an *identity's statement* needs the old net-change allowance, and
   `Goal::aligned` pays it once, by padding the narrower side.
3. **Elimination-only units are not a gap.** Unit *introduction* is unbounded
   and is never needed: the staircase rules re-pad shapes boundedly, which is
   what introduction was ever for.
4. **Yang–Baxter is an instance.** The braid relation
   `swap ; id(1)*swap ; swap = id(1)*swap ; swap ; id(1)*swap` — needed for
   the permutation fragment to be complete — is naturality of σ at
   `X = swap`, reachable from `swap-nat` plus the staircases; the
   `a_framed_computation_is_a_rolled_one` corpus test runs its shape.
5. **Totality and determinism are free today, and are the load-bearing
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
- **A cheap oracle.** Symbolic evaluation therefore decides the branch-free
  fragment outright, and `rewrite/src/nf.rs` implements it — extended to
  **case trees** over the branch fragment (sound there, complete only
  here). It produces no derivation, so it cannot replace the prover — but
  it answers "is this identity even true?" before anything searches, it is
  the right completeness sweep for the rule set (random branch-free pairs,
  oracle verdict against e-graph reach), and the `norm` proof steps spend
  it: `A = B` cut at the left side's normal form into `A = NF(A)` and
  `NF(A) = B`, with the e-graph answering for both halves — or, spelled
  `norm_trusted` and so marked in the proof, with the `A = NF(A)` half
  closed on the oracle's word. [docs/proving.md](proving.md) has the trust
  discussion.

## Layer 2: branching — the sum-type fragment

`branch` makes the category bicartesian, and this is the fragment with no
easy complete rewrite system. The reference points from the λ-calculus
literature: β for case, η for booleans, and the commuting conversions.
Deciding equality here needed normalization by evaluation with case trees
(Altenkirch–Dybjer–Hofmann–Scott); expect this layer to stay the hard one.

| law | reading | where |
|---|---|---|
| β | `push c ; branch { A } { B }` = the arm `truthy(c)` selects | `fold-branch` |
| η (booleans) | ask `is_bool`, branch, push back what branching told you = ε | stated as `identities::split_bool` in the corpus and *run*; as a rewrite it inserts branches, so it stays a goal-level move for the case-split strategy to spend |
| commuting conversion, suffix | `branch { A } { B } ; C = branch { A;C } { B;C }` | `branch-distribute` ⇄ (backward is suffix-factoring) |
| commuting conversion, frame | `(x * id(1)) ; branch { A } { B } = branch { x;A } { x;B }` | `branch-hoist` ⇄ — no arithmetic: the frame hid exactly the condition |
| commuting conversion, beside | `x * branch { A } { B } = branch { x*A } { x*B }` | `branch-beside` ⇄ — the tensor distributing over the case, and independent of the other two. The one lowering asks for constantly: a branch whose arms are narrower than the stack is emitted framed, and every law about branches is stated unframed |
| copy absorbed by its branch | `copy(1) ; branch { drop(1);A } { drop(1);B } = branch { A } { B }` | `branch-absorbs-copy` |
| path condition, truthiness | the arm an outer branch took decides an inner branch on a copy of its condition | `retest-then/-else` (+ `-bare` forms) |
| path condition, value | a value that tested `equal` to a literal *is* that literal, in the then arm | `specialize-equal` |
| codomain fact | `op ; is_bool = op ; drop-top ; push true` for `yields_bool` ops | `bool-result`; the `yields_bool` fact is measured by `vm` and lifted through composition by the analysis |

Candidates, verified against the junk semantics of
[docs/totality.md](totality.md) but not yet written — none is needed by the
current corpus:

| law | in terms | why it is true |
|---|---|---|
| `not_branch` | `not ; branch { A } { B } = branch { B } { A }` | `not v` is truthy iff `v = false`, the unique falsy value |
| `and_branch` | `and ; branch { A } { B } = branch { branch { A } { B } } { drop-top ; B }` | short-circuiting as an equation; dual form for `or` |
| `equal_refl` | `copy(1) ; equal = drop... = push true` over the value | `equal` is structural identity; unprovable on opaque values today |
| type-test family | `op ; is_int = op ; drop-top ; push false` for a `yields_bool` op, per (codomain, test) pair | the other five tests of the same codomain fact, table-driven off `Instruction::yields_*` |

## Layer 3: the signature — evaluation

Laws about what specific instructions compute. The discipline that matters
more than any individual law: **facts live on the instruction and are
measured by `vm`, never restated** — `truthy`, `op_arity`, `commutative`,
`yields_bool` are the precedents, and the prover's `eval` rule goes one
further: it executes the literal window on a scratch VM, so there is no
second implementation of the semantics at all.

| law | where |
|---|---|
| evaluation — `push v̄ ; op` = the pushes of what the machine answers, junk included | `eval`, `eval-padded`, `eval-nothing` |
| commutativity — `swap ; op = op` for `Instruction::commutative` | `commute` |
| tuple cancellation — `tuple n ; untuple n = id(n)` | `tuple-cancel` |
| the coercion — `untuple n ; tuple n = as_tuple n` | `untuple-retuple` |
| coercion idempotence — `as_X ; as_X = as_X` | `as-bool-idem`, `as-int-idem`, `as-tuple-idem` |

## Lemmas, never axioms

Laws that looked essential and are reachable from the set above — each held
by a test rather than stated as a rule:

| lemma | reached by | held by |
|---|---|---|
| `copy_const` — `push c ; copy(1) = push c ; push c` | `copy-nat` at `X = push c`, staircases, units | `rules::tests::copying_a_constant_is_pushing_it_twice`, and the corpus identity |
| vacuous — copy a block, compute, drop the results = ε | counits + `drop-nat` + the block bridges | corpus identity `discarded_work_on_copies` |
| the guard a split leaves — `op ; copy(1) ; is_bool = op ; push true` | `copy-nat` read backward by the e-graph, `bool-result`, counits | corpus identity `the_guard_a_split_leaves` |
| a frame off — `X * id(1) = swap ; id(1)*X ; swap` | `swap-nat` + `swap-cycle` | corpus identity `taking_a_frame_off` |
| branch of equal arms — `branch { A } { A } = drop-top ; A` | `branch-distribute` backward + `drop-nat` + counit | candidate sweep, when wanted |

The demotion test is unchanged from the old sheet: read the opaque `X` as a
random oracle (kills `copy-nat`) or as fallible (kills `drop-nat` and the
interchange) and see what else falls. A law that survives every such reading
of the others but fails on its own is independent; anything else is a lemma.

## If effects or partiality ever arrive

The literature already says which rows fall, and it matches the constraints
column exactly:

- **Partiality** (a `panic` returns): `drop-nat` and the interchange go — the
  counit stops being natural and the tensor is merely *premonoidal*
  (Power–Robinson). Every other layer-1 law survives.
- **Nondeterminism or effects**: `copy-nat` goes — the diagonal stops being
  natural. The recovery notion is Führmann's *thunkability*: the laws return
  for the pure sub-language, which is how an effectful Hanoi would keep this
  page — as the theory of its pure fragment.

## References

- Fox, *Coalgebras and cartesian categories* (1976) — cartesian = symmetric
  monoidal + natural cocommutative comonoids; the spine of layer 1.
- Lafont, *Towards an algebraic theory of Boolean circuits* (2003) —
  explicit finite presentations of these PROPs.
- Bonchi–Sobociński–Zanasi, *Interacting Hopf algebras*; the *String Diagram
  Rewrite Theory* series I–III — rewriting these presentations as hypergraph
  rewriting, which dissolves the padding bureaucracy layer 1 pays for in
  staircase rules; Kissinger's Chyp is the working tool.
- Altenkirch–Dybjer–Hofmann–Scott, *Normalization by evaluation for typed
  lambda calculus with coproducts* (2001) — why layer 2 is the hard one, and
  the shape of its decision procedure.
- Power–Robinson, *Premonoidal categories and notions of computation*
  (1997); Führmann, *Direct models of the computational lambda calculus*
  (1999) — the effects roadmap.
- Willsey et al., *egg: Fast and extensible equality saturation* (POPL 2021)
  — the engine `bin/prove` is built on.
