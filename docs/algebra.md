# The algebra of programs

A reference sheet for the rewriter's equation set: every structural law stated
symbolically and as a Hanoi window, with its side conditions, its status in the
current set, and what is known about completeness. Written against the set of
22 in [docs/tactics.md](tactics.md); intended as the sheet to check a rebooted
rule set against, so gaps and candidates are listed beside what exists.

The organizing fact: the copy/drop/swap/frame fragment of this language is the
standard finite presentation of the **free cartesian PROP** — the categorical
structure singled out by Fox's theorem — and the branch fragment is the
equational theory of **sum types**. The first has a complete, known axiom set
and a decision procedure; the second is decidable but genuinely hard, and that
split is exactly where the proof effort in this corpus goes.

## Conventions

- `;` is composition in program order — the left factor runs first — matching
  both diagrammatic order and Hanoi concatenation. It is written only where a
  law needs the seam pointed at; adjacency means the same thing.
- Objects are stack widths, so on objects `⊗` is `+`. In `W ⊗ X` the **deeper**
  region is on the left and the top of the stack on the right, so
  `dip k { A }` is `A ⊗ id_k`.
- Generators: `δ = copy : 1 → 2` (the fresh copy lands on top — the right
  factor), `ε = drop : 1 → 0`, `σ = swap : 2 → 2`.
- Derived: `Δₙ : n → 2n` is the block diagonal, `pick (n-1)` written `n` times;
  `!ₙ = εⁿ : n → 0` is `n` drops; `sink k` puts the top value under the `k`
  beneath it.
- Every law is stated in its minimal window. Congruence — `A = B ⟹ C[A] = C[B]`,
  which is what a `Location` is — embeds it in any context, so no ambient
  identity wires appear.
- **Status** column: *in set* (one of the 22), *missing* (needed for
  completeness, not currently stated), *candidate* (true and useful, priority a
  judgment call), *lemma* (derivable — keep as a matcher or tactic, never as an
  axiom).

## Layer 1: the cartesian core

The structural laws — everything about copying, discarding and rearranging,
with the signature's instructions opaque. This layer has a known complete
presentation: symmetric monoidal structure, a cocommutative comonoid on the
generating object, and naturality of `δ` and `ε` (Fox 1976; Lafont 2003 is the
copy-paste-friendly catalogue).

| law | symbolic | Hanoi | constraints | status |
|---|---|---|---|---|
| coassociativity | `δ ; (id ⊗ δ) = δ ; (δ ⊗ id)` | `copy ; copy = copy ; dip 1 { copy }` | — | in set (`copy_assoc`) |
| counit, drop the copy | `δ ; (id ⊗ ε) = id` | `copy ; drop = ε` | net-change asymmetry (note 2) | in set (`counit`) |
| counit, drop the original | `δ ; (ε ⊗ id) = id` | `copy ; dip 1 { drop } = ε` | top of stack only; at depth it is a `roll` | in set (`counit_under`) |
| **cocommutativity** | `δ ; σ = δ` | `copy ; swap = copy` | — | **missing** (note 5) |
| symmetry involutive | `σ ; σ = id₂` | `swap ; swap = ε` | — | in set (`swap_cycle`) |
| naturality of σ | `(X ⊗ Y) ; σ = σ ; (Y ⊗ X)` | `dip 1 { X } ; sink m = sink n ; X` is the `Y = id₁` instance | `X : n → m`; matcher places `m = 1`, single frame — the law is general | in set (`unframe`) |
| naturality of δ | `Δₙ ; (X ⊗ X) = X ; Δₘ` | `pick (n-1)^n ; X ; dip m { X } = X ; pick (m-1)^m` | `X : n → m` **deterministic** — the only law that needs it | in set (`copy_nat`) |
| naturality of ε | `X ; !ₘ = !ₙ` | `X ; drop^m = drop^n` | `X : n → m` **total**; lowers the input requirement | in set (`annihilate`) |
| `id_k ⊗ (−)` preserves composition | `(id_k ⊗ A) ; (id_k ⊗ B) = id_k ⊗ (A ; B)` | `dip k { A } ; dip k { B } = dip k { A B }` | same `k` both frames | in set (`fuse`) |
| **`id_k ⊗ (−)` preserves identities** | `id_k ⊗ id₀ = id_k` | `dip k { } = ε` | — | **missing** — the other half of functoriality; `fuse` alone cannot delete an empty frame |
| tensor unit | `id₀ ⊗ A = A` | `dip 0 { A } = A` | — | in set (`elim_dip0`) |
| strict associativity of ⊗ | `id_k ⊗ (id_j ⊗ A) = id_{k+j} ⊗ A` | `dip k { dip j { A } } = dip (k+j) { A }` | — | in set (`collapse`) |
| interchange | `(id ⊗ X) ; (Y ⊗ id) = (Y ⊗ id) ; (id ⊗ X)` | `X ; D_k = D_(k−m+n) ; X` | `X : n → m`, `k ≥ m`; totality of the reordered computations | in set (`interchange`) |

Notes:

1. **Two kinds of constraint.** Semantic side conditions (determinism,
   totality, `k ≥ m`, depth-0-only) are part of the law — violate them and the
   equation is false. Matcher restrictions (`unframe` placing only `m = 1`) are
   part of the search; a derivation file may cite the general law.
2. **Net change, not full arity.** The counits and `annihilate` have sides with
   different input *requirements* — `copy ; drop` is `(1 → 1)` against `ε` at
   `(0 → 0)`. The compiler and `--check` compare net stack effect for exactly
   this reason.
3. **Arities are re-derived.** Every `n`, `m` above rides in a script as an
   argument and is recomputed by the applier against the real program. The
   arity constraints cost nothing to state.
4. **Totality and determinism are free today.** No `panic`, no effects — so the
   starred conditions are discharged by construction. They are recorded because
   they are the load-bearing walls: an effectful instruction takes `copy_nat`
   down (the diagonal stops being natural), a partial one takes `annihilate`
   and `interchange` (the counit stops being natural and the tensor is merely
   premonoidal). See "if effects arrive", below.
5. **Cocommutativity appears underivable from the 22.** For a *boolean* value
   it falls to `split_bool` + `eval` (each arm holds a literal, and `eval`
   folds `push c ; push c ; swap`). For an opaque value nothing applies: no law
   in the set exchanges the two outputs of a `copy`. Worth a `rewrite` session
   to confirm before adding — and if it is underivable, some identity will
   eventually stall on it.

### Permutations: Yang–Baxter is already an instance

A complete presentation of the symmetric groups by adjacent transpositions
needs three families: `sᵢ² = 1`, `sᵢsⱼ = sⱼsᵢ` for `|i−j| ≥ 2`, and the braid
relation `sᵢsᵢ₊₁sᵢ = sᵢ₊₁sᵢsᵢ₊₁`. In this language those are, respectively,
`swap_cycle` (under frames), `interchange` (disjoint windows), and:

```text
swap ; dip 1 { swap } ; swap  =  dip 1 { swap } ; swap ; dip 1 { swap }
```

The third is **not** covered by `interchange` — the windows overlap — but it
needs no new axiom: it is `unframe` at `X = swap` (`n = m = 2`), once `sink 2`
is spelled as `swap ; dip 1 { swap }`. No matcher places `unframe` at `m = 2`,
so today this is reachable by a derivation file and not by a search. A rebooted
set should either keep the general `unframe` and make sure the braid instance
is provable, or state the braid relation directly; without one of the two, the
permutation fragment is incomplete.

### What completeness means for this layer

In the free cartesian category on a signature, a morphism `n → m` **is** an
m-tuple of first-order terms over n variables. Consequences worth building on:

- **Normal form.** Every branch-free program is equal to: a copy/discard/permute
  layer, then the operations, with each output a term. Two branch-free programs
  are equal under this layer's axioms **iff** symbolic evaluation yields the
  same tuple of terms (dropped inputs and discarded work vanish — that is
  `annihilate` — and shared work may be copied — that is `copy_nat`).
- **A cheap oracle.** Symbolic evaluation decides the branch-free fragment
  outright. It produces no derivation, so it cannot replace `prove` — but it
  can answer "is this identity even true?" before a tactic is written, and it
  is the right completeness test for the axiom set: sweep pairs of random
  branch-free terms, compare the oracle's verdict against the rewriter's reach.
- `--stack`'s abstract interpretation is this oracle in embryo.

## Layer 2: branching — the sum-type fragment

`branch` makes the category bicartesian (products *and* a boolean coproduct),
and this is the fragment with no easy complete rewrite system. The known-good
reference points from the λ-calculus literature: β for case, η for booleans,
and the commuting conversions. Deciding equality here needed normalization by
evaluation with case trees (Altenkirch–Dybjer–Hofmann–Scott); expect this
layer to stay the hard one, and measure any reboot against these named laws.

| law | symbolic reading | Hanoi | status |
|---|---|---|---|
| β | `case(inl) = first arm` | `push c ; branch { A } { B }` = the arm `truthy(c)` selects | in set (`fold_branch`) |
| η (booleans) | `case(x, true, false) = x` | `copy ; is_bool ; branch { branch { push true } { push false } } { }` = `ε` | in set (`split_bool`) |
| commuting conversion, suffix | `case(x, f, g) ; h = case(x, f;h, g;h)` | `branch { A } { B } ; C = branch { A C } { B C }` | in set (`distribute`) |
| commuting conversion, frame | `(id ⊗ case) = case of (id ⊗ −)` | `dip (k+1) { X } ; branch { A } { B } = branch { dip k { X } ; A } { dip k { X } ; B }` | in set (`hoist`) |
| path condition, truthiness | an arm knows which way its own condition branches | `retest` (see tactics.md) | in set |
| path condition, value | an arm that tested `equal` to a literal holds that literal | `specialize_equal` | in set |
| codomain fact | `op` factors through `Bool ↪ Value` | `op ; is_bool = op ; drop ; push true` for `yields_bool` ops | in set (`bool_result`) |

The coproduct laws are sound with the shared program **duplicated textually**
— `C` appears in both arms of `distribute` — because a branch's arms are
alternatives: any run takes one, so nothing runs twice. Contrast the tensor,
where `(a;b) ⊗ c ≠ (a⊗c);(b⊗c)` unless `c` is idempotent: ⊗ means *both
happen*. That asymmetry is the whole difference between this layer and layer 1.

### Candidates for this layer

Each verified against the junk semantics of [docs/totality.md](totality.md) —
`truthy(v) = (v ≠ false)`, per-operand coercion, `equal` is structural
identity. None is in the current set.

| law | Hanoi | why it is true | why it is useful |
|---|---|---|---|
| `not_branch` | `not ; branch { A } { B } = branch { B } { A }` | `not v` is truthy iff `v = false`, the unique falsy value | deletes every `not` that feeds a branch; pairs with `split_bool`, which otherwise leaves the `not` to fold arm by arm |
| `and_branch` | `and ; branch { A } { B } = branch { branch { A } { B } } { drop ; B }` | `and` pops the top operand first; if it is falsy the else arm runs regardless of the other | turns boolean structure into control structure, where `retest` and the path-condition laws can reach it — short-circuiting as an equation |
| `or_branch` | `or ; branch { A } { B } = branch { drop ; A } { branch { A } { B } }` | dual of `and_branch` | same |
| `equal_refl` | `copy ; equal = drop ; push true` | `equal` is structural identity, so `v == v` for every value the machine has | a postcondition comparing a value to itself is otherwise unprovable on opaque values — `specialize_equal` needs a literal |
| `branch_same_arms` | `branch { A } { A } = drop ; A` | either arm is `A` | **lemma, not axiom**: `inv(distribute)` factors `A` as a shared suffix, `annihilate` at `m = 0` and `counit` finish — the `same_arms` derivation in tactics.md |
| type-test family | `op ; is_int = op ; drop ; push false` for a `yields_bool` op, and the analogous line per (op-codomain, test) pair | same fact as `bool_result`, read at the other five tests | tactics.md already names this gap; keep it table-driven off `Instruction::yields_*` and measured by `vm`, never restated |
| `assoc` for `and`/`or` | `dip 1 { and } ; and = and ; and` | per-operand `truthy` and `truthy(Bool(p)) = p` | low priority — only bites on opaque values, where `split_bool` cannot reach; note `add` does **not** get this shape, its flag changes the arity |
| De Morgan | `and ; not = not ; dip 1 { not } ; or` | the argument in totality.md § Truthiness | low priority; mostly subsumed by `not_branch` once conditions feed branches |

`retest` and `specialize_equal` are this language's spelling of what the sum
literature calls path conditions, and they are the right shape: a branch
observes truthiness and nothing else, so *which facts an arm may learn* is
exactly (a) which way a second test of the same value goes, and (b) the whole
value when the test was `equal` against a literal. A reboot should keep both
and expect no completeness theorem to cover them — this is the fragment where
the corpus, not a theorem, says what is missing.

## Layer 3: the signature — evaluation

Laws about what specific instructions compute. The discipline that matters
more than any individual law: **facts live on the instruction and are measured
by `vm`, never restated in the rewriter** — `truthy`, `op_arity`,
`commutative`, `yields_bool` are the existing precedents. A second copy of any
of these lists is a silent hazard.

| law | Hanoi | status |
|---|---|---|
| evaluation | `push v₁ … push vₙ ; op` = the pushes of what `op` answers — junk included, flags included, `tuple`/`untuple` included | in set (`eval`) |
| tuple cancellation | `tuple n ; untuple n = push true` | in set (`cancel_tuple`); no backward reading — `push true` does not determine `n` |
| commutativity | `swap ; op = op` for `add`, `multiply`, `and`, `or`, `equal` | in set (`commute`) |
| structural `equal` over tuples | `tuple n ; dip 1 { tuple n } ; equal` = the pairwise `equal`s conjoined | candidate — what a postcondition comparing a *built* value against a spec wants; today `eval` covers only the all-literal case |

## Lemmas, never axioms

Derivable — each has a derivation checked in the tests, and keeping them
demoted is what keeps the axiom count honest. A reboot inherits the same
worked examples:

| lemma | derived from | where checked |
|---|---|---|
| `copy_const` — `push c ; copy = push c ; push c` | `copy_nat` at `X = push c`, `interchange`, `elim_dip0` | `applier::tests::copy_const_is_derivable_from_copy_nat` |
| vacuous — `Δₙ ; X ; !ₘ = ε` | n× `counit` backward, one `annihilate` backward | `applier::tests::vacuous_is_derivable_from_annihilate_and_counit` |
| `bool_result_copied` — `op ; copy ; is_bool = op ; push true` | `copy_nat` backward, `interchange`, `bool_result`, annihilation, counits | `tests::the_guard_a_split_leaves_is_derivable` |
| `factor` — hoist a shared prefix | 2× `elim_dip0` backward, `hoist` backward | the three-step firing in tactics.md |
| `speculate` / `lift` | counits backward, `introduce`, `factor` | `tests::speculating_is_what_the_three_rules_do_written_out` |
| `branch_same_arms` | `inv(distribute)`, `annihilate`, `counit` | the `same_arms` run in tactics.md |
| Yang–Baxter | `unframe` at `X = swap` | not yet stated as an identity — worth adding to the corpus |

The demotion test, from tactics.md: read the opaque `X` as a random oracle
(kills `copy_nat`) or as fallible (kills `annihilate`, `interchange`) and see
what else falls. A law that survives every such reading of the others but
fails on its own is independent; anything else is a lemma.

## If effects or partiality ever arrive

The literature already says which rows fall, and it matches the constraints
column exactly:

- **Partiality** (a `panic` returns): `annihilate` and `interchange` go — the
  counit stops being natural and the tensor is merely *premonoidal*
  (Power–Robinson). Every other layer-1 law survives.
- **Nondeterminism or effects**: `copy_nat` goes — the diagonal stops being
  natural. The recovery notion is Führmann's *thunkability* / centrality: the
  laws return for the sub-category of pure computations, which is how an
  effectful Hanoi would keep this document — as the theory of its pure
  fragment, with an effect row annotation deciding membership.

## References

- Fox, *Coalgebras and cartesian categories* (1976) — cartesian = symmetric
  monoidal + natural cocommutative comonoids; the spine of layer 1.
- Lafont, *Towards an algebraic theory of Boolean circuits* (2003) — explicit
  finite presentations of these PROPs; the copy-paste catalogue.
- Bonchi–Sobociński–Zanasi, *Interacting Hopf algebras*; the *String Diagram
  Rewrite Theory* series I–III — rewriting these presentations as hypergraph
  rewriting, which dissolves the frame bureaucracy layer 1 pays for explicitly;
  Kissinger's Chyp is the working tool.
- Altenkirch–Dybjer–Hofmann–Scott, *Normalization by evaluation for typed
  lambda calculus with coproducts* (2001) — why layer 2 is the hard one, and
  the shape of its decision procedure.
- Power–Robinson, *Premonoidal categories and notions of computation* (1997);
  Führmann, *Direct models of the computational lambda calculus* (1999) — the
  effects roadmap.
- egg (Willsey et al., POPL 2021) — equality saturation with proof production;
  the natural candidate for a "smarter upper layer" whose explanations compile
  to `.hand` derivations, which tactics.md § "what is not here yet" already
  reserves space for.
