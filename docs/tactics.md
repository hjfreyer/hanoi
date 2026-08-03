# Tactics

`bin/rewrite` turns one sentence's compiled bytecode into a tree and prints it.
A **tactic** says how to rewrite that tree before printing.

No *call* is expanded unless you ask. The default listing shows one sentence,
naming every call it makes on a single line; `inline` is how you open one up.
Blocks written inline — branch arms and `dip N { ... }` bodies — are always
spelled out, because they are not calls.

```bash
cargo run --bin rewrite -- tests 'SimpleTuple::check' -t dip_normalize
```

A rewriting system has three separable parts, and a tactic is what makes the
second and third of them things you say rather than things the tool decides:

1. **Rules** — a fixed set of local transformations.
2. **Control** — order, choice, repetition.
3. **Traversal** — where in the tree to look.

## Rules

Every rule is a local splice on a window of a fixed small number of adjacent
nodes — two for most of them, three or four where a rule has to see where its
operand came from. It either matches and returns a replacement, or fails.
`--list-rules` prints them.

| rule | window | replacement |
|---|---|---|
| `collapse` | `dip k { dip j { B } }` | `dip (k+j) { B }` |
| `expand` | `dip k { B }`, `k >= 2` | `dip 1 { dip (k-1) { B } }` |
| `factor_branch` | `branch { X A } { X B }` | `dip 1 { X }; branch { A } { B }` |
| `sink` | `X ; dip k { S }`, `k >= m` | `dip (k-m+n) { S } ; X` |
| `float` | `dip j { S } ; X`, `j >= n` | `X ; dip (j-n+m) { S }` |
| `fuse` | `dip k { A }; dip k { B }` | `dip k { A B }` |
| `annihilate_drop` | `X ; drop` | nothing, or `drop` |
| `pick_drop_to_roll` | `pick d ; dip (d+1) { drop }` | `roll d` |
| `noop` | `roll 0`, or an empty `dip` | nothing |
| `flatten_call` | `dip 0 { P }` | `P`, spliced in |
| `distribute_branch` | `branch { A } { B } ; X` | `branch { A X } { B X }` |
| `fold_branch` | `push true \| false ; branch { A } { B }` | the arm it selects |
| `inline` | a call | the block it names, spliced in |
| `fold_const` | `push a ; push b ; op` | `push (a op b)` |
| `fold_const_unary` | `push a ; op` | `push (op a)` |
| `bool_identity` | `B ; push true ; and` | `B`, and the three other unit laws |
| `cancel_tuple` | `tuple n ; untuple n` | nothing |
| `retain_condition` | `pick 0 ; branch { A } { B }` | `branch { push true; A } { push false; B }` |
| `specialize_equal` | `pick d; push c; equal; branch { A } { B }` | the same, with A as `dip d { drop; push c }; A` |
| `copy_const` | `push c ; pick 0` | `push c ; push c` |
| `dup_natural` | `pick 0 ; X ; dip m { X }`, `X : 1 -> m` | `X ; (pick (m-1))^m` |
| `unfactor_branch` | `dip k { X } ; branch { A } { B }`, `k >= 1` | `branch { dip (k-1) { X }; A } { … }` |
| `rebuild_copy` | `pick 0 ; untuple n` | `untuple n ; (pick (n-1))^n ; dip n { tuple n }` |
| `copy_assoc` | `pick d ; pick 0` | `pick d ; dip 1 { pick d }` |
| `copy_comm` | `pick d ; pick d`, `d >= 1` | `pick (d-1) ; dip 1 { pick d }` |
| `copy_comm_inv` | `pick (d-1) ; dip 1 { pick d }` | `pick d ; pick d` |
| `merge_branch` | `B ; branch { A } { A }`, B yields bool | `B ; drop ; A` |
| `probe_tuple` | `tuple n ; pick 0 ; is_tuple` | `tuple n ; push true` |
| `probe_length` | `tuple n ; pick 0 ; tuple_length` | `tuple n ; push n` |
| `shortcut_and` | `dip 1 { P } ; and ; branch { A } { B }` | `dip 1 { P } ; branch { branch { A } { B } } { push true; and; drop; B }` |
| `fold_and_branch` | `push true ; and ; branch { A } { B }` | `branch { A } { B }`, and the `false` case decides `B` |
| `annihilate_and` | `P1 ; dip 1 { P2 } ; and ; drop`, both yield bool | `P1 ; drop ; P2 ; drop`, either dip order |
| `annihilate_equal` | `equal ; drop` | `drop ; drop` |
| `distribute_drop` | `branch { A } { B } ; drop` | `branch { A drop } { B drop }` |
| `float_drop` | `dip 1 { S } ; drop` | `drop ; S`, spliced |
| `discharge_length` | `pick 0; is_tuple; branch { pick 0; tuple_length; drop; A } …` | the re-check erased |
| `discharge_untuple` | `pick 0; tuple_length; push n; equal; branch { untuple n; drop^n; A } …` | the arm becomes `drop; A` |
| `hoist_probe` | a branch whose arm heads with a total probe, framed or not | the probe outside, a drop in the other arm |
| `probe_split` | `P ; branch`, P a total probe | `pick 0 ; P ; dip 1 { drop } ; branch` |
| `sink_probe` | `pick d ; dip k { pick j; P }`, `k >= 1` | `dip (k-1) { pick j; P } ; pick d'` |
| `dup_probe` | `pick d ; P ; pick (d+1) ; P` | `pick d ; P ; pick 0` |

`sink` is the interchange rule, and its side condition is the one piece of real
arithmetic here: writing `X`'s arity as `(n -> m)`, the dip's window must sit
entirely below everything `X` leaves behind — that is `k >= m` — and the same
window is `k - m + n` deep on the other side. One formula covers `push` (0→1),
`drop` (1→0), arithmetic (2→1), `pick d` (d+1→d+2), `roll d` (d+1→d+1) and a
nested dip alike.

`float` is the same law read from the other side, and its arithmetic is the
dual: swap `n` and `m` and each rule becomes the other. Where `sink` needs the
window to clear everything `X` *leaves behind*, `float` needs it to clear
everything `X` *consumes* — `j >= n` — so that `X`'s operands are entirely
inside the hidden region and `S` cannot be what produced them. The two are
inverses, so they must never share a `repeat`; `sink` is the normalizing
direction and `float` has no measure at all. It earns its place when a total
computation has to be delivered *to* somewhere rather than gathered up — see
"a construction is a proof" below.

`annihilate_drop` only fires for instructions that cannot panic: `push` and
`pick` cancel entirely, the five `is_*` predicates leave the drop behind
(they consume a value to make the dropped one), and `tuple n` spreads the drop
into `n` drops — dropping a built tuple is dropping its parts. `add; drop` is
deliberately not `drop; drop` — the add still rejects non-numeric operands, and
cancelling it would discard that check.

`pick_drop_to_roll` is where copying a value and then discarding the original
turns back into the roll it always was. `sink` cannot reach this one and should
not: the dip deliberately operates on the value the pick just produced, which is
exactly the interference the interchange rule forbids — `pick d` has arity
`(d+1 -> d+2)`, so `k >= m` is `d+1 >= d+2` and never holds.

At `d = 0` the answer is `roll 0`, which does nothing. `pick_drop_to_roll`
emits it anyway and lets `noop` remove it, so each rule states one law. That
pairing is why `cleanup` bundles them: neither finishes the job alone.

`distribute_branch` and `fold_branch` are the pair that shows why controlling
order matters. Distribution is not a simplification — it duplicates X on
purpose — but it puts X somewhere a rule can see it *in context*, and folding
is what then pays off. On a sample of the test corpus `fold_branch` fires **no
times at all** on its own, and **31 times** when `distribute` has run first.
Neither rule finds that alone, and no flag combination expresses "distribute,
then fold".

`fold_branch` matches only a literal `Bool`. The VM rejects a non-boolean
condition, so folding `push 1 ; branch …` would erase a panic rather than
preserve one — the same reason `annihilate_drop` will not touch `add`.

`merge_branch` is the other way a branch dies: not because its condition is
known but because its arms agree, so the branch decides nothing. It is what
finishes a derivation whose leaves have all become the same thing, and the
naive one-node statement `branch { A } { A } → drop; A` is unsound for the
same reason folding `push 1; branch` is — the `drop` it leaves accepts the
non-boolean the branch would have rejected. Seeing the node that produced the
condition is what licenses it, the same stance `bool_identity` takes, and the
arms are compared by effect rather than provenance, since two arms that do the
same thing rarely share an origin.

`inline` **splices**: the callee's body lands in the caller's sequence, with no
frame left behind. That matters more than it sounds, because rules only ever
see one sequence — leaving a `dip 0` wrapper would put the expanded code
somewhere no other rule could reach it, and `inline` would compose with almost
nothing. A `dip k` call for `k > 0` does keep its frame, since there the frame
is what the instruction means.

The cost is provenance: spliced code no longer says which sentence it came
from. That is exactly why nothing inlines by default — the un-expanded listing
names every call on one line, and you flatten only what you mean to.

## A block is not a call

Phase 4 gives a branch arm and a `dip N { ... }` body a `SentenceIndex` alike,
purely because it needs somewhere to put them. Neither is reachable by name, so
neither is a call: there is no call site for `inline` to open, and nothing for
the un-expanded listing to usefully name on one line. Both are therefore spelled
out by `build`, before any tactic runs.

```
      4 │ dip 1 → #676 <inline> {
      4 │   is_symbol
        │ }
```

Leaving these closed only meant that a rule wanting to look inside a dip had to
ask for an expansion that expands nothing — and worse, that `sink` would decline
to move one until you had. A `dip N` or `jump` naming a real sentence is a
different thing and stays a call: there the callee exists independently, `inline`
is a real choice, and the label is worth keeping. An inline block that would
recurse also stays a call, which is what it becomes at run time anyway.

```
$ rewrite tests 'State::check'                    #   48 lines, every call named
$ rewrite tests 'State::check' -t 'once(inline)'  #   71, one call opened
$ rewrite tests 'State::check' -t inline_all      # 1085, one flat sentence
```

Because splicing rescans where it landed, `each(inline)` already expands a
whole sequence transitively; `bu` is what additionally reaches into branch
arms. To expand *less*, use `once`, which takes a single call — and note that
it works on one sequence, so `repeat_n(k, once(inline))` counts calls at the
level you are looking at rather than descending into arms.

## Don't expand more than you are about to cancel

The size of an expansion is not a property of the callee. Opening one layer and
*folding what that exposed* before opening the next keeps a term small that
inlining eagerly does not:

```
$ rewrite tests emit_does_pre_and_post -t 'inline_all; distribute; cleanup'
49376 lines
$ rewrite tests emit_does_pre_and_post -t 'repeat_n(3, once(inline); distribute; cleanup)'
   42 lines
```

Same sentence, same rules, three orders of magnitude apart. The staging is what
does it: `distribute_branch` duplicates the continuation into both arms, so
every call still un-expanded when it fires gets copied along with everything
else, and expanding first means paying that cost on the largest term rather
than the smallest.

Note that `repeat(bu(each(inline); ...))` does *not* buy this, and neither does
`td` — both expand every call they can see before the folding rules get a turn,
which is the situation the interleaving was meant to avoid. Staging needs a
tactic that opens a bounded number of calls, which means `once` or `repeat_n`.

## Reaching one arm: `then`, `else`, `body`

`children` visits every child of every node. That is what a normalizing pass
wants and the opposite of what a targeted one wants, so it comes in narrower
flavours: `then` and `else` take a branch's arms one at a time, and `body`
takes dip bodies.

Staged inlining is what makes the difference concrete. `once` works on one
sequence, so the moment the only remaining calls are inside branch arms it has
nothing left to find, and no amount of `repeat_n` gets further:

```
$ rewrite tests emit_does_pre_and_post -t 'repeat_n(3,  once(inline); distribute; cleanup)'  # 42
$ rewrite tests emit_does_pre_and_post -t 'repeat_n(19, once(inline); distribute; cleanup)'  # 42
```

`then(once(inline))` is how you say which arm to open next, and it is the whole
difference between a plateau and a derivation.

These three partition `children` rather than overlapping it: `body` declines a
branch arm and `then`/`else` decline a dip, so `children(t)` is exactly
`then(t); else(t); body(t)`. A selector that finds nothing to descend into
reports "unchanged", the same stance `each` takes towards a rule that matches
nowhere — `then(t)` on a sequence with no branch is a no-op, not an error.

`flatten_call` does for a stray `dip 0` what `inline` does for a call. It is no
longer needed after inlining, which splices directly, but `sink` can still
produce one: `push 1; dip 1 { X }` becomes `dip 0 { X }; push 1`.

## Values, and why a literal is special

Everything above rearranges code without asking what a value *is*. The last four
rules do ask, and they all answer to one constraint: **an instruction that
rejects an operand is a check, and removing the check changes the program even
when it does not change the result.**

That is why `annihilate_drop` will not touch `equal; drop` while `fold_const`
folds `equal` happily. The objection in the first case is that an operand may
itself be a panic, which `equal` propagates and `drop; drop` would not — an
operator's panic branch is reachable whenever its operands are arbitrary. **A
literal is never a panic.** With both operands pushed right there the branch
cannot be taken, so the fold is an equality in the Z3 encoding and in the VM
alike, and the rule needs no view on which of the two is the real semantics.

The operators that reject ordinary values are still restricted: `and`/`or` fold
only on two booleans and the comparisons only on two numbers, because
`push 1; push 2; and` is a panic and `push false` is not. `equal` rejects
nothing, so it folds on any pair — which is what decides
`push idle; push thirsty; equal` and collapses a whole symbol decision tree,
since distinct symbols are already distinct structurally.

`bool_identity` is the one that needs a three-node window, and the reason says
something about how far two nodes can get you. `a && true = a` is a rewrite of
*this* program only when `a` is known to be a boolean, since `and` rejects
anything else; the two-node view `push true; and` cannot tell whether the value
underneath was ever checked. Seeing the node that produced it can. That test is
deliberately syntactic — a call to a sentence that happens to return a bool does
not count, because that is a fact about the library rather than about the node,
and `inline` is how you make the operator underneath visible.

Its absorbing cases go to `B; drop; push c` rather than to `push c`, for the
same reason the unit case needs `B` at all: `B` may panic, and `a && false` is
`false` only on the runs where `a` happened.

`cancel_tuple` goes one way only. `tuple n; untuple n` returns the stack to
where it started, but `untuple n; tuple n` is **not** a no-op — `untuple` is
the instruction that checks the shape, so cancelling that pair would accept
values the original rejected.

## A path condition can be a value

A branch may tell its arms what its condition was, and doing so needs no
context at all. The VM rejects a non-boolean condition, so an arm that runs at
all ran because the value was exactly `true` or exactly `false` — which is a
literal, and the arm can push it for itself. That is `retain_condition`.

This matters more than it sounds, because it is what lets a **path condition
travel as a value**. The alternative is a traversal that carries hypotheses
into arms, which would break the governing invariant below and would need every
reordering rule to fix up whatever the hypotheses were keyed to. Here the fact
rides in the sequence, and every rule that folds literals can already use it.

`specialize_equal` is the same idea for the shape that actually occurs, and it
refines at whatever depth the test looked: `pick d; push c; equal` leaves the
original `d` deep once the branch has popped the boolean, so the refinement dips
to exactly there.
Predicates in this language are written `pick 0; jump P::check; branch {...}`,
and the `type` sugar's decision trees are built out of
`pick 0; push <symbol>; equal; branch` — a *computed* condition, not a
duplicated one. The then-arm runs exactly when the copy compares equal to `c`,
so inside it the value on top **is** `c`. The else arm learns a disequality,
which has no literal form and is left alone.

The guard on `specialize_equal` is worth reading if you plan to write a rule
that refines something. The obvious statement of "already refined" — the arm
begins with `drop; push c` — oscillates, because the `push c` it introduces is
live code: `annihilate_drop` cancels it against a following `drop` and
`fold_const_unary` rewrites it into a different literal, after which the arm no
longer matches the guard and the rule fires again. **A guard survives its
neighbours only if it names something they cannot remove.** Guarding on the
leading `drop` works, because that is the arm's first node and the two-node
rules have nothing to pair it with — and it says the right thing anyway, since
an arm that opens by discarding the value has no use for a refinement of it.

One limitation to be clear about: `specialize_equal` refines the value *the
check is holding*, not the one the caller kept. Where a predicate consumes a
copy and the real code later destructures the original, those are different
stack slots and no refinement relates them. This looked like a separate
problem and turns out not to be one — the existing rules close it, by making
the test look at the original instead. Where the copy's creation is adjacent
to the test that consumes it — `pick 2; pick 0; push c; equal; branch` —
`copy_assoc` reframes the test's copy as a re-derivation from the original,
`float` walks that frame past the comparison (so the comparison consumes the
*created* copy), and `unfactor_branch` delivers the re-derivation into the
arms, where the then-arm's leading `drop` annihilates it. What remains is
`pick 2; push c; equal; branch` — the test now names the original's depth,
and the refinement lands on the slot the caller will actually destructure.
The else arm's head becomes the next test's `pick`, which re-forms the same
window one level down, so the dance walks a whole decision tree by itself.
`the_derivation_discharges_three_of_emits_four_panics` runs it on the real
corpus.

## Sharing, and the one thing that is still missing

`dup_natural` is duplication-naturality: computing `X` on a copy and then on the
original is computing it once and copying all `m` results.

```
pick 0; untuple 3; dip 3 { untuple 3 }   ==   untuple 3; pick 2; pick 2; pick 2
```

Three copies because the value came apart into three. At `m = 1` it is the
familiar `pick 0; X; dip 1 { X }` → `X; pick 0`. Panic behaviour is preserved
rather than merely respected: `X` runs on the copy first, so where the left side
panics it does so on exactly the value the right side hands to its single `X`.
`print` is excluded, being the one instruction for which running twice differs
in something other than the stack.

This is the law that ought to close the gap between a predicate and its caller,
because every predicate here is written `pick 0; jump P::check; branch {...}` —
the check consumes a *copy* and the real work destructures the *original*. And
it does close it, whenever the two occurrences are in one sequence.

**They are not.** There is a branch in between, and nothing in this rule set
moves code *out* of a branch arm except `factor_branch`, which needs both arms
to share it. Hoisting from a single arm is not merely missing:

```
branch { untuple 3; A } { B }   →   dip 1 { untuple 3 }; branch { A } { tuple 3; B }
```

would run `untuple 3` on the path that took the *other* arm, and `untuple` is
partial — so the rewrite invents a panic the original did not have. The
`untuple n ⊣ tuple n` pair looks like an iso and is only a *partial* one, and
the case that matters is exactly where the partiality bites. Whether the hoist
is safe depends on a guard several branches further out having already
established that the value is a 3-tuple, and that is a fact about a path, not
about a window.

So `unfactor_branch` goes the other way — pushing context *into* both arms,
which is always sound — and is the direction available today. It is the exact
inverse of `factor_branch`; never put the two in one `repeat`.

## A construction is a proof

The gap above looks like it needs a fact: *this value is a 3-tuple here*, known
several branches out and long since consumed. Supplying it by hand is enough —
`factor_branch` hoists the now-shared `untuple`, `sink` walks it back, and
`dup_natural` merges the two. But no window-local rule can establish it, and a
search that simply asserted it would be a rule saying *trust me*.

It does not have to. **The fact is already in the program and is merely being
thrown away.** Carry the *parts* forward instead of the value, and rebuild the
value where it is wanted. That is `rebuild_copy`:

```
pick 0; untuple n   ==   untuple n; (pick (n-1))^n; dip n { tuple n }
```

Instead of keeping the value and taking a copy apart, take the value apart and
rebuild the copy. Both sides leave `[x, e(n-1) .. e0]` and both panic on exactly
the inputs where `x` is not an n-tuple, so the rewrite asks nothing of `x` — but
it changes what the surviving `x` *is*, from an opaque value into a `tuple n`
applied to parts now on the stack. The rebuild is framed as `dip n { tuple n }`
rather than emitted with rolls because that rebuilds the lower copy where it
already sits, and arrives in the form `float` can move.

Now the value reaching the branch is a `tuple n` node. `tuple n` is **total**,
so `unfactor_branch` may push it into both arms without inventing anything, and
in the arm that takes it apart again `cancel_tuple` removes both. `float` is
what delivers it there:

```
$ rewrite … -t 'once(rebuild_copy); repeat(bu(each(float)));
              repeat(bu(each(unfactor_branch); each(cancel_tuple); cleanup))' --trace
  float              5
  cancel_tuple       1
  rebuild_copy       1
  unfactor_branch    1
```

Two `untuple`s become one, and **no rule ever needed to know the value's shape**.
A window that sees `tuple 3; untuple 3` needs to know nothing about where the
value came from: the shape is evident because the code in front of it built that
shape.

This is the shape of the bargain between a clever search and a dumb rewriter.
The search does not communicate a *fact*, which the rewriter would have to take
on faith — it communicates a *construction*, which the rewriter checks for
itself. If the search is wrong the rewrite simply does not fire; there is no way
to talk the rewriter into an unsound step.

### Getting the copy to where it is needed

`rebuild_copy` wants `pick 0; untuple n` adjacent, and in real code they are not:
the copy is made at the top of the caller and the `untuple` happens several
guards and two branches later. So the copy has to travel, and a bare `pick`
cannot travel at all — only a framed computation is something `float` can carry.

`copy_assoc` is what puts it in a frame:

```
pick d; pick 0   ==   pick d; dip 1 { pick d }
```

**Duplication is coassociative.** Making a third copy from the copy and making
it from the original are the same thing, because they are the same value.
`annihilate_drop`'s treatment of `pick; drop` is the counit law of the same
comonoid, and `pick 0; roll 1` becoming `pick 0` would be its cocommutativity.
Neither side is smaller — the point is purely that one of the copies is now
framed.

`float` declines to do this itself, and correctly: its side condition `j >= n`
is sufficient but not necessary, and two picks of the same slot commute even
though their windows overlap. A general rule failing to see a special case is
the usual reason a specific law earns its own entry.

From there the copy walks: `float` past each guard instruction,
`unfactor_branch` through each branch. That last one is why `unfactor_branch`
takes any `k >= 1` rather than only `k = 1` — `float` essentially never leaves a
computation at exactly depth 1, and restricting it would mean a computation
could only enter a branch it happened to sit immediately beneath.

The cost is that `float`, `rebuild_copy`, `copy_assoc` and `unfactor_branch` all
make the term worse on their own. None belongs in a normalizing pass, and none is in `all` or
`cleanup`. That is the right place for the division to fall: aiming them is the
search's job, and `once` and `repeat_n` are how it says so.

Note also what this does *not* need. There is no `assume` node, no hypothesis
threaded through the traversal, and no rule that reads a fact off its context.
The governing invariant below is untouched — every rule involved still depends
only on the sequence it is handed.

### How far the constructions reach: the emit derivation

The standing goal is `emit_does_pre_and_post ≡ drop; push true`, derived by
nothing but the rules above, and two corpus tests record how far that
currently gets. `the_derivation_discharges_three_of_emits_four_panics` is the
first act: open `is_state::check`, share the caller's copy through it, walk
the union's decision tree with the `copy_assoc`/`float`/`unfactor_branch`
dance so `specialize_equal` refines the *original*, then open `emit`
everywhere — on the three refined symbol paths `emit`'s decision tree folds
on literals and its `panic` arm folds away with it.

`the_derivation_reaches_a_panic_free_form` is the second: `shortcut_and`
expands one conjunction layer per round — never more than the round's folding
can cancel — which finally gives the union's *last* variant (compiled without
a branch of its own) an arm to learn in, and the fourth panic folds like the
others. The decided skeletons then drain: `fold_and_branch` takes the arm a
folded test chose, `merge_branch` removes branches whose arms have agreed
(`yields_bool` looks through a whole tree of arms for this), the annihilate
family peels retained check chains apart, and the discharge pair erases a
guard's re-check inside the window that holds the guard. **No panic survives**,
every firing passes `--check`, and the whole run is under a second.

What still stands between the panic-free form and `drop; push true` is one
residue, on the thirsty path: the postcondition re-checks `is_symbol` on
values whose *copies* the precondition checked, across branches on those
checks' results. The travelling rules exist and each step is sound —
`probe_split` turns a consuming check into a pick-probe with a deferred drop,
`hoist_probe` carries a probe out of either arm, `sink_probe` walks it left
past copy creations, `dup_probe` fuses two probes of one slot — and probes
demonstrably climb from the innermost arm to the sequence top. What has not
been found is a *composition* of phases that aims them without the phases
undoing each other: `unfactor_branch` re-buries what `hoist_probe` surfaced,
`sink` reassembles what `probe_split` opened, and the `n -> m` interchange
arithmetic is too coarse to walk a frame past a dead refinement that writes
into its window. The missing piece is orchestration — a search that aims what
exists — not a fact, and not a new kind of rule.

**Rules are not tactics.** They live in their own namespace and cannot be
aliased or defined; a rule has to be *placed* by `each` or `once`. Writing a
bare rule name where a tactic belongs is an error that tells you so.

## Combinators

| form | meaning |
|---|---|
| `each(r, ...)` | apply the rules at every position, to exhaustion |
| `once(r, ...)` | apply the first rule that matches, at the first position |
| `a; b` | in sequence |
| `a \| b` | the first branch that changes something |
| `try(t)` | `t`, treating failure as "changed nothing" |
| `repeat(t)` | until `t` stops making progress |
| `repeat_n(k, t)` | at most `k` times, stopping early if it settles |
| `children(t)` | to every child sequence, one level down |
| `then(t)`, `else(t)` | to one branch arm, one level down |
| `body(t)` | to every dip body, one level down |
| `bu(t)` | children first, then here |
| `td(t)` | here first, then children |
| `id`, `fail` | succeed changing nothing; fail (the only thing that does) |

`;` binds tighter than `|`, so `a; b | c` is `(a; b) | c`.

## Named tactics

`--tactics <file>` loads definitions; `--list-tactics` prints what is defined.

```
tactic mine = repeat(bu(try(each(sink)); try(each(fuse))));
tactic both = mine; factoring;
```

Definitions may not recurse, directly or mutually. That is deliberate: it makes
`repeat` the only unbounded construct in the language, so the fuel budget has to
backstop rule oscillation only, never arbitrary user loops.

The built-in prelude defines `inline_all`, `default`, `dips`, `unary`,
`factoring`, `annihilate`, `values`, `cleanup`, `distribute`, `flatten`, `all`
and `dip_normalize`. With no `-t` you get `default`, which is `id` — nothing is
expanded and nothing is rewritten. The first four plus
`dip_normalize` reproduce what the old `--dip-normalize`, `--factor-branches`
and `--annihilate` flags did.

`values` is the four value rules on their own. They are also folded into
`cleanup` and `all`, because folding and branch-elimination feed each other:
folding is what exposes the literal `fold_branch` needs, and dropping a branch
is what exposes the next thing to fold.

`distribute` and `flatten` are deliberately **not** part of `all` or `cleanup`: it makes the
listing bigger, which is the opposite of what those are for. Reach for it
when you want to see what a following instruction looks like inside each arm —
usually as `distribute; cleanup`.

## Four things that are easy to get wrong

**`bu` and `try` are total, on purpose.** `bu(t)` is `children(bu(t)); try(t)`,
not `children(bu(t)); t`. The strict version fails whenever `t` misses at the
root — which is nearly always — so `repeat(bu(X))` would stop after a single
pass even though a child had changed.

**`repeat` keys on progress, not on success.** It follows from the above: if
`repeat` stopped only on failure and `bu` never fails, `repeat(bu(X))` would
diverge for every `X`. A tactic that succeeds without changing anything is
`Unchanged`, and `repeat` treats that as done.

**A rule that matches nowhere is a no-op, not a failure.** `each` and `once`
report "unchanged" when they find no work, so `a; b` keeps everything `a` did
even if `b` has nothing to do. Reporting it as failure meant a sequence
silently discarded its own progress — `each(inline); each(flatten_call)` gave
back the original tree while `--trace` still said `inline` fired. Only an
explicit `fail` fails, which is also why `try` is almost never needed.

**`|` falls through on "did nothing", not just on failure.** The two coincide
for `each`, which only ever reports changed-or-failed. But every total tactic —
`repeat`, `bu`, `try`, `id` — reports "unchanged" when it had no work, and if
`|` treated that as a win then `a | b` would be unusable with any named tactic,
since they are all `repeat`s. `annihilate | factoring` has to reach `factoring`.

**`collapse` and `expand` are exact inverses.** Putting both into one `repeat`
does not terminate, and the language will let you write it:

```
$ rewrite tests foo -t 'repeat(bu(each(collapse, expand)))'
error: out of fuel after 51 rule firings.

The last 24 firings were:
  expand@1
  collapse@1
  expand@1
  ...
```

The budget is part of the semantics rather than a safety net, and the trace is
what makes an oscillation diagnose itself. Fuel is charged per rule *firing*,
globally: `each` terminates on its own and `repeat` only goes round again when
something changed, so a loop that never ends must fire without end.

## The governing invariant

**A tactic's result depends only on the sequence it is given, never on where in
the tree it is being applied.** Anything that would need to know its position —
a traversal-local visited set, say — belongs in the environment as a fact about
the whole library instead. This is what keeps rules unit-testable in isolation
and keeps `Failed` meaning the same thing everywhere.

Two consequences worth knowing: a rule cannot express a condition about its
context (`this dip begins a branch arm` is not sayable), and the entry stack
depth is tracked only by the printer, never by a rule.

Facts about the *library* are a different matter and do not break this — a
sentence's arity and its annotations are properties of the whole program, the
same wherever a rule meets them.

The invariant is also why nothing reaches across a frame. When you want that,
the answer is to remove the frame with `flatten_call` rather than to give a
rule the context — one rule that erases a boundary composes with everything,
whereas context-aware rules would each need their own notion of it.

## Recursion is refused, and no analysis is needed to spot it

The tool will not open a `#[recursive]` sentence:

```
$ rewrite tests recursion_and_returns
error: 'control_flow::recursion_and_returns' is #[recursive]
```

Deciding that takes **one annotation lookup, not a graph traversal**, and the
reason is worth knowing because it is a property of hanoi rather than of this
tool. `check_arities` refuses to compile a sentence that calls a `#[recursive]`
one without being `#[recursive]` itself, and a sentence inside a cycle cannot
escape the annotation either, since arity inference would detect the cycle and
refuse. So the annotation has already propagated transitively up the call graph
by the time anything here runs, and its *absence on a root is a proof that
expanding that root terminates*.

That claim is load-bearing, so it is checked rather than assumed:
`program::invariant::reaching_a_cycle_implies_the_recursive_annotation` computes
the real cycles over the whole test corpus and asserts every sentence reaching
one carries the annotation. The graph traversal survives only as that check —
the tool itself never runs it.

## Checking and tracing

- `--check` verifies that every rule preserves the net stack effect of the
  window it rewrote, and aborts naming the rule if not. Learning an arity that
  was previously unknown is allowed — `inline` does exactly that, since a
  `#[recursive]`-annotated sentence has no inferable arity as a call while its
  expanded body may well have one — but changing or losing one is a bug. It checks *net change*
  rather than full arity, because `annihilate_drop` legitimately lowers the
  input requirement: dropping `pick 2; drop` also drops the demand for three
  values that only the pick made.
- `--trace` prints how often each rule fired. This is the cheap way to answer
  "does this rule ever apply to real code", and the answers are not obvious:
  `annihilate_drop` fires on none of the 3526 sentences in `tests/`, while
  `pick_drop_to_roll` fires on a third of them — 11 times in `State::check`
  alone, which the listing shows as 1148 lines becoming 1092. Grepping the
  `.hana` sources for that pattern finds exactly one site; the compiled,
  inlined tree is where it actually lives. And `fold_branch` fires nowhere at
  all until `distribute` has run, then 31 times.
- `--fuel <n>` raises the budget when the work is genuinely large.
- `--stack` shows what each slot holds, with equal values sharing a name. See
  below.

## Seeing which slots hold the same value

The rules deliberately know nothing about values. Reading a derivation by hand
is a different job — the whole question is which slots hold the same value and
which hold a known one, and a column of depths cannot say. `--stack` adds a
symbolic view:

```
                             stack │ depth │ instruction
  ─────────────────────────────────┼─────────────────────────
                                 a │      1 │   untuple 3
                             e f g │      3 │   pick 2
                           e f g e │      4 │   pick 2
                         e f g e f │      5 │   pick 2
                       e f g e f g │      6 │   push symbol(Customer is idle)
                 e f g e f g 'idle │      7 │   equal
                       e f g e f h │      6 │   branch then → #668 {

  where
      e = a.2
      f = a.1
      g = a.0
      h = g == 'idle
```

`e f g e f g` is the sharing, visible at a glance: the check's copy and the
caller's parts are the same three slots. Constants show themselves, so a literal
that has reached a slot is obvious.

**A shared label means the values are equal.** The converse does not hold — two
slots that happen to be equal may show different labels, because the
interpretation lost track (a call's result is opaque, and where two branch arms
disagree the slots go fresh). Being vague is fine; being wrong is not, so the
view never merges two things it has not actually followed.

It is an abstract interpretation run *after* all rewriting, and no rule ever
consults it. That is why it is allowed to be as clever as it likes without
touching the governing invariant — it decides what to print, nothing else.
