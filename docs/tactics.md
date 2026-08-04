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
| `annihilate_drop` | `X ; drop`, `X : n -> 1` | `drop^n` |
| `annihilate_flagged` | `X ; drop ; drop`, `X : n -> 2` | `drop^n` |
| `pick_drop_to_roll` | `pick d ; dip (d+1) { drop }` | `roll d` |
| `noop` | `roll 0`, or an empty `dip` | nothing |
| `flatten_call` | `dip 0 { P }` | `P`, spliced in |
| `distribute_branch` | `branch { A } { B } ; X` | `branch { A X } { B X }` |
| `fold_branch` | `push c ; branch { A } { B }` | the arm `c` selects |
| `inline` | a call | the block it names, spliced in |
| `fold_const` | `push a ; push b ; op` | `push (a op b)` |
| `fold_const_unary` | `push a ; op` | `push (op a)` |
| `bool_identity` | `B ; push true ; and` | `B`, and the three other unit laws |
| `cancel_tuple` | `tuple n ; untuple n` | `push true` |
| `retain_condition` | `Y ; pick 0 ; branch { A } { B }`, `Y` yields a bool | `Y ; branch { push true; A } { push false; B }` |
| `specialize_equal` | `pick d; push c; equal; branch { A } { B }` | the same, with A as `dip d { drop; push c }; A` |
| `copy_const` | `push c ; pick 0` | `push c ; push c` |
| `dup_natural` | `pick 0 ; X ; dip m { X }`, `X : 1 -> m` | `X ; (pick (m-1))^m` (also under a retained copy) |
| `unfactor_branch` | `dip k { X } ; branch { A } { B }`, `k >= 1` | `branch { dip (k-1) { X }; A } { … }` |
| `rebuild_copy` | `pick 0 ; untuple n`, `n >= 1` | `untuple n`, then a branch on its flag |
| `copy_assoc` | `pick d ; pick 0` | `pick d ; dip 1 { pick d }` |
| `speculate_branch` | `branch { X; A } { B }`, `X : n -> m` total | `dip 1 { (pick (n-1))^n; X }; branch { dip m { drop^n }; A } { drop^m; B }` |

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

`annihilate_drop` fires on any operator that leaves exactly one value:
computing something and throwing it away is throwing away the operands
instead, so `add; drop` is `drop; drop` and `tuple 3; drop` is three drops.
`push` lands at zero drops, and `pick d` gets its own answer — no drops, since
it consumed nothing — because its arity `(d+1 -> d+2)` is not of that shape.

Only `print` is excluded, and not for a reason about failure: running it and
not running it differ in something other than the stack. `assert` and
`assert_eq` fall out on their own, leaving nothing on top for a drop to pair
with.

`annihilate_flagged` is the same law one output wider, and it exists because a
**fallible** instruction leaves its success flag alongside its value (see
[totality.md](totality.md)). `add; drop` is no longer an annihilation — it is
the old `add`, with the flag thrown away — so what cancels is `add; drop; drop`,
three nodes and one more than the first rule's window. It is not only about
flags: `pick 0` has arity `(1 -> 2)` and belongs there for the same arithmetic.

This pair used to be a single five-instruction whitelist, and `add; drop` was
deliberately *not* `drop; drop` — the add still rejected non-numeric operands,
and cancelling it would have discarded that check. The widening is not
academic: it fired on **none** of the corpus before, and the two rules together
now fire **17616 times across 721 sentences**.

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
is what then pays off. On `State::check` fully inlined, `fold_branch` fires
**no times at all** on its own and **32762 times** when `distribute` has run
first. Neither rule finds that alone, and no flag combination expresses
"distribute, then fold".

`fold_branch` matches **any** literal, not only a `Bool`. A branch takes the
then arm on `Bool(true)` and the else arm on everything else, so
`push 1; branch …` is decided just as firmly as `push false; branch …` — it
goes to the else arm. A *computed* condition still declines, which is the part
of the rule that was ever really about knowing something.

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

## Values, and why folding is just evaluation

Everything above rearranges code without asking what a value *is*. The value
rules do ask, and the ground under them has shifted: **every data operation is
total**, so an operator has no operand it could reject and no check a rewrite
could throw away. See [totality.md](totality.md) for the contract and the junk
table.

That makes folding *evaluation*. `fold_const` and `fold_const_unary` may
compute anything the VM computes, and their obligation is not a licence but an
agreement — they must answer exactly as the interpreter does, on junk as much
as on anything else. `push 1; push 2; and` folds to `push false` (neither
operand is `Bool(true)`), `push idle; push thirsty; less` folds to `push false`
(neither is a number), and `push sym; not` folds to `push true` (a symbol is not
`true`, so it is falsy). The definitions themselves live in `bytecode::value` —
`Value::truthy` and `numeric_cmp` — precisely so there is one of each rather
than one for the VM and one for the rewriter.

What survives is a different constraint, and a sharper one. **Truthiness is not
injective.** `and`, `or` and `branch` collapse every non-`true` value onto one
answer, so a rule that hands a value *back* still has to know it was a boolean
to begin with.

`bool_identity` is where that bites, and the reason says something about how far
two nodes can get you. `a && true = a` is a rewrite of *this* program only when
`a` is known to be a boolean — `and` no longer rejects a junk `a`, but it does
coerce it to `Bool(false)`, which is a different value even though it is the
same truth. The two-node view `push true; and` cannot tell what the value
underneath is; seeing the node that produced it can. That test is deliberately
syntactic — a call to a sentence that happens to return a bool does not count,
because that is a fact about the library rather than about the node, and
`inline` is how you make the operator underneath visible.

Its absorbing cases go to `B; drop; push c` rather than to `push c`, and that is
the one place a failure argument still applies: `B` may be a `panic` or an
`assert`, and `a && false` is `false` only on the runs where `a` happened.

`cancel_tuple` goes one way only, and neither change touched that. `tuple n;
untuple n` returns the stack to where it started and now says so, leaving the
literal `true` that `untuple` could not have failed to produce. The converse
`untuple n; tuple n` is **not** a no-op: it used to reject every value that was
not an n-tuple, then junk-normalized each of them, and now additionally strands
a flag. Still a real function, still not the identity.

## A path condition can be a value

A branch may tell its arms what its condition was, and doing so needs almost no
context: one node's worth. That is `retain_condition`, and it is written
`Y; pick 0; branch { A } { B }` — three nodes, where `Y` is something that
yields a boolean.

The `Y` is load-bearing. A branch decides on *any* value, taking the else arm on
everything that is not literally `Bool(true)`, so an else arm may perfectly well
run while the copy `pick 0` left behind holds a `42`. Telling that arm its
condition was `false` would be a lie about the value even though it is the truth
about the path. `Y` yielding a bool is what rules the case out — the same
predicate, and the same three-node window, that `bool_identity` needs for the
same reason.

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
stack slots and no refinement relates them. Sharing the two is a separate
problem.

## Sharing, and the one thing that is still missing

`dup_natural` is duplication-naturality: computing `X` on a copy and then on the
original is computing it once and copying all `m` results.

```
pick 0; untuple 3; dip 3 { untuple 3 }   ==   untuple 3; pick 2; pick 2; pick 2
```

Three copies because the value came apart into three. At `m = 1` it is the
familiar `pick 0; X; dip 1 { X }` → `X; pick 0`. Failure behaviour is preserved
rather than merely respected: `X` runs on the copy first, so where the left side
fails — `X` may contain an `assert` — it does so on exactly the value the right
side hands to its single `X`. `print` is excluded, being the one instruction for
which running twice differs in something other than the stack.

This is the law that ought to close the gap between a predicate and its caller,
because every predicate here is written `pick 0; jump P::check; branch {...}` —
the check consumes a *copy* and the real work destructures the *original*. And
it does close it, whenever the two occurrences are in one sequence.

**They are not.** There is a branch in between, and `factor_branch` — the only
rule that moves code *out* of an arm — needs both arms to share it.

The obvious hoist from a single arm does not work, and totality does not make it
work:

```
branch { untuple 3; A } { B }   →   dip 1 { untuple 3 }; branch { A } { tuple 3; B }
```

would run `untuple 3` on the path that took the *other* arm, where it
junk-normalizes a value that `B` then goes on to use — and `tuple 3` does not
put it back. The `untuple n ⊣ tuple n` pair looks like an iso and is not one.
It used to invent a panic there instead; the argument changed and the
conclusion did not.

## Speculation is cheaper than an inverse

**The hoist does not need an inverse. It needs a copy.** That is
`speculate_branch`:

```
branch { X; A } { B }
  ==
dip 1 { (pick (n-1))^n; X };  branch { dip m { drop^n }; A } { drop^m; B }
```

Run `X` on a *copy* before the branch, and let each arm throw away the half it
did not want. The losing path never gives up its own values, so nothing has to
be reconstructed and `untuple n` is asked nothing that `add` is not asked. The
`dip 1` is because the condition is still on top and `X` must not be handed it.

**This is what totalizing the VM actually bought.** The rule is sound only
because `X` cannot fail on the path that skipped it — which, for the `untuple`
case the sharing problem is entirely about, was false a week ago. Beyond that it
asks only that `X` have no effect but the stack (excluding `print`) and a
locally known arity (excluding calls, whose bodies may hold an `assert` several
frames down; `inline` is how you make that visible). A `dip` qualifies when its
whole body does, which is what lets a speculation climb out of *nested*
branches — the rule's own output is a dip, and it would otherwise strand itself
at the next branch out.

It declines when both arms open with the same effect: that is `factor_branch`'s
case, and it does it strictly better, with no copies and no drops.

So the direct route through the sharing problem is open:

```
speculate_branch   runs the arm's `untuple` on a copy, before the branch
sink               walks it left to sit on the check's `untuple`
dup_natural        merges the two
```

`dup_natural` learned one thing to close this. `sink` delivers the speculation
as `pick 0; dip 1 { pick 0; X }; X` — the frame carries a `pick 0` of its own,
because speculating had to copy — so the law is stated under a retained copy:

```
pick 0; dip 1 { pick 0; X }; X   ==   pick 0; X; (pick (m-1))^m
```

which is the same statement with the value surviving on the left of both sides.

### How far it actually gets

On the probe shape, all the way:
`the_direct_route_closes_by_speculating` takes two `untuple`s to one with no
reconstruction anywhere.

On `emit_does_pre_and_post` — where the copy is made at the top of the caller
and the `untuple` is two branches and several guards away — it does **not**
close. The speculation climbs out correctly, but each level wraps the previous
one in another frame, and `dup_natural` cannot see two occurrences through that
nesting. There the `rebuild_copy` chain is still the one that pays, taking seven
`untuple`s to two. Which route wins is a property of the shape, not of the
rules, and picking one is the search's job.

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
pick 0; untuple n
  ==
untuple n;
branch { (pick (n-1))^n; dip n { tuple n }; push true }
       { dip (n-1) { pick 0 }; push false }
```

Instead of keeping the value and taking a copy apart, take the value apart and
rebuild the copy. That changes what the surviving `x` *is*, from an opaque value
into a `tuple n` applied to parts now on the stack. The rebuild is framed as
`dip n { tuple n }` rather than emitted with rolls because that rebuilds the
lower copy where it already sits, and arrives in the form `float` can move.

The branch is the interesting part, and its history is the shortest argument
for the whole flags design. The rule used to be the bare equation, justified by
both sides panicking on exactly the inputs where `x` was not an n-tuple. Once
the operators became total there was no panic left to agree about and the two
sides visibly differed — the rule had been *relying* on partiality to hide a
normalization — so it grew a `tuple_length; push n; equal` guard to buy the
condition back, and an else arm that could only invent `n` copies of `()`.

Neither is needed now. **`untuple n` reports for itself**, so the condition is
already on the stack, and the else arm has something to say: the value `untuple`
could not take apart is still sitting in the deepest of the slots it filled. No
recomputation, no `is_tuple`, and both arms exact. The guard a rewrite needs is
the one the instruction already computed.

Now the value reaching the branch is a `tuple n` node. `tuple n` is **total on
the nose**, so `unfactor_branch` may push it into both arms without inventing
anything, and in the arm that takes it apart again `cancel_tuple` removes both.
`distribute_branch` is what brings the consumer into the guard's arms in the
first place, and `float` is what delivers the rebuild the rest of the way:

```
$ rewrite … -t 'once(rebuild_copy); distribute; repeat(bu(each(float)));
              repeat(bu(each(unfactor_branch); each(cancel_tuple); cleanup));
              all; flatten; cleanup'
```

Two `untuple`s become one, and **no rule ever needed to know the value's shape**.
A window that sees `tuple 3; untuple 3` needs to know nothing about where the
value came from: the shape is evident because the code in front of it built that
shape.

Distribution copies the consumer into *both* arms, so the off-guard arm arrives
carrying every `untuple` downstream of the rebuild — which would be a loss, if
anything were left to compute there. Nothing is: that arm holds n literal `()`s,
so `fold_const_unary` answers each `is_symbol` with `false`, `fold_const`
collapses the `and`s, and `fold_branch` picks the arm that never untuples at
all. **All three of those folds are things the old semantics declined to do.**
The guard totality forced is paid for by the folding totality enabled, in the
same derivation.

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
  `pick_drop_to_roll` fires on a third of the sentences in `tests/` — 11 times
  in `State::check` alone, which the listing shows as 1148 lines becoming 1092.
  Grepping the `.hana` sources for that pattern finds exactly one site; the
  compiled, inlined tree is where it actually lives. `fold_branch` fires nowhere
  at all until `distribute` has run, then thousands of times. And
  `annihilate_drop` fired on **none** of the corpus while it was a whitelist of
  instructions that cannot panic, and on 78 sentences once totality let it take
  any single-output operator — which is the cheapest available measurement of
  what that change was worth.
- `--fuel <n>` raises the budget when the work is genuinely large.
- `--stack` shows what each slot holds, with equal values sharing a name. See
  below.
- `--step` walks the derivation one rule firing at a time. See below.

## Walking a derivation: `--step`

`--trace` says which rules fired and how often; the listing says where the term
ended up. Neither says *when* the term stopped being the one you meant.
`--step` walks the derivation a firing at a time. Each step puts the tree as it
stood **before** the last firing beside the tree **after** it, so the only thing
on the screen is what that one rule did — and sketches the window the next rule
is about to match:

```
$ rewrite tests dip_hides_several_values -t dip_normalize --step
  stepping `dip_normalize` — 2 rule firings.
  ... the tree at step 0 ...
(rewrite 0/2) s

    step 0                      ┃   step 1  ·  sink@3
  ──────────────────────────────╂──────────────────────────────
    ⋮ 5 unchanged lines         ┃
    0 │ push 1                  ┃   0 │ push 1
    1 │ push 2                  ┃   1 │ push 2
    2 │ push 8                  ┃   2 │ push 8
  - 3 │ push 9                  ┃ + 3 │ dip 1 → #658 <inline> {
  - 4 │ dip 2 → #658 <inline> { ┃ + 3 │   add
  - 4 │   add                   ┃ + 3 │   drop
  - 4 │   drop                  ┃
      │ }                       ┃     │ }
                                ┃ + 2 │ push 9
    3 │ push 9                  ┃   3 │ push 9
    4 │ assert_eq               ┃   4 │ assert_eq
    2 │ push 8                  ┃   2 │ push 8
    ⋮ 3 unchanged lines         ┃

  step 1 of 2
  next   sink@2
           push 8 ; dip 1 { add ; drop }
        ⇒  jump { add ; drop } ; push 8
(rewrite 1/2)
```

There is the interchange rule doing its one job: the dip walked left past the
`push 9`, and came out one shallower on the other side because the push is no
longer under it. A rule firing is a splice of a few nodes, so showing the change
rather than the tree is what keeps that visible — the listing around it may be a
thousand lines, and one `inline` on a real sentence is thirty of them at once.

`list` shows the whole tree when the tree is the question, and `diff` goes back.
Step 0 has no firing behind it, so it shows the tree either way.

| command | meaning |
|---|---|
| `s`, `step [n]` | apply n more firings (default 1) |
| `b`, `back [n]` | undo n firings |
| `g`, `goto <n>` | the tree after exactly n firings |
| `c`, `continue` | run to the end of the derivation |
| `r`, `restart` | back to the tree the tactic starts from |
| `l`, `list` | show the whole tree instead of the change |
| `d`, `diff` | back to showing what the last firing changed |
| `t`, `trace` | the firing log around the cursor, and counts so far |
| `stack` | toggle the `--stack` column |
| `q`, `quit` | leave |

A bare newline repeats the last command, and end of input quits — so a session
can be piped in.

A step is **one rule firing, wherever in the tree it happened**. The `@n` beside
a rule is a position within its own sequence rather than a global one: two
firings reporting `@0` may be in different dip bodies. The diff above the prompt
is what says where.

The diff is textual, over the rendered listing, rather than structural over the
tree. That is a choice: a structural diff would have to decide what "the same
node" means across a rewrite that splices, reorders and reparents — which is the
question the rewriter is itself answering, so any answer here would be a second,
quieter opinion about it. Working on the listing also means a depth shifting by
one counts as a changed line, which is exactly what you want to see when the
firing was `sink`.

### Stepping by replaying

It steps by replaying, not by remembering. A rule is a pure function of the
window it is handed, and the search that places rules reads nothing but the
tree, so running the same tactic over the same sentence twice fires the same
rules at the same places in the same order. Step *n* is therefore "run it again
with a budget of n firings" — which is why stepping backwards costs exactly what
stepping forwards does, and why none of this needs an undo log, a snapshot, or
one line of special handling inside a rule.

The budget is not `--fuel`, and the difference is the point. Running out of fuel
is a failure and reports itself as one. Reaching the step budget makes every
further rule *decline*: `each` still walks to the end of its sequence and
`repeat` still asks once more, neither finds anything, and the traversal unwinds
normally — so what comes back is a whole tree rather than an error. Every
intermediate tree is a real one, net stack effect included.

What it costs is re-running the prefix, so walking to step *n* is quadratic in
*n*. That is the deliberate trade: a derivation worth reading by hand is tens of
firings long, and the alternative buys speed with a second notion of what a
rewrite is.

### A tactic that will not settle

This is what the stepper is most wanted for. `--fuel` reports an oscillation as
a list of recent firings, which tells you *which* pair of rules is undoing each
other; stepping shows you the term they are passing back and forth, and `goto`
puts you either side of it.

```
$ rewrite tests dip_hides_several_values \
    -t 'repeat(bu(each(expand, collapse)))' --fuel 5 --step

    step 4                        ┃   step 5  ·  expand@4
  ────────────────────────────────╂────────────────────────────────
    ⋮ 6 unchanged lines           ┃
    1 │ push 2                    ┃   1 │ push 2
    2 │ push 8                    ┃   2 │ push 8
    3 │ push 9                    ┃   3 │ push 9
  - 4 │ dip 2 → #658 <inline> {   ┃ + 4 │ dip 1 {
  - 4 │   add                     ┃ + 4 │   dip 1 → #658 <inline> {
  - 4 │   drop                    ┃ + 4 │     add
                                  ┃ + 4 │     drop
                                  ┃ +   │   }
      │ }                         ┃     │ }
    3 │ push 9                    ┃   3 │ push 9
    4 │ assert_eq                 ┃   4 │ assert_eq
    ⋮ 4 unchanged lines           ┃

  step 5 of 5
  next   the run ends here:
           out of fuel after 6 rule firings.
```

The census run happens once, before the prompt, which is how the stepper knows
how long the derivation is — and how it knows a run ends in failure. It walks
you up to the last firing before the failure and shows the error there. `--check`
failures land the same way.

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
