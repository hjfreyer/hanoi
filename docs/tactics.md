# Tactics

`bin/rewrite` — in the `rewrite` crate, beside `bin/prove` — works the **goal**
an `identity` states: two terms, and the claim that they are equal. A **tactic**
says how to rewrite a term, and is most of this document.

```bash
cargo run --bin rewrite -- tests state_check -t 'exact(unfold_all; dips)'
```

No *call* is opened unless you ask. A listing shows one sentence, naming every
call it makes on a single line; `unfold` is how you open one up. Blocks written
inline — branch arms and `dip N { ... }` bodies — are always spelled out,
because they are not calls.

**There is no way to name a bare sentence**, because everything this tool does
is about a goal. A term worth looking at is therefore a term worth stating an
identity over, and the cheapest one is reflexive: `tests/probes.hana` holds
`identity state_check { jump State::check } = { jump State::check };` for exactly
that. Three idioms come out of it, and they are worth knowing before the
examples below use them:

| what you want | what to write |
|---|---|
| the term, fully opened | `-t unfold_all` — it closes, and prints where the two sides met |
| what a tactic *did*, against where it started | `-t 'exact(t)'` — no inlining fallback, so the goal stays open and you get the diff |
| the derivation `t` produces | `-t 'normalize(t)'` — both sides driven the same way, so it always closes |

`-t` takes a **strategy**, which is a sequence of moves over the goal:
`cleanup ; rhs(unfold_all)` drives the left with one tactic and the right with
another, and `peel ; descend(then: cleanup)` narrows the goal and then decomposes
what is left. `--width <n>` widens each column of a side-by-side listing when the
elision took the part you wanted.

A run of this tool answers a question and forgets it. To write the answer down —
so that it is re-checked when the library changes, and so that something can
later build on it — prove the identity in the `.hant` beside the `.hana`. What
closes here is what goes in that file, character for character. See
`docs/identities.md`; `bin/prove` is the other binary in this crate.

## Two layers

The tool is split in half, and the split is the thing worth understanding
first.

**The lower layer is mechanical.** A small set of **equations** — each a pair of
program sequences asserted to behave identically — plus a **script** saying
which equation to use, with which arguments, at exactly which place, in which
direction. An **applier** consumes a script and a tree and performs the
rewrites, refusing anything that does not line up precisely. It searches for
nothing and guesses at nothing.

**The upper layer decides.** Matchers scan windows and *propose* steps;
combinators say in what order and where to look. Nothing up here rewrites a
tree — it only produces scripts, which the lower layer then applies.

Both layers are **blind**: a matcher reads one window of one term, and a tactic
threads a single tree. Neither can know what the term is being rewritten
*towards*. That is deliberate, and everything in this document stays inside it.
`bin/prove` adds a third layer on top — a **strategy**, which discharges a goal
by cutting it into smaller goals and handing each to an ordinary blind tactic —
and the direction of the dependency is what keeps the two layers here intact: a
strategy calls tactics, and nothing below it knows a goal exists. See
`docs/identities.md`.

So a run leaves behind a derivation:

```
$ rewrite tests a_value_tested_twice -t all --show-script
closed — 6 steps
...
  derivation — 6 step(s)
     1  retest -> @0
        pick 0 ; branch { drop ; push 1 } { branch { push 3 } { push 4 } }
     ⇒  pick 0 ; branch { drop ; push 1 } { drop ; push 4 }
     4  hoist <- @1
        branch { jump { drop } ; push 1 } { jump { drop } ; push 4 }
     ⇒  dip 1 { drop } ; branch { push 1 } { push 4 }
```

Applying that script to a fresh build reproduces the run exactly. That is
asserted by every engine test and swept over the corpus, and it is what makes
the script a derivation rather than a log written alongside one.

Why bother: an equation is a claim about the language and a search is a
heuristic about how to find work. Tangling them meant every equation was
written twice — once per direction — and carried a termination measure that had
nothing to do with whether it was true. Now a direction is something a *step*
says, and termination is entirely the generator's problem, because a script is
finite by construction.

## The equations

Twenty-two, plus one thing that is not an equation. `--list-rules` prints the
matchers that place them, which is not all of them — the last three have no
matcher yet, and are steps a script may name rather than shapes anything looks
for. Twenty-one of the twenty-two are axioms: `copy_const` is the constant case
of `copy_nat` and is kept only because it is one step where the derivation is
three.

| equation | law | notes |
|---|---|---|
| `collapse` | `dip k { dip j { A } }` = `dip (k+j) { A }` | forward is the old `collapse`; backward at the split `(1, k-1)` is the old `expand` |
| `elim_dip0` | `dip 0 { A }` = `A` | forward splices a frame that hides nothing; backward *introduces* a frame around a run |
| `interchange` | `X ; D_k` = `D_(k-m+n) ; X`, for `X : n -> m`, `k >= m` | forward is `sink`, backward is `float`. `D` is a dip at any depth, or a call that hides something |
| `fuse` | `dip k { A } ; dip k { B }` = `dip k { A B }` | backward splits one frame at a point the arguments name |
| `hoist` | `dip (k+1) { X } ; branch { A } { B }` = `branch { dip k { X } ; A } { dip k { X } ; B }` | forward is `unfactor`; backward is the last step of `factor` |
| `distribute` | `branch { A } { B } ; C` = `branch { A C } { B C }` | `C` is a whole sequence. Backward factors a shared *suffix*, which the old set could not do at all |
| `fold_branch` | `push c ; branch { A } { B }` = the arm `c` selects | selected by `truthy`, and `false` is the only falsy value, so `push 1; branch` takes the **then** arm |
| `eval` | `push v1 … push vn ; op` = the pushes of what `op` answers | subsumes the old `fold_const` and `fold_const_unary`. `tuple` and `untuple` are operators that answer, so they fold too |
| `annihilate` | `X ; drop^m` = `drop^n`, for `X : n -> m` | `X` is a whole sequence. Forward subsumes `annihilate_drop` (m=1), `annihilate_flagged` (m=2) and the case with no drops at all (m=0, where `branch { } { }` = `drop`); backward is `introduce`, below |
| `commute` | `roll 1 ; op` = `op`, for a commutative `op` | `roll 1` swaps the top two, and `add`, `multiply`, `and`, `or`, `equal` cannot tell. Forward is `comm`, backward is `swap` |
| `split_bool` | `pick 0 ; is_bool ; branch { branch { push true } { push false } } { }` = nothing | a boolean is either `true` or `false`. Backward it is a case split; forward is `unsplit_bool` |
| `counit` | `pick d ; drop` = nothing | copy, discard the **copy**. *Not* an annihilation: `pick d` is `(d+1 -> d+2)` |
| `counit_under` | `pick 0 ; dip 1 { drop }` = nothing | copy, discard the **original**. The other counit law; only at depth 0, since deeper it is a `roll` |
| `retest` | `pick 0 ; branch { branch { A } { B } ; R } { Q }` = `pick 0 ; branch { drop ; A ; R } { Q }`, and the mirror | the same value tested twice answers the same, so the other inner arm is dead. One equation read at either arm |
| `specialize_equal` | `pick 0 ; push c ; equal ; branch { A } { B }` = `… branch { drop ; push c ; A } { B }` | a value that tested equal to a literal **is** that literal. No side condition: `equal` is structural identity on every value the machine has |
| `copy_const` | `push c ; pick 0` = `push c ; push c` | |
| `copy_assoc` | `pick d ; pick 0` = `pick d ; dip 1 { pick d }` | neither side is smaller; the point is that one copy ends up **in a frame**, and a framed computation is one `float` can carry |
| `copy_nat` | `pick (n-1)^n ; X ; dip m { X }` = `X ; pick (m-1)^m`, for `X : n -> m` | copying is natural. Forward is common-subexpression elimination; the only law that needs `X` to be **deterministic** |
| `bool_result` | `op ; is_bool` = `op ; drop ; push true`, for an `op` that always leaves a boolean | the only fact here about an instruction's **codomain**, and the only one no rewriting could reach. `Instruction::yields_bool`, measured by `vm` |
| `cancel_tuple` | `tuple n ; untuple n` = `push true` | the flag is the whole residue. The converse order is not a no-op and has no equation |
| `roll_cycle` | `(roll d)^(d+1)` = nothing | a rotation of `d+1` things has order `d+1`. Backward it is the only way to put a roll into a term that holds none |
| `unframe` | `dip d { X } ; (roll (d+m-1))^m` = `(roll (d+n-1))^n ; X`, for `X : n -> m` | a framed computation is a rolled one. Forward brings the operands to the top; backward puts the answer back under a frame |
| `pick_roll` | `pick d` = `dip d { pick 0 } ; roll d` | copying from depth is copying at depth and rolling the copy up |

**`unfold` is not one of these.** That `Call { k, S }` may be replaced by `S`'s
body is not a law of the calculus — it is the axiom the *library* contributes by
defining `S`, and it says nothing about any other sentence. So it is a separate
kind of step, and the applier reads the body from the library itself: a script
names a sentence and never quotes it. Read backward it *folds*, contracting a
body back into a call, which the old rule set had no way to express.

### Adding one is adding an axiom

The set is meant to grow rarely, and "it would be convenient" is not enough.
The worked example is a law that looked essential and was not:

```text
pick (n-1)^n ; X ; drop^m  =  nothing            for X : n -> m
```

Compute on copies, discard the results, and the originals were never touched.
Read backward this is the only way to introduce work into a term at all — which
is how a cancelling pair gets in beside the value it will eventually meet. It
is also **derivable**: `n` backward `counit`s nest a run of picks against a run
of drops, and one backward `annihilate` turns the drops into `X`. So it is a
lemma for a generator to emit as one firing, not an axiom. See
`applier::tests::vacuous_is_derivable_from_annihilate_and_counit`, which runs
the derivation both ways rather than asserting the claim.

### The one that was worth adding: `copy_nat`

```text
pick (n-1)^n ; X ; dip m { X }  =  X ; pick (m-1)^m       for X : n -> m
```

Copy the inputs and run `X` on both the copy and the original, or run it once
and copy the outputs. `pick (n-1)` done `n` times duplicates the top `n` values
as a block — `a b` becomes `a b a b` — and the second application runs under
the first one's results, which is what the frame is for. Forward it is common
subexpression elimination; backward it delivers a second copy of a computation
to a place that needs its own.

**It is genuinely independent, and there is an argument rather than a failed
search.** Read an opaque `X` as a random oracle — every application answers
freshly — and every other equation in the set still holds. `annihilate` throws
the answers away, `interchange` reorders computations that cannot see each
other, and the rest never mention an opaque `X`. This one fails: the left side
runs `X` twice and gets two different answers where the right runs it once and
copies, and an `equal` afterwards can tell. No derivation from the others can
exist.

That argument is also the statement of what it assumes. **It is the only law
here that needs `X` to be deterministic**, the way `annihilate` and
`interchange` are the only two that need it to be total. It costs nothing
today, because the instruction set is pure and a sentence of arity `(n -> m)`
can see only the `n` values it is given — but an effectful instruction would
take this law with it and nothing else, so it is written down rather than
assumed.

Adding it demoted one: `copy_const` is the case `X = push c`. The `n = 0`
instance reads `push c ; dip 1 { push c }` = `push c ; pick 0`, and one
`interchange` and one `elim_dip0` turn the left side into `push c ; push c`.
See `applier::tests::copy_const_is_derivable_from_copy_nat`, which runs that
derivation both ways. It keeps its one-step matcher because `values` and
`cleanup` fire it constantly and three steps is three times the fuel, but the
set now rests on fifteen axioms rather than sixteen.

## Scripts

A step is a rule, a direction, and a place:

```
interchange -> [1.then, 2.body, 1.then] @2
```

The location reads outermost-first. `[1.then, 2.body]` means "the then arm of
the node at index 1, then the body of the node at index 2 within it", and `@2`
is where the window starts in the sequence that walk arrives at.

**A location addresses the tree as the preceding steps left it.** Locations are
not stable across a script — step 5 may name an index that did not exist when
step 4 was recorded — and that is not a defect but the reason a script is
cheaper than a search. What makes it safe is that the applier regenerates the
side it expects to find and refuses to splice unless the window matches, so a
stale path fails loudly instead of rewriting the wrong code.

A script also has a **file format**, which is that line with the arguments
written out:

```
annihilate(x = { equal }, n = 2, m = 1) -> [1.then, 2.body] @2;
```

`prove --emit` writes them and `bin/replay` checks them, with none of this page
involved — no tactic, no matcher, no fuel. That is the payoff of the split:
everything above is about *finding* a rewrite, and none of it is needed to check
one. See [docs/derivations.md](derivations.md).

### What the applier checks

Every application, live run and replay alike:

- the descent reaches a real node, of a kind that has the part named;
- the window is in range;
- the window matches the side the equation generates, compared **by effect** —
  provenance is not part of a term's identity, since two identical blocks
  compiled to different sentences never share a label;
- the equation's side conditions hold;
- with `--check`, the replacement leaves the stack as the window did.

**Nothing in a script is trusted.** Facts that originate in the library ride in
the arguments — the claimed arity of `X` in `interchange` and `annihilate` — and
are re-derived against the real program on every application. A step claiming
`add` is `(1 -> 1)` is refused however it came to be written, and the tree is
left untouched. The script communicates a construction; the applier checks it.

### A firing may be more than one step

`factor` — hoisting a prefix both arms of a branch share — used to be one rule
that knew a whole procedure. It is now three steps, each an instance of a law:

```
elim_dip0 <- [0.then] @0     wrap the shared prefix in a frame, in the then arm
elim_dip0 <- [0.else] @0     and in the else arm
hoist     <- @0              lift the two frames into one, in front of the branch
```

That is what the split buys. The old rule *asserted* that splicing a shared
prefix out was allowed; this spells out why, in laws that are individually
checkable. The fuel budget notices too — `factor` costs three, because it is.

## Matchers

One matcher per *search direction*, since a law read backward is a genuinely
different thing to look for even though the arithmetic is the same:

| matcher | width | places |
|---|---|---|
| `unfold` | 1 | opens a call |
| `collapse` / `expand` | 1 | the frame-nesting law, either way |
| `flatten` | 1 | `elim_dip0` forward |
| `fuse` | 2 | |
| `sink` / `float` | 2 | interchange, either way |
| `factor` / `unfactor` | 1 / 2 | hoist, either way (factor is three steps) |
| `distribute` | 2 | |
| `fold_branch` | 2 | |
| `eval0` / `eval1` / `eval2` | 1 / 2 / 3 | no operands, one, or two |
| `annihilate` / `annihilate_flagged` / `annihilate_void` | 2 / 3 / 1 | one output, two, or none |
| `comm` / `swap` | 2 / 1 | commutativity, either way |
| `split_bool` / `unsplit_bool` | 1 / 3 | the case split, either way |
| `introduce { .. }` | n | annihilate backwards — see below |
| `share { .. }` | n+\|X\|+1 | `copy_nat` forward — see below |
| `speculate { .. }` | 1 | hoist out of the one arm that has it — see below. `n + 4` steps, no new law |
| `lift` | 1 | the same move with the prefix **found** rather than named — see below. 4 steps, or `speculate`'s |
| `bool_result` | 2 | `op ; is_bool` forward; backward is `inv(bool_result)` |
| `bool_result_copied` | 3 | the same fact through a copy — `op ; pick 0 ; is_bool`, which is the guard `split_bool` leaves. 8 steps, no new law |
| `unframe` | 1 | takes a frame off, bringing the operands to the top — see below. 2 steps, no new law |
| `retest` | 2 | one arm per firing, then arm first; no backward reading |
| `specialize_equal` | 4 | writes the literal into the arm that tested equal to it; backward is `inv(specialize_equal)` |
| `counit_under` / `inv(counit_under)` | 2 / 1 | the other counit, found or *put in* |
| `counit` / `counit(d)` / `inv(counit(d))` | 2 / 2 / 1 | the copy-and-discard law: found, found at one depth, or *put in* |
| `copy_const`, `copy_assoc`, `cancel_tuple` | 2 | |

`inv(r)` is the rest of them: every backward reading that is not worth a name
of its own. See "reading an equation backwards" below.

A matcher checks its own side conditions, so anything it proposes is something
the applier accepts. That is swept: every matcher over a corpus of windows,
asserting nothing is ever refused.

Two of these need no coordination even though they look adjacent. `annihilate`
wants `X : n -> 1` and `counit` wants `pick d ; drop`; since `pick d` is
`(d+1 -> d+2)` it fails annihilate's arity requirement outright. The old code
had an explicit special case for exactly this.

### Reaching a value below the top

Every law about *what a value is* — `split_bool`, `bool_result`, `copy_const`,
`eval` — is stated about the top of the stack, because `branch` observes the top
and nothing else does. So a value held under a frame is out of all of their
reach, and the obvious fix is the wrong one twice over.

`body(t)` is not it. A rule does apply inside a frame, and sees the top of the
*inner* stack — but a `branch` inside a frame cannot show its two cases to the
code outside it, and there is no top-level branch equal to one. A case split at
depth is therefore an identity insertion that tells the continuation nothing:
sound, and useless.

Parameterizing the laws by depth is not it either. `split_bool(d)` would want
`bool_result(d)` to discharge its guard, which would want `copy_const(d)` to
read what it left, and each is the same fact restated in a new shape. The
namespace grows and nothing composes.

**The three roll laws move the value instead of the reasoning.** `roll d` lifts
the value at depth `d` to the top, `roll_cycle` is what lets one be written down
at all, and `unframe` is what a frame turns into. Applied to
`dip 3 { is_symbol }` they leave

```
untuple 3 ; roll 3 ; is_symbol ; …the split… ; roll 3 ; roll 3 ; roll 3
```

— the case analysis on a top-level `branch`, where `distribute` can push the
continuation into both arms and the value is a literal in each, and then three
rolls that carry that literal back down to the slot it came from. That is the
whole point: the fork has to happen where `branch` can express it.

`pick_roll` is the third because a literal at depth is read with `pick d`, which
every folding law is blind to. Opening it into `dip d { pick 0 } ; roll d` puts
the literal and its copy adjacent *inside* the frame, where `copy_const` fires
and `unframe` eats the leftover roll —
`applier::tests::copy_const_at_depth_is_derivable_from_the_roll_laws` runs that
derivation both ways. So `copy_const` needs no depth reading, and neither does
anything else.

No `unroll` instruction was needed. `roll d` rotates `d+1` values, so
`(roll d)^d` already inverts it, and `roll 0 = ε` is `roll_cycle` at `d = 0`
rather than a law of its own.

### Placing one: `unframe`

`unframe` has a matcher now, and what unblocked it was reading the other side.

```text
dip d { X } ; (roll (d+m-1))^m  =  (roll (d+n-1))^n ; X       for X : n -> m
```

The obstacle recorded here was that a matcher "can only fix one of `n` and `m`
before it looks" — true of one reading the **rolls**, since how many there are
is `m` and a width is fixed before looking. Reading the **frame** instead, `d`
is on the node and `n` and `m` are its body's arity, so the window is one node
and all three are known. The obstacle was in which side to search from.

The equation has rolls on both sides and a term usually holds none, so the
firing puts them in first — `roll_cycle` backwards is the only way to introduce
a roll at all, and it introduces a whole cycle, of which the unframing eats `m`
and leaves `d`:

```
$ rewrite mini unframing -t 'exact(must(once(unframe)))' --show-script
closed — 2 steps
     0  roll_cycle <- @1   (nothing)                     ⇒  roll 1 ; roll 1
     1  unframe    -> @0   dip 1 { push t2 ; equal } ; roll 1
                                                         ⇒  roll 1 ; push t2 ; equal
```

What that buys is the middle: `equal` is now at the top level with its result on
**top of the stack**, which is the window `split_bool` needs and could not reach
while the value sat under a frame. `identities::taking_a_frame_off` states the
claim and `a_framed_computation_is_a_rolled_one` runs both sides.

It declines `dip 0 { X }`, which is `flatten`'s and needs no rolls.

**It is not free.** Each firing pays `d+1` rolls, and nothing deletes a roll
except `roll_cycle` completing a full cycle — so a term driven to a fixpoint on
this grows with the depth of what it unwraps: `dip 8 { is_symbol }` comes out as
`roll 8 ; is_symbol ; (roll 8)^8`. It is in no default pass; aim it at the frame
whose operand you actually need.

**The other five readings are still unplaced.** `roll_cycle` forward is `d+1`
nodes wide, its backward reading has the "somewhere to stand" problem
`inv(counit(d))` has, and `pick_roll` is waiting for something to want it.

### Three matchers, one annihilation

`annihilate`, `annihilate_flagged` and `annihilate_void` are the same equation
read at `m = 1`, `2` and `0`. They are three matchers because a matcher's width
is fixed before it looks, and the width is `1 + m`.

The last of them is the one with **no drops to read**, so it recognizes `X` by
its arity alone: a computation that leaves nothing is exactly the discarding of
what it consumed.

```text
branch { } { }   ⇒   drop
```

That is the case that wanted it — two empty arms take the condition and do
nothing else — and empty arms are what `factor` leaves behind when the two arms
were the same *all the way down*. So `factoring; all` now takes the husk with
them:

```
$ rewrite demo probe -t factoring      # pick 0 ; dip 1 { drop } ; branch { } { }
$ rewrite demo probe -t 'factoring; all'                                 # drop
```

It reaches more than branches: any `(n -> 0)` node, including a call. A `drop`
is itself `(1 -> 0)` and is declined, or it would rewrite every one into itself
and report a change forever.

**It is not a new equation, and the number says it was not a corner either.** A
third of every annihilation over the admissible corpus is this case, and
nothing was looking for it — see
`tests::the_annihilation_with_no_outputs_is_a_third_of_them`.

## Reading an equation backwards: `inv`

An equation is true both ways, but *looking* for it is not one job done twice.
`sink` reads `X ; D` where `float` reads `D ; X`, and the arithmetic between
them runs the other way. So a backward reading is a real matcher and has to be
written — the question is only whether it deserves a name.

Some do. `sink`/`float`, `collapse`/`expand`, `comm`/`swap` are pairs anyone
working here talks about separately, and naming them is right. The rest are
not: `unfuse`, `undistribute`, `unflatten` are words invented to fill a table,
and every one added is another entry in a namespace that has to be memorized.

```
each(inv(fuse))          each(inv(distribute))         at(2, inv(flatten))
```

`inv(r)` is `r`'s equation, read the other way, wherever a rule name goes. It
composes — `inv(inv(sink))` is `sink` — and when the reading already has a
name, that is exactly what you get, so `inv(sink)` *is* `float`.

Six readings exist only this way, and each is a capability the tool did not
have:

| | |
|---|---|
| `inv(flatten)` | `A` = `dip 0 { A }` — put a frame round a bare node so the movement laws can carry it. `factor`'s first two steps |
| `inv(fuse)` | split one node off the front of a frame's body, the way `expand` takes the canonical split of `collapse` |
| `inv(unfactor)` | lift a frame **both arms open with** out in front of the branch. `factor`'s third step, at any depth rather than only `0` |
| `inv(distribute)` | factor the longest shared **suffix** out of both arms — the end of a branch `factor` cannot reach, since it only ever worked on prefixes |
| `inv(copy_const)` | `push c ; push c` = `push c ; pick 0` |
| `inv(copy_assoc)` | take the second copy back out of its frame |
| `inv(introduce { X })` | `X ; drop^m` = `drop^n` — `annihilate`'s law reading a whole *term*, where `annihilate` reads a single node |

### Putting work where there is nothing to match

Every introduction so far has stood on something. `introduce { X }` needs the
drops already there; `inv(flatten)` needs a node to wrap; `share`'s backward
reading needs the computation it un-shares. None of them can put code at a
position that holds nothing to match.

`counit` is the law that can — `pick d ; drop` = nothing, so backwards it puts
a copy-and-discard anywhere at all. What stopped it was not the empty side but
the **`d`**: no window can say which value to copy. So the tactic says it.

```
$ rewrite demo probe -t 'must(at(1, inv(counit(0))))' --show-script
     0  counit <- @1
        (nothing)
     ⇒  pick 0 ; drop
```

`counit(d)` is the forward reading narrowed to one depth, and `inv` flips it
like any other pair. A rule taking a number reads the way `at(n, r)` does, and
`counit` is the only one that takes one.

**It inserts *before* the window** and reads one node purely to have somewhere
to stand — the same arrangement `split_bool` uses, and for the same reason: an
equation whose other side is empty has no window to recognize. The same
limitation follows for both, that neither can insert past the last node of a
sequence.

The copy is the point. A cancelling pair beside a value is how a copy of that
value gets somewhere it is wanted, and `introduce` then turns the `drop` into a
computation — which together spell out the vacuous law in the tactic language,
where it belongs, since it is a lemma rather than an axiom:

```
$ rewrite demo probe -t 'at(1, inv(counit(0))); at(2, introduce { pick 0 })'
   1 │ pick 0        ⎫
   2 │ pick 0        ⎬  pick (n-1)^n ; X ; drop^m  =  nothing
   3 │ drop          ⎪
   4 │ drop          ⎭
```

### When there is no backward reading

Five rules have none, and asking says why rather than matching nothing:

```
$ rewrite tests pair_check -t 'each(inv(cancel_tuple))'
error: `cancel_tuple` has no backward reading
  | each(inv(cancel_tuple))
  |      ^^^^^^^^^^^^^^^^^
  = help: the backward side of `cancel_tuple` is `push true`, which does not
          say what `n` was — a tuple of any width leaves the same flag
```

Two things put a reading out of reach, and they are worth telling apart:

- **It would have to invent, not recognize.** `inv(eval1)` would need the
  operator that produced the literal, and `inv(fold_branch)` the arm that was
  not taken. Nothing in the window says either, and nothing you could write
  would either — the term that made it right would be a different rewrite.
- **An argument is not recoverable from the window.** `cancel_tuple`'s `n`,
  above. This is the weaker obstacle of the two, and `counit` is what shows it:
  it was on this list until `inv(counit(0))` let the tactic name the `d`. The
  same could be done for `cancel_tuple` the day something wants it.

Two more are refusals that point somewhere: `inv(annihilate)` is the
introduction rule and has to say what to conjure, so it is
`introduce { ... }`; and `factor` is three steps of two different equations, so
there is no single one to reverse — `inv(unfactor)` is the last of the three.
`inv(unfold)` is the real gap: folding a body back into a call is expressible
as a step, but nothing looks for it, because a window does not say which
sentence to fold into.

**Nothing needs to, as it turns out.** A fold script is an unfold script read
backwards, and `rule::invert` is that reading — reverse the order, flip every
direction. So the one place that wants folding gets it without a matcher:
`bin/prove` compares an identity's two sides up to inlining by unfolding both
and inverting the right-hand side's script, which lets a right-hand side be
written as the call it is rather than pasted out. The gap is in *searching*, and
a generator that knew where it was going would not be searching. See
`docs/identities.md`.

**Every matcher has to answer.** `Matcher::inverse` has no default
implementation, so adding a rule means saying what its backward reading is or
why there is not one — a new rule cannot quietly have none.

### They are still opposite readings

`inv(r)` and `r` are one equation, so they oscillate: the warning about
`collapse`/`expand` in one `repeat` covers `fuse`/`inv(fuse)` and
`distribute`/`inv(distribute)` exactly as much. Most of the `inv` readings also
grow the term and have no measure at all, which is what `once`, `at` and a
descent are for.

## Saying what code to create

Every matcher above rewrites what it found, so what it produces is a function of
the window. An **introduction** has nothing to read: `drop` says nothing about
which computation ought to appear in front of it. The code has to be written
down, and the tactic expression is where.

```
once(introduce { pick 0 })
```

That is `annihilate` read backwards. The term names an `X : n -> m`; the matcher
looks for `n` drops and replaces them with `X ; drop^m`. Both sides discard
exactly the same `n` values, so the program means what it meant — but it now
contains `X`, which nothing in the window could have supplied.

**What it is for.** `factor` needs *both* arms of a branch to share a prefix.
When only one does, give the other the missing code in a place where it provably
costs nothing, and the two arms now share it:

```
$ rewrite probe test_always_true -t 'else(once(introduce { pick 0 })); factoring' --show-script
  derivation — 4 step(s)
     0  annihilate <- [2.else] @0
        drop
     ⇒  pick 0 ; drop ; drop
     1  elim_dip0 <- [2.then] @0
     2  elim_dip0 <- [2.else] @0
     3  hoist <- @2
        branch { jump { pick 0 } ; … } { jump { pick 0 } ; … }
     ⇒  dip 1 { pick 0 } ; branch { … } { … }
```

The copy has been hoisted out of both arms, which is the move the old rule set
could not reach at all.

### Running one computation instead of two

`share { X }` is the other rule that takes a term, and it takes one for a
sharper reason. `introduce`'s window says nothing about what to conjure;
`share`'s window cannot say what `X` **is**. For a run of nodes there is
nothing to mark where the computation begins, and the number of `pick`s in
front of it is `X`'s own input arity — which the matcher has to know before it
can even ask for a window, since a matcher's width is fixed before it looks.

```
$ rewrite demo twice -t 'must(once(share { jump classify }))' --show-script
   0 │      1 │ jump → #0 classify
   1 │      1 │ pick 0

  derivation — 1 step(s)
     0  copy_nat -> @0
        pick 0 ; jump → #0 ; dip 1 { jump → #0 }
     ⇒  jump → #0 ; pick 0
```

Backwards — `inv(share { X })` — it un-shares, running `X` a second time
rather than copying what it left. That is how a computation reaches a place
that needs its own copy, and unlike `inv(annihilate)` the second copy is
provably the same value as the first.

### Hoisting out of the one arm that has it

`factor` needs *both* arms to share a prefix. `speculate { X }` is the move for
when only one does, in a single firing:

```text
branch { pick (n-1)^n ; X ; B } { C }
  =  dip 1 { pick (n-1)^n ; X } ; branch { B } { drop^m ; C }
```

```
$ rewrite demo spec -t 'must(once(speculate { equal }))' --show-script
   0  counit     <- [1.else] @0    (nothing)   ⇒  pick 1 ; drop
   1  counit     <- [1.else] @1    (nothing)   ⇒  pick 1 ; drop
   2  annihilate <- [1.else] @2    drop ; drop ⇒  equal ; drop
   3  elim_dip0  <- [1.then] @0    ⎫
   4  elim_dip0  <- [1.else] @0    ⎬ factor, with the prefix named
   5  hoist      <- @1             ⎭
   ⇒  dip 1 { pick 1 ; pick 1 ; equal } ; branch { and } { drop ; not }
```

**It is shorthand, not a law.** Every step is an equation the set already had:
what it conjures into the other arm is the *vacuous* identity, which is a lemma
— `n` backward `counit`s nest a run of picks against a run of drops, and one
backward `annihilate` turns the drops into `X`. Written out it is
`inv(counit(d))` ×n, then `introduce { X }`, then `factoring`; the matcher just
does it in one firing with the prefix named rather than found.
`tests::speculating_is_what_the_three_rules_do_written_out` holds the two
routes to the same answer.

**The copies are what make it sound.** `X` runs on the path that did not want
it, but only ever on copies of the operands — the losing arm drops the results
and carries on with the values it always had. So `X` needs no inverse, and
nothing is asked of it beyond the totality the precondition already gives.

Two things it does that the hand-written version cannot. It **names the
prefix**, where `factoring` takes the longest shared run and will happily
swallow more than you meant once the conjured drops line up with what follows.
And it reaches an arm that is **empty**: `inv(counit(d))` needs a node to stand
in front of, where a planned step can name position 0 of a sequence with
nothing in it.

It declines when *both* arms open with the prefix — that is `factor`'s, and
factoring needs no copies and no drops. It has no measure and grows the term by
the frame and the `m` drops, so it is in no default pass; but it cannot fire on
its own output, since the arm it rewrote no longer opens with the prefix and
the other now opens with drops.

### Emptying the arms: `lift`

`speculate { X }` and `introduce { X } ; factoring` are both **aimed**: the
prefix is written into the tactic expression, which is one line per firing and a
rewrite of every one of them when the library moves underneath. `lift` is the
search that places them, so that "get every computation out of the arms it is
buried in" is a pass rather than a transcript.

It reads an arm's longest **branch-free** prefix `X : n -> m` and takes the
first of two routes to the same shape:

```text
branch { X ; B } { drop^n ; C }        =  dip 1 { X } ; branch { B } { drop^m ; C }
branch { pick (n-1)^n ; X ; B } { C }  =  dip 1 { pick (n-1)^n ; X } ; branch { B } { drop^m ; C }
```

The first is the cheaper one and is tried first. The other arm was going to
discard those `n` values anyway, so `annihilate` read backwards stands `X` in
front of the drops it already has, and the two arms now share a prefix that
`factor`'s last three steps lift out — four steps, nothing copied, nothing left
behind. The second is `speculate`, for an arm that computes on copies where the
other has no drops to stand in.

**Why the prefix has to be branch-free.** A branch is the one node whose arms
cannot see out of it, so lifting one would mean lifting both of its arms with
it. Stopping in front of it is also what makes the pass terminate: the arm that
was rewritten now opens with that branch, so `lift` cannot fire on it again.

**Why `drop` and `pick` are not lifted.** They say *which* values a branch is
choosing between rather than computing anything with them — and `drop^m` is
exactly what the last firing put into the other arm, so a rule that read those
back out would take turns with itself forever.

The measure is real, and it is the number of non-trivial nodes inside branch
arms weighted by how many arms deep each one sits. A frame is not a level: `X`
moving from inside an arm into a `dip 1 { X }` in front of the branch is `X`
leaving that arm, which is the whole point. `tests::\
lifting_empties_the_arms_of_the_barista_probe` measures it over the corpus
rather than asserting the shape.

`lifting` is the pass, and it alternates with the frame laws — every firing
leaves a `dip 1 { X }` behind, and collapsing and sinking those is what lets the
next one see a prefix rather than a pile of frames:

```
$ rewrite tests emit_pre_and_post -t 'exact(unfold_all; lifting)' --trace
  lift               92
  sink               50
  unfold             10
  factor              3
  collapse            1
```

The histogram is in **steps**, as everywhere else, so that is twenty-three
`lift` firings at four steps each and one `factor` at three.

That term is a precondition, a computation and a postcondition, and every
condition in it is buried in an arm of the test before it. What comes out has
all four state comparisons in one frame at the top and branch arms holding
nothing but branches, drops and the literal each one selects:

```
   0 │      1 │ pick 0
   1 │      2 │ dip 1 {
   0 │      2 │   untuple 3
   1 │      5 │   dip 1 { pick 0 ; push state::thirsty ; equal }
     │        │ }
   2 │      6 │ untuple 3
   3 │      9 │ dip 1 {
     │        │   …the four comparisons, nested one per else arm…
   4 │     12 │   push state::idle
   5 │     13 │   equal
     │        │ }
   4 │     12 │ branch then {
   0 │     11 │   branch then {
   0 │     10 │     drop
   1 │      9 │     drop
   2 │      8 │     drop
   3 │      7 │     push true
```

**What it cannot reach.** A prefix that *consumes* values the other arm still
needs can only be lifted onto copies, and the copies have to be paid for:
`pick (n-1)^n ; X ; dip m { drop^n }` = `X` is what would license it, which is
one `interchange` and then `pick (n-1)^n ; dip n { drop^n }` = nothing — which
is `counit_under` at `n = 1` and a **roll** for anything above it. That is
`pick_drop_to_roll`, on the list under "what is not here yet", so an arm that
builds a value out of operands the other arm goes on to use keeps its work. In
the term above that is `emit`'s answer and nothing else.

### Terms

A term is a run of instructions in braces. `pick n`, `roll n`, `tuple n`,
`untuple n`, `push <int|true|false|"const string"|symbol>`, `dip n { ... }`,
`branch { .. } { .. }`, `jump <sentence>`, and the argument-free operators
(`drop`, `not`, `and`, `equal`, `is_bool`, `add`, …). `--list-rules` prints the
list.

Every instruction is spellable, which was not always so: `panic`, `assert` and
`assert_eq` were left out on purpose, being the three that could fail. They are
gone from the language now, so there is nothing to leave out.

**A branch used to be absent too**, on the grounds that it needs two blocks and
a condition and so reads as a program rather than a term. That was wrong about
the condition: a `Node::Branch` carries only the two arms, and the condition it
pops is whatever the stack already holds — so it is a node like any other, of
arity `(n+1 -> m)`. Excluding it left a hole exactly where the last equation
landed: `annihilate` at `m = 0` turns `branch { } { }` into `drop`, and nothing
could write the term to read that backwards.

```
$ rewrite demo just_drop -t 'must(once(introduce { branch { } { } }))'
   0 │      1 │ branch then → <term> {
     │        │ } else → <term> {
     │        │ }

     0  annihilate <- @0
        drop
     ⇒  branch { (nothing) } { (nothing) }
```

Both arms have to leave the same amount behind, which is what the arity checker
asks of real code and is checked when the tactic is compiled. Nothing
downstream would catch it otherwise — a node's arity is read off whichever arm
answers first, so a term that broke it would put a program into the tree that
could not have been compiled, and the tree would be wrong about itself.

Code written in a tactic is labelled `<term>` in the listing, the way phase 4
labels an inline block `<inline>`. Provenance is not part of a term's identity,
so it never affects what matches.

**Two things in a term reach outside it**, and both are resolved the way the
command line resolves a sentence: an exact name, or an unambiguous trailing
part of one.

`jump <sentence>` is a call. A term used to hold none because there was nothing
for one to name — the code is written in the tactic rather than compiled from a
sentence — but `share` is about running *a function* twice, and the function
has a name. Sentences also answer to an index.

`push <symbol>` is a symbol, by fully qualified name: `push
queue::State::Idle::tag`, or `push Idle::tag` where that is unambiguous. A
symbol cannot be built from its text — `Symbol` compares by `id`, so two
declarations reading the same are different symbols — so this looks the real
one up and refuses a name that denotes none.

```
error: No symbol matching 'std::io'. Symbols:
  std::io::io
  std::io::stdout::putch
  std::io::stdout::stdout
  | once(introduce { push std::io equal })
  |                       ^^^^^^^
```

A symbol prints as the fully qualified name it was declared under, so a name
read off a listing is a name that resolves. A **const string** is the opposite
case and reaches outside nothing: it is exactly its text, so `push "hello"`
writes one down and needs no program at all.

A term's arity is worked out when the tactic is compiled. From the term alone
where it names nothing, which is what lets the prelude be checked with no
program loaded; from the library where it says `jump`, which is why a term that
names a sentence is refused unless there is one. Two terms are refused at
compile time rather than at run time:

- one whose arity is unknown, since there would be no saying what it discards;
- one that **consumes nothing**. `push 7` would match a window of no nodes,
  which is every position, so `each` would never move past the first — and this
  law discards whatever the term produces, so it could only ever become
  `push 7 ; drop`, which no later step can use.

### Commutativity, and what the set is

`comm` deletes a swap that a commutative operator cannot see:

```
roll 1 ; and   ⇒   and
```

The set is `add`, `multiply`, `and`, `or` and `equal`. It lives on the
instruction — `Instruction::commutative` — rather than in the rewriter, for the
same reason `op_arity` and `truthy` do: a second copy of the list would be a
silent hazard. **`vm` measures it** rather than restating it, running every
binary instruction on every pair of value shapes both ways round and holding the
list to what it finds.

That measurement earned its keep immediately. `assert_eq` — an instruction the
language has since dropped — looked commutative, failing exactly when `a != b`,
which is symmetric. It was not: the diagnostic it failed *with* named the
operands in the order given, so the two readings were observably different.

The flag a fallible operator leaves is symmetric too, so this holds for `add` on
operands it cannot add: `0, false` either way round.

`swap` is the backward reading, putting a `roll 1` *in* so that what sits
underneath the operands can be rearranged to line up with something else. It has
no measure and grows the term — its output still contains the operator it
matched, so `each` would put a second `roll 1` in front of it and keep going.
Aim it, as with `introduce`.

### An arm knows its own condition: `retest`

```text
pick 0 ; branch { branch { A } { B } ; R } { Q }  =  pick 0 ; branch { drop ; A ; R } { Q }
pick 0 ; branch { P } { branch { C } { D } ; R }  =  pick 0 ; branch { P } { drop ; D ; R }
```

The condition is a copy, so the arm the outer branch took already decides the
inner one: in the *then* arm the value is truthy and the inner branch goes
then, in the *else* arm it is `false` and the inner branch goes else. The other
inner arm cannot run.

One equation read at either arm, so it fires when only *one* arm opens with a
branch. Both arms and it fires twice, and `factor` and `counit_under` finish:

```
$ rewrite demo four_arms -t all --show-script
   0  retest -> @0    pick 0 ; branch { branch { push 1 } { push 2 } } { branch { push 3 } { push 4 } }
                   ⇒  pick 0 ; branch { drop ; push 1 } { branch { push 3 } { push 4 } }
   1  retest -> @0 ⇒  pick 0 ; branch { drop ; push 1 } { drop ; push 4 }
   2  elim_dip0 <- [1.then] @0            ⎫
   3  elim_dip0 <- [1.else] @0            ⎬  factor
   4  hoist     <- @1                     ⎭  ⇒ dip 1 { drop } ; branch { … } { … }
   5  counit_under -> @0                     ⇒ branch { push 1 } { push 4 }
```

**Why the inner branch.** It is not an arbitrary restriction. Inside the then
arm the value is known only to be **truthy**, not what it is — replacing it
with `push true` would be wrong, since `is_int` answers differently on `42`
than on `true`. A branch is the only construct that observes exactly
truthiness, so it is the only thing the law can say anything about. (The else
arm knows more, since `false` is the unique falsy value: there the value is a
literal. Stated that way the law is more general on that side and grows the
term, where this direction shrinks it.)

**What is derivable, and is therefore not in the law.** When the two inner
branches are *the same*, no axiom is needed:

```
$ rewrite demo same_arms -t 'bu(each(inv(distribute))); cleanup' --show-script
   0  distribute <- @1   ⇒  branch { (nothing) } { (nothing) } ; branch { push 1 } { push 2 }
   1  annihilate -> @1   ⇒  drop
   2  counit     -> @0   ⇒  (nothing)
```

`inv(distribute)` factors the shared inner branch out as a suffix, which leaves
`branch { } { }` for `annihilate` at `m = 0` and then `counit`. So the whole
content of `retest` is that the **off-diagonal arms are dead** — and nothing
reaches that, because an arm cannot see the branch it is inside. Driving it
through `split_bool` stalls in the same "not a bool" arm that `bool_result`
does, holding the original problem verbatim.

### The value an arm tested equal to: `specialize_equal`

```text
pick 0 ; push c ; equal ; branch { A } { B }
  =  pick 0 ; push c ; equal ; branch { drop ; push c ; A } { B }
```

`retest`'s sibling, and between them they cover the two ways an arm can learn
its own condition. A branch observes **truthiness** and nothing else, so what
`retest` recovers is which way a second branch goes. `equal` observes the
**whole value**, so what this recovers is the value — and writing it down is
what turns something opaque into a literal `eval` can read.

```
$ rewrite mini spec -t 'exact(must(once(specialize_equal)); values)' --show-script
closed — 2 steps
     0  specialize_equal -> @0   branch { push t1 ; equal } ⇒ branch { drop ; push t1 ; push t1 ; equal }
     1  eval             -> …    push t1 ; push t1 ; equal  ⇒ push true
```

**The `then` arm only.** The `else` arm knows the value is *not* `c`, and no
equation can use a negative fact — there is nothing to write in place of the
value. So this is one equation read at one arm where `retest` is read at either.

**It is an axiom, and the first here about what an instruction *computes*.**
`bool_result` is about a codomain and `eval` is evaluation; nothing in the set
relates `equal`'s answer to its operands, and no rewriting reaches it —
`split_bool` splits the boolean and leaves the value opaque in both arms, which
is the same stall `bool_result` has.

What makes it true is narrow and worth stating plainly: `equal` is exactly
`Value`'s derived `PartialEq`, and that equality **is** structural identity —
nothing the machine has compares equal to a value it stays distinguishable
from. The law therefore claims nothing about equal values being interchangeable
in general — it says two spellings of one value may be swapped.

Floats were the exception, and the reason this used to carry a side condition:
`0.0 == -0.0` answers `true` on two values that stay distinguishable, so `check`
had to refuse a `c` holding one anywhere. They are gone, and `check` has nothing
left to verify here.

It declines an arm that already opens with `drop ; push c`, which is what keeps
it out of its own output — the window still matches after a firing, and without
the guard `each` would write the literal in forever.

### Two counits, not one

`pick` is a comultiplication and `drop` a counit, and a comonoid has *two*
counit laws — discard the copy, or discard the original:

```text
counit        pick d ; drop            = nothing
counit_under  pick 0 ; dip 1 { drop }  = nothing
```

Only the first was here. The second is what `factor` leaves behind after
`retest` has fired on both arms, and it is an axiom for the same reason its
partner is. It holds **only at depth 0**: `pick d ; dip (d+1) { drop }` copies
to the top and deletes the original, which for `d > 0` *moves* the value — that
is a `roll d`, a different law, and not written.

`inv(counit_under)` puts the pair in where there was nothing, and unlike
`inv(counit(d))` it needs no argument, the law being stated at one depth.

### The one thing a case split cannot reach: `bool_result`

```text
op ; is_bool  =  op ; drop ; push true       for an op that yields a boolean
```

`is_bool ; is_bool` is the case that wants it, and with `annihilate` to take
the `is_bool ; drop` away it comes out as `drop ; push true`. The operator
stays on both sides on purpose — that makes this the smallest thing that has to
be assumed, and lets the existing set finish the job. It also means the law
covers a **flag** as readily as a predicate: `add` is `(2 -> 2)` and the flag
is what `is_bool` would be asking about, so `add ; is_bool` folds even though
nothing can delete the `add`.

**Why it is not derivable from `split_bool`.** It looks as though it should be:
split the value, and in each case it is a literal that `eval` folds. The then
arm does exactly that. The else arm does not:

```
$ rewrite demo twice_bool -t 'at(1, split_bool); distribution; values; factoring; all'
   0 │ is_bool
   1 │ pick 0
   2 │ is_bool
   3 │ branch then → a bool {
     │   drop
     │   push true
     │ } else → not a bool {
     │   is_bool                          ← the original problem, again
     │ }
```

That arm is *dead* — the value came out of `is_bool`, so it is a boolean — and
its deadness is precisely the fact being sought. Splitting again reproduces it.

It is independent rather than merely elusive, and the argument is the same
shape as `copy_nat`'s. Read `is_bool` as answering `42` for `true`, `true` for
`false`, and `false` otherwise. `split_bool` still holds — 42 is truthy, so the
then arm runs and the inner branch still recovers the value — and every other
equation is generic in what `is_bool` means. This law fails there. The gap is
that a branch can observe only **truthiness**, and `false` is the only falsy
value, so being truthy is strictly weaker than being a boolean. **No case split
on a value yields a fact about the codomain of a function.**

So the fact lives on the instruction, as `Instruction::yields_bool`, beside
`commutative` and for the same reason — and `vm` measures it rather than
restating it, running every computation on every shape of operand and holding
the list to what it finds. The list is wide, because every fallible operation
reports with a flag and reports it on top; `tuple n` is the negative case that
keeps the sweep honest.

`push` is excluded deliberately. A literal's type is known *better* than this
law says: `eval` folds `push c ; is_bool` to the answer rather than to `true`.

The five type tests other than `is_bool` are decided by the same fact —
`op ; is_int` would be `op ; drop ; push false` — and are not written yet.

### A boolean is either true or false

The only law that can put a `branch` on an **unknown** condition into a term,
and so the only way to learn anything about a value that did not arrive as a
literal. Everything else needs the fact already on the stack.

```
$ rewrite demo probe -t 'at(0, split_bool); distribution; values'
 pos │  depth │ instruction
─────┼────────┼────────────
   0 │      1 │ pick 0
   1 │      2 │ is_bool
   2 │      2 │ branch then → a bool {
   0 │      1 │   branch then → true {
   0 │      0 │     push false
     │        │   } else → false {
   0 │      0 │     push true
     │        │   }
     │        │ } else → not a bool {
   0 │      1 │   not
     │        │ }
```

That was `not` on an opaque value — nothing to fold. Splitting first replaces
the value with a **literal** inside each arm, and `not true = false` and
`not false = true` both fall out. It is the "path condition becomes a value"
move, with no side condition to satisfy.

The guard is what makes the law unconditional. Stating it instead as
`X ; branch { push true } { push false }` = `X` for an `X` that yields a boolean
would need a syntactic predicate over instructions, and would then decline
exactly the interesting cases — a value that arrived by `pick`, or out of a
call. Asking `is_bool` in the term costs a branch and answers for every value.

It takes no arguments at all, which nothing else in the set manages. Both sides
leave the stack as they found it, though the left needs a value to look at where
the right does not; that asymmetry is `counit`'s, and `--check` allows it.

`unsplit_bool` is the forward reading, for taking a split back out once its arms
have been folded down to nothing interesting.

#### The guard it leaves: `bool_result_copied`

```text
op ; pick 0 ; is_bool  =  op ; push true       for an op that yields a boolean
```

The split asks `is_bool` **behind a `pick 0`**, because the value it is about to
branch on has to survive the question. `bool_result` reads `op ; is_bool`, and a
matcher's width is fixed before it looks — so the copy in the middle put the
answer out of reach, and a split placed on an operator's result stalled holding
a question the equation set could already discharge. The two laws built to
compose could not meet, and `values` walked straight past the term.

```
$ rewrite mini probe -t 'exact(at(1, split_bool); values; cleanup)'
   0 │ equal
   1 │ branch then → true { push true } else → false { push false }
```

That is the whole point of the case split — an unknown boolean replaced by a
literal in each arm — and until this window existed it did not happen.

**It is a lemma, and the derivation is the argument.** Un-sharing is what makes
it go: `copy_nat` backwards turns the copy into a *second run of `op`*, which is
what puts an `op` next to the `is_bool`, and the run left over is exactly what
the annihilation and counits the copies paid for take away again.

```
$ rewrite mini guard -t 'exact(must(once(bool_result_copied)))' --show-script
     0  copy_nat    <- @0   equal ; pick 0        ⇒ pick 1 ; pick 1 ; equal ; …
     1  interchange <- @3   dip 1 { equal } ; is_bool ⇒ is_bool ; dip 1 { equal }
     2  bool_result -> @2   equal ; is_bool       ⇒ equal ; drop ; push true
     3  annihilate  -> @2   equal ; drop          ⇒ drop ; drop
     4  counit      -> @1                         ⇒ (nothing)
     5  counit      -> @0                         ⇒ (nothing)
     6  interchange -> @0   push true ; dip 1 { equal } ⇒ dip 0 { equal } ; push true
     7  elim_dip0   -> @0                         ⇒ equal
```

`tests::the_guard_a_split_leaves_is_derivable` runs both routes and holds them
to the same answer, and `identities::the_guard_a_split_leaves` states the claim
in the language.

It reads `op : n -> 1` only. A flag-leaving operator is `(n -> 2)` and the
annihilation in the middle has nothing to say about it — where plain
`bool_result` covers a flag happily, since it deletes nothing.

### It is not a normalizing pass

`introduce` grows the term and has no measure, so it belongs in no `repeat`;
putting it in one exhausts the budget. Aiming it is the whole job, which is what
`once`, `then`, `else` and `repeat_n` are for. `annihilate` takes straight back
out what `introduce` puts in, they being the two readings of one law — so the
two must never share a fixpoint either.

## Combinators

Control and traversal, unchanged from before the split:

| | |
|---|---|
| `each(r, ...)` | every position in one sequence, left to right, to exhaustion |
| `once(r, ...)` | the first matcher that matches, at the first position it does |
| `at(n, r, ...)` | the first matcher that matches, at *exactly* position n |
| `a; b` | in sequence |
| `a \| b` | the first that *changes something* |
| `try(t)` | never fails, and an aim inside it that misses is not reported |
| `must(t)` | fails unless `t` changed something, rolling the term back |
| `repeat(t)` | until nothing changes |
| `repeat_n(k, t)` | at most k times, stopping early |
| `children(t)` | every child sequence, one level down |
| `then(t)`, `else(t)`, `body(t)` | one *kind* of child, everywhere |
| `then(k, t)`, `else(k, t)`, `body(k, t)` | that child of the node at `k` |
| `bu(t)`, `td(t)` | children first / here first, recursively |
| `id`, `fail` | |

`|` takes the first branch that *does something*, not merely the first that does
not fail. Every total tactic reports "unchanged" when it had no work, and
treating that as a win would make `a | b` unusable with any of them.

A matcher that matches nowhere reports **unchanged, not failed**. Scanning a
sequence and finding no work is a successful no-op; treating it as an error made
`a; b` throw away everything `a` did whenever `b` had nothing to do. `Failed`
comes only from an explicit `fail`.

An *aimed* step that misses is unchanged too, and is additionally **reported** —
see "an index is a claim" below. That is a diagnostic rather than an outcome, so
nothing above it has to know about it.

### Aiming at exactly one window

`each` and `once` say *what* to apply and `then`/`else`/`body` say *which kind*
of child to go into. Neither says *which one*, so a term with two branches in it
could not be addressed. Two forms close that, and composed they name any window
a script prints:

```
$ rewrite tests pair_check -t 'normalize(unfold_all; then(1, body(2, then(1, at(2, sink)))))' --show-script
     3  interchange -> [1.then, 2.body, 1.then] @2
```

The tactic and the location read the same, in the same order. `at(n, ...)` is
`once` told where to look instead of asked to find out, and `then(k, t)` is
`then(t)` narrowed from every branch to the one you meant.

### The listing says which number to write

Every number in that tactic is in the `pos` column, which is a node's index in
the sequence it belongs to. It restarts at every nesting level, which is what
the indentation shows, and a closing brace belongs to no node and is blank:

```
$ rewrite tests pair_check -t unfold_all
closed — 3 steps + 3 up to inlining

 pos │  depth │ instruction
─────┼────────┼────────────
   0 │      1 │ untuple 2
   1 │      3 │ branch then → #3499 <inline> {
   0 │      2 │   push type_tests::RelEnum::Pair::tag
   1 │      3 │   equal
   2 │      2 │   dip 1 → #3500 <inline> {
   0 │      2 │     untuple 2
   1 │      4 │     branch then → #3496 <inline> {
   0 │      3 │       pick 0
   1 │      4 │       is_int
   2 │      4 │       branch then → #3489 <inline> {
```

Read down the column at each nesting level and the path writes itself:
`then(1, body(2, then(1, at(2, …))))`, which is the `[1.then, 2.body, 1.then]
@2` above. One number per level, and the last one is the window.

The stepper's diff leaves the column out, and `list` puts it back. A splice
renumbers every sibling after it, so a step that removed one node would report
the whole rest of the sequence as changed — where a depth is stable across a
firing, since every equation preserves the net stack effect of what it rewrote.

### An index is a claim; a scan is a question

A matcher that matches nowhere reports **unchanged, not failed**, and must: a
sweep that finds no work has done its job, and treating that as an error would
make `a; b` throw away everything `a` did whenever `b` had nothing to do.

But `at(2, unfold)` is not asking whether anything fits — it is saying there is
a call at 2. When there is not, the number is wrong, and that used to look
exactly like a rule with nothing to do. So the two are separated:

| | |
|---|---|
| a **claim** | `at(n, r)`, `then(k, t)`, `else(k, t)`, `body(k, t)` |
| a **question** | `each`, `once`, `then(t)`, `children`, `bu`, `td`, `repeat`, `repeat_n` |

A claim that does not hold is a **miss**: reported at the end of the run, with
what was there instead, and the tool exits non-zero.

```
$ rewrite tests pair_check -t 'unfold_all; at(9, sink)'
   ...the listing...

error: 1 aimed step(s) matched nothing:

  at(9, sink) at the root — that sequence holds 2 nodes, 0 to 1
```

**A miss is a diagnostic, not a failure.** Nothing rolls back, and the listing
is printed first — because the tree is what says which number to write instead,
and a rollback would take away the thing you need to fix it. It also means a
miss composes: `a; b` still keeps what `a` did.

The reason is worth having, because four different mistakes used to look
identical: the sequence is too short, the window runs off the end of it (`fuse`
reads two nodes and one is left), the node is the wrong shape, or a rule looked
and declined.

Two things do **not** record a miss:

- **A claim inside a search is not a claim.** `bu(at(0, collapse))` is a sweep
  that happens to be aimed at every level it visits, so the levels where it does
  not land are the answer rather than a mistake. Same for `try(t)`, which is the
  explicit way to say a miss is acceptable, and for `repeat`, whose last turn
  misses by construction.
- **A `|` branch a later one took over from.** Offering an alternative is saying
  the first may miss. If nothing changed anything, they all stand — which is
  what makes `t | fail` report the same as `must(t)`.

`must(t)` is still there, and is now the *stronger* thing: it fails unless `t`
changed something, rolling the term and the derivation back. Use it when the
aim is a precondition for what follows rather than a step in its own right —
and note it also fires when a search legitimately found nothing, which a miss
deliberately does not. It is exactly `t | fail`, and is built that way. The miss
survives the rollback, since it is the explanation rather than the work.

### The scan discipline

After a firing at window-start `w`, `each` resumes at `w - (width - 1)` rather
than moving on. A width-1 matcher therefore re-applies to its own output, and a
width-2 one reconsiders a moved node against its new neighbour. This lives in
one place and nowhere else.

## Named tactics

`--list-tactics` prints them. `unfold_all`, `dips`, `unary`, `factoring`,
`annihilation`, `values`, `commuting`, `cleanup`, `lifting`, `distribution`,
`flattening`, `all`, `dip_normalize`.

A tactic may not take a matcher's name, so where a pass and the matcher at its
heart would collide the pass gives way: `annihilation` drives `annihilate`,
`flattening` drives `flatten`. Tactic definitions may not recurse — `repeat` is
the only unbounded construct — and later definitions shadow earlier ones, so
`--tactics <file>` can replace a prelude entry.

## Precondition: total

The tool refuses no roots at all, and it is worth recording that it used to
refuse two.

One was a recursive root, which had no finite expansion to work with — but
recursion is forbidden now, and `check_arities` refuses a sentence that reaches
itself, so *every* sentence in a library that compiled has a finite expansion
and there is nothing left to ask. See
[hana.md](hana.md#recursion-is-forbidden).

The other was a root **able to fail**, because the equations assume totality.
`panic`, `assert` and `assert_eq` were the three instructions that could fail,
and a sentence reaching any of them — directly or through a call — was turned
away. They are gone from the language, so every sentence is total and the
precondition is discharged by construction rather than checked.

That is what lets `annihilate` ask only for an arity where the old rule needed a
syntactic whitelist to keep a buried `assert` from being dropped along with its
results.

### What that restriction cost, measured

It was expensive while it lasted, and the number is worth keeping because it is
what motivated getting rid of it. Two thirds of the sentences were admissible —
**but only about a fifth of the corpus by node count, and a few percent by
rewriting work done.** The admissible sentences were the small generated
accessors and predicates; the substantial code said `assert`, because a sentence
that untupled a value it had no reason to trust said so, and saying so is what
made it fallible.

The consequence was visible in a trace: the movement laws ran freely while the
value laws had almost nothing to act on.

```
$ rewrite tests state_check -t 'exact(unfold_all; all)' --trace
  rule firings
  ────────────
  sink               66
  unfold             33
```

`exact` is doing real work there: without it the goal would close up to
inlining, and a closed goal prints where the two sides *met* rather than what
the tactic did on the way. The counts are the search's and would be printed
either way — a route that does not work out still cost what it cost.

Worth knowing either way: only **two** of the thirteen equations actually need
totality. `annihilate` needs it because dropping `X`'s results still has to run
`X` if `X` can fail, and `interchange` needs it because reordering is only
unobservable when the failure order cannot be seen. The other eleven were sound
on fallible code as written.
## The governing invariant, in three parts

The old rule was: *a tactic's result depends only on the sequence it is given,
never on where in the tree it is being applied.* With a script in the picture
that splits:

1. **Matchers stay position-blind.** `plan` is a pure function of its window and
   reports where it wants to rewrite *relative to that window*. A matcher that
   needs to reach into a branch arm says so with a descent from the window,
   never with a path from the root.
2. **Only the driver knows the path.** It is threaded through the traversal and
   used for exactly one thing: stamping absolute locations onto recorded steps.
3. **The applier depends only on the tree and the step.** Hence the headline
   property: replaying a recorded script against a fresh build reproduces the
   run exactly.

Facts about the *library* do not break this — a sentence's arity and its
annotations are properties of the whole program, the same wherever they are met.

The invariant is also why nothing reaches across a frame. When you want that,
the answer is to remove the frame with `flatten` rather than to give a matcher
context — one law that erases a boundary composes with everything, whereas
context-aware ones would each need their own notion of it.

### Local application, absolute record

A traversal owns each sub-sequence as it visits it, so during a run the root is
not reachable from where the work happens. A firing is therefore applied to the
sequence in hand with a *relative* location, while the step written into the
script carries the full path. The two agree by construction, and the replay test
is what holds them to it — deliberately recording the relative location instead
fails six tests.

Ancestor indices cannot go stale in between, because while the engine is inside
a child body every enclosing frame is suspended mid-iteration and nothing can
splice an ancestor sequence until the traversal returns to it.

## A block is not a call

Phase 4 gives a branch arm and a `dip N { ... }` body a `SentenceIndex` alike,
purely because it needs somewhere to put them. Neither is reachable by name, so
neither is a call: there is no call site for `unfold` to open, and nothing for
the un-expanded listing to usefully name on one line. Both are spelled out by
`build`, before any tactic runs.

```
   3 │      4 │ dip 1 → #676 <inline> {
   0 │      4 │   is_symbol
     │        │ }
```

A `dip N` or `jump` naming a real sentence is a different thing and stays a
call: there the callee exists independently, `unfold` is a real choice, and the
label is worth keeping.

```
$ rewrite tests state_check -t 'exact(once(unfold))'              #  50 lines
$ rewrite tests state_check -t 'exact(repeat_n(2, once(unfold)))' #  62, one more call opened
$ rewrite tests state_check -t unfold_all                         # 635, one flat sentence
```

Because splicing rescans where it landed, `each(unfold)` already opens a whole
sequence transitively; `bu` is what additionally reaches into branch arms. To
open *less*, use `once`, which takes a single call — and note that it works on
one sequence, so `repeat_n(k, once(unfold))` counts calls at the level you are
looking at rather than descending into arms.

## Don't expand more than you are about to cancel

The size of an expansion is not a property of the callee. Opening one layer and
folding what that exposed before opening the next keeps a term small that
unfolding eagerly does not, because `distribute` duplicates the continuation
into both arms — so every call still unopened when it fires gets copied along
with everything else.

Note that `repeat(bu(each(unfold); ...))` does not buy this, and neither does
`td`: both open every call they can see before the folding laws get a turn,
which is the situation the interleaving was meant to avoid. Staging needs a
tactic that opens a bounded number of calls, which means `once` or `repeat_n`.

## Reaching one arm: `then`, `else`, `body`

`children` visits every child of every node. That is what a normalizing pass
wants and the opposite of what a targeted one wants, so it comes in narrower
flavours: `then` and `else` take a branch's arms one at a time, and `body` takes
dip bodies.

Staged unfolding is what makes the difference concrete. `once` works on one
sequence, so the moment the only remaining calls are inside branch arms it has
nothing left to find, and no amount of `repeat_n` gets further.
`then(once(unfold))` is how you say which arm to open next, and it is the whole
difference between a plateau and a derivation.

These three partition `children` rather than overlapping it: `body` declines a
branch arm and `then`/`else` decline a dip, so `children(t)` is exactly
`then(t); else(t); body(t)`. A selector that finds nothing to descend into
reports "unchanged" — `then(t)` on a sequence with no branch is a no-op, not an
error.

## Folding is evaluation

Every data operation is total (see `docs/totality.md`), so running one on known
values and pushing the answer is the same program. There is no operand it could
have rejected and no check the fold discards. What `eval` owes is therefore not
a licence but an **obligation**: to agree with the interpreter exactly, on junk
as much as on anything else.

That is why it goes through `Value::truthy` and `numeric_cmp` from
`bytecode::value` rather than a second reading of the same rules. `push 1; push
2; and` folds to `push true` because neither operand is `Bool(false)` — `false`
is the unique falsy value. `less` on two symbols is not a comparison it can
claim to have made, so it answers `false, false` — the flag as well as the
value.

`fold_branch` selects by the same `truthy`, which is why `push 1; branch` is
decided just as firmly as `push false; branch`: it takes the **then** arm.
Reading it as a test for *being* a boolean would send junk down the wrong path.

**`tuple` and `untuple` are operators that answer**, and for a long time `eval`
did not know it. Every value law is stated about literals and a *constructed*
tuple was not one, so a postcondition comparing what a function just built
against what it should have built stalled with both operands sitting right
there. Widening `eval_op` is not a new law — `Rule::Eval` already says "the
pushes of what the operator answers".

Both directions owe the interpreter exactly, junk included: `tuple n` takes the
top `n` in the order they sit on the stack, so the **topmost becomes the last
element** and `push 1 ; push 2 ; tuple 2` is `push (1, 2)`; and an `untuple n`
whose width does not match leaves
the value in the deepest slot it filled, `()` in the rest, and `false` on top.
`identities::building_and_taking_apart_literals` measures both against the
machine rather than restating them.

`eval0` is the third matcher for the reason there are three annihilations: a
width is fixed before it looks, and `tuple 0` reads no operands at all.

## Four things that are easy to get wrong

1. **Opposite readings of one law in one `repeat`.** `collapse`/`expand`,
   `sink`/`float`, `factor`/`unfactor`, `annihilate`/`introduce` — and every
   `r`/`inv(r)` pair, which is now the general statement of it. Each is one
   equation read two ways and will oscillate until the fuel runs out. The trace
   is what diagnoses it, since the two readings show up under both names.
2. **Expecting `bu` to stage.** It reaches new bodies only on the next pass;
   `td` descends into what it just created, so one `td` pass opens the whole
   call graph.
3. **Expecting a matcher to see context.** It sees its window and nothing else.
   Remove the frame with `flatten`, or bring the neighbour in with `distribute`.
4. **Reading `@n` as a global position.** It is an offset in the sequence the
   descent arrives at. Two steps reporting `@0` may be in different arms.
5. **Hiding an aim inside a search.** `at(9, sink)` on a five-node sequence
   reports itself, but `bu(at(9, sink))` does not — an aim inside a sweep is
   along for the ride, and there is no telling a level it skipped from a level
   it was never meant to hit. Read the position off the `pos` column rather
   than counting lines, since the column restarts at every nesting level and
   the lines do not, and reach for `must` when the aim is a precondition for
   what comes after it rather than a step in its own right.

## Checking and tracing

- `--check` verifies every step preserves the net stack effect of the window it
  rewrote. It checks *net change* rather than full arity, because `annihilate`
  legitimately lowers the input requirement: dropping `pick 2; drop` also drops
  the demand for three values that only the pick made.

  **What it cannot catch is a rewrite licensed by a wrong arity.** A
  misreported arity preserves net change as readily as a correct one, and a
  lowered requirement is what it allows on purpose — so it is downstream of the
  reckoning being right, not a guard on it. A branch whose arity was read off
  one arm claimed `(1 -> 0)` where it was `(2 -> 1)`, and `--check` waved the
  resulting rewrite through; see `arity::branch_arity` and
  `tests::a_function_that_is_not_the_identity_is_not_rewritten_into_one`.
- `--show-script` prints the derivation, one step per line, with each step's
  window and replacement sketched.
- `--trace` prints how often each matcher fired, and the total step count. The
  two differ when a matcher takes more than one step.
- `--fuel <n>` raises the budget. It is spent per *step*, so `factor` costs
  three. Running out prints the last two dozen steps, which is how an
  oscillation diagnoses itself.
- `--stack` shows what each slot holds, with equal values sharing a name.
- `--step` walks the derivation. See below.

## Walking a derivation: `--step`

Each step puts the tree as it stood **before** the last step beside the tree
**after** it, so the only thing on the screen is what that one law did, and
sketches the window the next one is about to match:

```
    step 0                                    ┃   step 1  ·  unfold -> [1.then, 2.body] @0
  ────────────────────────────────────────────╂────────────────────────────────────────────
    ⋮ 8 unchanged lines                       ┃
    2 │   dip 1 → #3400 <inline> {            ┃   2 │   dip 1 → #3400 <inline> {
  - 2 │     jump → #645 …::Body::check        ┃ + 2 │     untuple 2
                                              ┃ + 4 │     branch then → #3396 <inline> {
```

Commands: `s`/`step`, `b`/`back`, `g`/`goto`, `c`/`continue`, `r`/`restart`,
`l`/`list`, `d`/`diff`, `t`/`trace`, `stack`, `h`/`help`, `q`/`quit`. A bare
newline repeats the last, and end of input quits — so a piped script needs no
closing `q`.

`trace` shows the derivation around the cursor with counts so far:

```
       1  unfold -> [1.then, 2.body] @0
       2  unfold -> [1.then, 2.body, 1.then] @0
       3  interchange -> [1.then, 2.body, 1.then] @2
  ▸    7  interchange -> [1.then] @0
```

### It steps by applying a prefix

A run produces a script, so the tree after *n* steps is exactly the first *n*
steps applied to a fresh build. Stepping backwards costs what stepping forwards
does, and neither needs an undo log or a snapshot.

This is what the two-layer split buys the stepper. It used to work by *re-running
the search* with a budget of n firings — correct only because rules were pure
functions of their windows, and quadratic in *n*. Now the derivation is a value
and the search runs once.

### A tactic that will not settle

The census run is where a tactic that never settles reports itself. The script
up to that point is still good, so the session walks to the failure and shows it
where it happens, which is the case stepping is most wanted for.

## Seeing which slots hold the same value

`--stack` adds a column showing what each slot holds, with equal values sharing
a name. It is a post-hoc abstract interpretation over the finished tree and is
never consulted by a matcher — the tool proves things by construction, not by
consulting an analysis.

## What is not here yet

- **Tranche two.** `dup_natural`, `rebuild_copy`, and `dip k { } = ε`. All are
  expressible as equations in this framework; none is written yet.
  `specialize_equal` was on this list and is now in the set — see "the value an
  arm tested equal to".

  Two that used to be on this list are now in the set, as equations without
  matchers. `roll 0 = ε` is `roll_cycle` at `d = 0`, and the rolls arrived with
  company: `unframe` and `pick_roll` are what make a roll worth writing, since
  alone it only moves a value and nothing could say what that bought.
  `pick_drop_to_roll` — `pick d ; dip (d+1) { drop }` = `roll d`, which is
  `counit_under` at depth and would demote it — is still not written, but
  something wants it now: it is what would let `lift` reach a prefix that
  consumes more than one value the other arm still needs.

- **Matchers for the other five roll readings.** `unframe` forward has one now
  — see "placing one" above, where the answer was to read the frame rather than
  the rolls. The rest still have real questions behind them: the width of
  `roll_cycle` is its own argument, and its backward reading needs somewhere to
  stand.

  Two that used to be on this list are not any more. `bool_identity` and
  `retain_condition` both existed to tell an arm what its condition was, and
  both needed the `yields_bool` syntactic predicate to do it — which declined
  the interesting cases. `split_bool` reaches the same place without a
  predicate: split the value, and each arm holds a literal that the folding
  laws read for themselves.
- **A smarter upper layer.** Matchers and combinators are the whole of the
  search *here*. Everything above is deliberately arranged so that a better
  generator can be dropped in without the lower layer noticing: whatever finds
  the derivation, it still has to hand over a script that the applier checks.

  `bin/prove`'s strategies are the first thing to take that up. They sit above
  both layers rather than inside either, and what they hand back is an ordinary
  `Script` — a sub-proof found inside a branch arm comes back out addressed to
  the whole term, by way of `Location::under`. So nothing in this document
  changed to make them possible, which is the property worth keeping when the
  next one arrives.
