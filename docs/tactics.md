# Tactics

`bin/rewrite` turns one sentence's compiled bytecode into a tree and prints it.
A **tactic** says how to rewrite that tree before printing.

No *call* is opened unless you ask. The default listing shows one sentence,
naming every call it makes on a single line; `unfold` is how you open one up.
Blocks written inline — branch arms and `dip N { ... }` bodies — are always
spelled out, because they are not calls.

```bash
cargo run --bin rewrite -- tests 'State::check' -t 'unfold_all; dips'
```

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

So a run leaves behind a derivation:

```
$ rewrite tests 'Pair::check' -t 'unfold_all; all' --show-script
...
  derivation — 7 step(s)
     0  unfold -> [1.then, 2.body] @0
        jump → #645
     ⇒  untuple 2 ; branch { jump → #642 ; dip 1 { push symbol(some_other) ; equal } ; and } { d…
     2  interchange -> [1.then, 2.body, 1.then] @2
        branch { drop ; push true } { is_bool } ; dip 1 { push symbol(some_other) ; equal }
     ⇒  dip 2 { push symbol(some_other) ; equal } ; branch { drop ; push true } { is_bool }
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

Thirteen, plus one thing that is not an equation. `--list-rules` prints the
matchers that place them.

| equation | law | notes |
|---|---|---|
| `collapse` | `dip k { dip j { A } }` = `dip (k+j) { A }` | forward is the old `collapse`; backward at the split `(1, k-1)` is the old `expand` |
| `elim_dip0` | `dip 0 { A }` = `A` | forward splices a frame that hides nothing; backward *introduces* a frame around a run |
| `interchange` | `X ; D_k` = `D_(k-m+n) ; X`, for `X : n -> m`, `k >= m` | forward is `sink`, backward is `float`. `D` is a dip at any depth, or a call that hides something |
| `fuse` | `dip k { A } ; dip k { B }` = `dip k { A B }` | backward splits one frame at a point the arguments name |
| `hoist` | `dip (k+1) { X } ; branch { A } { B }` = `branch { dip k { X } ; A } { dip k { X } ; B }` | forward is `unfactor`; backward is the last step of `factor` |
| `distribute` | `branch { A } { B } ; C` = `branch { A C } { B C }` | `C` is a whole sequence. Backward factors a shared *suffix*, which the old set could not do at all |
| `fold_branch` | `push c ; branch { A } { B }` = the arm `c` selects | selected by `truthy`, and `false` is the only falsy value, so `push 1; branch` takes the **then** arm |
| `eval` | `push v1 … push vn ; op` = the pushes of what `op` answers | subsumes the old `fold_const` and `fold_const_unary` |
| `annihilate` | `X ; drop^m` = `drop^n`, for `X : n -> m` | `X` is a whole sequence. Forward subsumes `annihilate_drop` (m=1) and `annihilate_flagged` (m=2); backward is `introduce`, below |
| `counit` | `pick d ; drop` = nothing | *not* an annihilation: `pick d` is `(d+1 -> d+2)` |
| `copy_const` | `push c ; pick 0` = `push c ; push c` | |
| `copy_assoc` | `pick d ; pick 0` = `pick d ; dip 1 { pick d }` | neither side is smaller; the point is that one copy ends up **in a frame**, and a framed computation is one `float` can carry |
| `cancel_tuple` | `tuple n ; untuple n` = `push true` | the flag is the whole residue. The converse order is not a no-op and has no equation |

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
| `eval1` / `eval2` | 2 / 3 | one operand or two |
| `annihilate` / `annihilate_flagged` | 2 / 3 | one output or two |
| `introduce { .. }` | n | annihilate backwards — see below |
| `counit`, `copy_const`, `copy_assoc`, `cancel_tuple` | 2 | |

A matcher checks its own side conditions, so anything it proposes is something
the applier accepts. That is swept: every matcher over a corpus of windows,
asserting nothing is ever refused.

Two of these need no coordination even though they look adjacent. `annihilate`
wants `X : n -> 1` and `counit` wants `pick d ; drop`; since `pick d` is
`(d+1 -> d+2)` it fails annihilate's arity requirement outright. The old code
had an explicit special case for exactly this.

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

### Terms

A term is a run of instructions in braces. `pick n`, `roll n`, `tuple n`,
`untuple n`, `push <int|true|false>`, `dip n { ... }`, and the argument-free
operators (`drop`, `not`, `and`, `equal`, `is_bool`, `add`, …). `--list-rules`
prints the list.

It has no calls — a term is written here rather than compiled from a sentence,
so there is nothing to name — and no branches, which would need two blocks and a
condition and would be a program rather than a term. `panic`, `assert` and
`assert_eq` are absent on purpose: they are the three instructions that can
fail, and introducing one would break the precondition every equation is stated
under.

A term's arity is worked out when the tactic is compiled, from the term alone,
which is what lets a tactic be checked before a program is loaded. Two terms are
refused there rather than at run time:

- one whose arity is unknown, since there would be no saying what it discards;
- one that **consumes nothing**. `push 7` would match a window of no nodes,
  which is every position, so `each` would never move past the first — and this
  law discards whatever the term produces, so it could only ever become
  `push 7 ; drop`, which no later step can use.

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
| `try(t)` | never fails |
| `must(t)` | fails unless `t` changed something |
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

### Aiming at exactly one window

`each` and `once` say *what* to apply and `then`/`else`/`body` say *which kind*
of child to go into. Neither says *which one*, so a term with two branches in it
could not be addressed. Two forms close that, and composed they name any window
a script prints:

```
$ rewrite tests 'Pair::check' -t 'unfold_all; then(1, body(2, then(1, at(2, sink))))' --show-script
     2  interchange -> [1.then, 2.body, 1.then] @2
```

The tactic and the location read the same, in the same order. `at(n, ...)` is
`once` told where to look instead of asked to find out, and `then(k, t)` is
`then(t)` narrowed from every branch to the one you meant.

Both are **silent when they miss**, because a rule that matches nowhere is an
ordinary no-op and always has been. That is wrong for an aimed step, where
missing means the position was wrong:

```
must(then(1, at(2, sink)))
```

`must(t)` fails unless `t` changed something. It is exactly `t | fail` and is
built that way; it exists because the idiom is not obvious and aiming without it
is unverifiable. A failure that reaches the top of a run is reported and exits
non-zero — nothing swallows it, since `try` is how you say a failure is
acceptable.

### The scan discipline

After a firing at window-start `w`, `each` resumes at `w - (width - 1)` rather
than moving on. A width-1 matcher therefore re-applies to its own output, and a
width-2 one reconsiders a moved node against its new neighbour. This lives in
one place and nowhere else.

## Named tactics

`--list-tactics` prints them. `unfold_all`, `dips`, `unary`, `factoring`,
`annihilation`, `values`, `cleanup`, `distribution`, `flattening`, `all`,
`dip_normalize`.

A tactic may not take a matcher's name, so where a pass and the matcher at its
heart would collide the pass gives way: `annihilation` drives `annihilate`,
`flattening` drives `flatten`. Definitions may not recurse — `repeat` is the
only unbounded construct — and later definitions shadow earlier ones, so
`--tactics <file>` can replace a prelude entry.

## Preconditions: non-recursive, and total

The tool refuses two kinds of root.

**Recursive**, because there is no finite expansion. Deciding that takes one
annotation lookup, not a graph traversal: `check_arities` will not compile a
sentence that calls a `#[recursive]` one without being `#[recursive]` itself, so
the annotation has already propagated up the call graph and *its absence on a
root is a proof that expanding that root terminates*. That claim is load-bearing
and so is checked rather than assumed —
`program::invariant::reaching_a_cycle_implies_the_recursive_annotation` computes
the real cycles over the corpus and asserts every sentence reaching one carries
the annotation.

**Able to fail**, because the equations assume totality:

```
$ rewrite tests 'queue::accept' -t all
error: 'queue::queue::accept' can fail

  It reaches a `panic`, an `assert` or an `assert_eq`, directly or
  through a call. ...
```

Both properties are closed over reachability, so refusing the root refuses every
node any tree can come to hold. That is what lets `annihilate` ask only for an
arity where the old rule needed a syntactic whitelist to keep a buried `assert`
from being dropped along with its results.

### What that restriction costs, measured

It is expensive on the current corpus, and the number is worth having in front
of you. Two thirds of the sentences are admissible — **but only about a fifth of
the corpus by node count, and a few percent by rewriting work done.** The
admissible sentences are the small generated accessors and predicates; the
substantial code says `assert`, because since fallible instructions started
reporting with a flag, a sentence that untuples a value it has no reason to
trust says so, and saying so is what makes it fallible (see `docs/totality.md`).

The consequence is visible in a trace: the movement laws run freely while the
value laws have almost nothing to act on.

```
$ rewrite tests 'State::check' -t 'unfold_all; all' --trace
  rule firings
  ────────────
  sink               66
  unfold             32

  98 step(s) in all
```

Worth knowing: only **two** of the thirteen equations actually need totality.
`annihilate` needs it because dropping `X`'s results still has to run `X` if `X`
can fail, and `interchange` needs it because reordering is only unobservable
when the failure order cannot be seen. The other eleven are sound on fallible
code as written. Lifting the restriction therefore means giving those two their
own side conditions rather than taking one for the whole run.
`tests::the_precondition_is_measured_rather_than_assumed` records the
measurement and fails if it goes stale.

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
      4 │ dip 1 → #676 <inline> {
      4 │   is_symbol
        │ }
```

A `dip N` or `jump` naming a real sentence is a different thing and stays a
call: there the callee exists independently, `unfold` is a real choice, and the
label is worth keeping. An inline block that would recurse also stays a call,
which is what it becomes at run time anyway.

```
$ rewrite tests 'State::check'                     #  48 lines, every call named
$ rewrite tests 'State::check' -t 'once(unfold)'   #  61, one call opened
$ rewrite tests 'State::check' -t unfold_all       # 637, one flat sentence
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

## Four things that are easy to get wrong

1. **Opposite readings of one law in one `repeat`.** `collapse`/`expand`,
   `sink`/`float`, `factor`/`unfactor`, `annihilate`/`introduce`, and now
   `distribute` forward and backward. Each pair is one equation read two ways
   and will oscillate until the fuel runs out. The trace is what diagnoses it.
2. **Expecting `bu` to stage.** It reaches new bodies only on the next pass;
   `td` descends into what it just created, so one `td` pass opens the whole
   call graph.
3. **Expecting a matcher to see context.** It sees its window and nothing else.
   Remove the frame with `flatten`, or bring the neighbour in with `distribute`.
4. **Reading `@n` as a global position.** It is an offset in the sequence the
   descent arrives at. Two steps reporting `@0` may be in different arms.
5. **Aiming without `must`.** `at(9, sink)` on a five-node sequence is a no-op,
   not an error, so a mistyped position looks exactly like a rule that had
   nothing to do. Wrap an aimed step in `must` and find out.

## Checking and tracing

- `--check` verifies every step preserves the net stack effect of the window it
  rewrote. It checks *net change* rather than full arity, because `annihilate`
  legitimately lowers the input requirement: dropping `pick 2; drop` also drops
  the demand for three values that only the pick made.
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

- **Tranche two.** `retain_condition`, `bool_identity`, `specialize_equal`,
  `dup_natural`, `rebuild_copy`, `speculate_branch`, `pick_drop_to_roll`, and
  `roll 0 = ε` / `dip k { } = ε`. All are expressible as equations in this
  framework; none is written yet.
- **Scripts as files.** A script is a value, not yet a syntax. Serializing one
  needs a grammar for node sequences; the step kinds are a closed, serializable
  shape on purpose. When it lands, a saved derivation will depend on the library
  only through names and facts the applier re-derives — never through quoted
  code — so it fails loudly at the changed step rather than rotting silently.
- **Symbols and floats in terms.** `push` takes an integer or a boolean; the
  other literals have no syntax yet.
- **A smarter upper layer.** Matchers and combinators are the whole of the
  search today. Everything above is deliberately arranged so that a better
  generator can be dropped in without the lower layer noticing: whatever finds
  the derivation, it still has to hand over a script that the applier checks.
