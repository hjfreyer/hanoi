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

Fifteen, plus one thing that is not an equation. `--list-rules` prints the
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
| `commute` | `roll 1 ; op` = `op`, for a commutative `op` | `roll 1` swaps the top two, and `add`, `multiply`, `and`, `or`, `equal` cannot tell. Forward is `comm`, backward is `swap` |
| `split_bool` | `pick 0 ; is_bool ; branch { branch { push true } { push false } } { }` = nothing | a boolean is either `true` or `false`. Backward it is a case split; forward is `unsplit_bool` |
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
| `comm` / `swap` | 2 / 1 | commutativity, either way |
| `split_bool` / `unsplit_bool` | 1 / 3 | the case split, either way |
| `introduce { .. }` | n | annihilate backwards — see below |
| `counit`, `copy_const`, `copy_assoc`, `cancel_tuple` | 2 | |

`inv(r)` is the rest of them: every backward reading that is not worth a name
of its own. See "reading an equation backwards" below.

A matcher checks its own side conditions, so anything it proposes is something
the applier accepts. That is swept: every matcher over a corpus of windows,
asserting nothing is ever refused.

Two of these need no coordination even though they look adjacent. `annihilate`
wants `X : n -> 1` and `counit` wants `pick d ; drop`; since `pick d` is
`(d+1 -> d+2)` it fails annihilate's arity requirement outright. The old code
had an explicit special case for exactly this.

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

### When there is no backward reading

Six rules have none, and asking says why rather than matching nothing:

```
$ rewrite tests probe -t 'each(inv(cancel_tuple))'
error: `cancel_tuple` has no backward reading
  | each(inv(cancel_tuple))
  |      ^^^^^^^^^^^^^^^^^
  = help: the backward side of `cancel_tuple` is `push true`, which does not
          say what `n` was — a tuple of any width leaves the same flag
```

Three things put a reading out of reach, and they are worth telling apart:

- **It would have to invent, not recognize.** `inv(eval1)` would need the
  operator that produced the literal, and `inv(fold_branch)` the arm that was
  not taken. Nothing in the window says either.
- **An argument is not recoverable.** `cancel_tuple`'s `n`, above.
- **The backward side is empty.** `counit` is `pick d ; drop` = *nothing*, so
  there is no window to match at all — a matcher must read at least one node.
  That reading belongs to the generator, which can emit it as part of a
  derivation; see the vacuous law above.

Two more are refusals that point somewhere: `inv(annihilate)` is the
introduction rule and has to say what to conjure, so it is
`introduce { ... }`; and `factor` is three steps of two different equations, so
there is no single one to reverse — `inv(unfactor)` is the last of the three.
`inv(unfold)` is the real gap: folding a body back into a call is expressible
as a step, but nothing looks for it, because a window does not say which
sentence to fold into.

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

That measurement earned its keep immediately. `assert_eq` looks commutative — it
fails exactly when `a != b`, which is symmetric — and is not: the diagnostic it
fails *with* names the operands in the order given, so the two readings are
observably different. It is excluded, and nothing is lost, because the tool
refuses any sentence that can reach an `assert_eq` anyway.

The flag a fallible operator leaves is symmetric too, so this holds for `add` on
operands it cannot add: `0, false` either way round.

`swap` is the backward reading, putting a `roll 1` *in* so that what sits
underneath the operands can be rearranged to line up with something else. It has
no measure and grows the term — its output still contains the operator it
matched, so `each` would put a second `roll 1` in front of it and keep going.
Aim it, as with `introduce`.

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
$ rewrite tests 'Pair::check' -t 'unfold_all; then(1, body(2, then(1, at(2, sink))))' --show-script
     2  interchange -> [1.then, 2.body, 1.then] @2
```

The tactic and the location read the same, in the same order. `at(n, ...)` is
`once` told where to look instead of asked to find out, and `then(k, t)` is
`then(t)` narrowed from every branch to the one you meant.

### The listing says which number to write

Every number in that tactic is in the `pos` column, which is a node's index in
the sequence it belongs to. It restarts at every nesting level, which is what
the indentation shows, and a closing brace belongs to no node and is blank:

```
$ rewrite tests 'Pair::check' -t unfold_all
 pos │  depth │ instruction
─────┼────────┼────────────
   0 │      1 │ untuple 2
   1 │      3 │ branch then → #3408 <inline> {
   0 │      2 │   push symbol(…::Pair::tag)
   1 │      3 │   equal
   2 │      2 │   dip 1 → #3409 <inline> {
   0 │      2 │     untuple 2
   1 │      4 │     branch then → #3405 <inline> {
   0 │      3 │       pick 0
   1 │      4 │       is_int
   2 │      4 │       branch then → #3398 <inline> {
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
$ rewrite tests 'Pair::check' -t 'unfold_all; at(9, sink)'
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
`annihilation`, `values`, `commuting`, `cleanup`, `distribution`, `flattening`,
`all`, `dip_normalize`.

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
   3 │      4 │ dip 1 → #676 <inline> {
   0 │      4 │   is_symbol
     │        │ }
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

- **Tranche two.** `specialize_equal`, `dup_natural`, `rebuild_copy`,
  `speculate_branch`, `pick_drop_to_roll`, and `roll 0 = ε` / `dip k { } = ε`.
  All are expressible as equations in this framework; none is written yet.

  Two that used to be on this list are not any more. `bool_identity` and
  `retain_condition` both existed to tell an arm what its condition was, and
  both needed the `yields_bool` syntactic predicate to do it — which declined
  the interesting cases. `split_bool` reaches the same place without a
  predicate: split the value, and each arm holds a literal that the folding
  laws read for themselves.
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
