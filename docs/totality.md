# Totality

Every operation in the hanoi bytecode is a total function. An operation applied
to operands it was not written for does not fail; it returns a **deterministic
default**, called *junk* below, and says nothing about having done so. No
instruction can end a run for a reason about values: there is nothing left to
fail.

This document is the normative specification of that. The junk table is the
spec; `vm::totality_tests` is its executable mirror.

## Why total

Reasoning about two programs being interchangeable means reasoning about local
windows: replace a stretch of one program with an equal stretch, and the whole
stays equal. Two programs that compute the same values are still not
interchangeable if one of them *rejects* an input the other accepts, so as long
as ordinary operators could fail, every such law had to carry a
panic-preservation side condition — and those conditions are not window-local.
The damage was visible everywhere:

- Cancelling an operator against a following `drop` needed a hand-maintained
  whitelist of instructions that "cannot panic", so `add; drop` was not
  `drop; drop`.
- Constant folding had to decline `push 1; push 2; and`, because `push false`
  is not a panic and the original was.
- Folding a branch needed a literal `Bool`, because `push 1; branch` was a
  panic. Any literal folds now, `push 1; branch` taking the then arm.
- Hoisting a partial computation out of a single branch arm stayed out of reach
  entirely, and the workarounds for it existed only to launder an opaque value
  into a syntactically total shape.

Making the data operations total moves the question. Equivalence is now over
total functions, which a local window can decide. Whether a program is
*meaningful* — whether it ever computes on junk — becomes a separate static
judgment, layered on top rather than tangled into the equational theory.

## What can still stop a run

Nothing about the values. There were once three instructions that could —
`panic`, `assert` and `assert_eq`, whose whole job was to fail — and they are
gone, along with the `#[total]` annotation that existed to say a sentence did
not reach them. A sentence that wants to report a problem answers with a value:
see the `?` operator and `check_equals` in [hana.md](hana.md).

What is left is **meta-level or structural**, not a property of the values:

| fault | where |
|---|---|
| stack underflow | `pop`/`peek`, and `drop`/`pick`/`roll`/`dip`/`tuple` |
| invalid sentence index | `execute`'s dispatch |
| gas limit exceeded | the step counter |

Structural faults are ruled out ahead of time rather than handled: arity
checking is mandatory on every `assemble` path (`lang/bytecode/src/assembly.rs`), so
a sentence that would underflow does not assemble. The one remaining gap is an
entry point whose inferred arity has `inputs > 0` — it assembles, and then
underflows when run with an empty stack.

### Why there is no annotation for it

`#[total]` was opt-in, and for a while it was the useful thing to say. A
sentence carrying it promised it neither executed one of those three
instructions nor reached anything that did, through a `jump`, a `dip` or either
branch arm, and the compiler checked the promise against a least fixpoint over
the call graph.

Removing the three instructions removes the claim, because every sentence now
satisfies it. An annotation that everything qualifies for distinguishes
nothing, so `#[total]` is an error rather than a no-op: writing it gets you told
that there is nothing left to claim.

Note what totality does *not* have to cover, and never did: a sentence that
never returns. Recursion is forbidden (see
[hana.md](hana.md#recursion-is-forbidden)), so divergence is not one of the ways
a Hanoi program can fail to produce an answer.

What remains open is the question this document makes askable and does not
answer: whether a program ever *computes on junk*. That is a static judgment
over the table below, not a property of the instruction set.

## Truthiness

```
truthy(v)  =  (v != Bool(false))
```

**`false` is the unique falsy value.** A number, a symbol, a const string, a tuple — anything
that is not literally `false` — is true.

Applied **per operand**, and every boolean-shaped instruction is defined through
it:

| instruction | definition |
|---|---|
| `not v` | `Bool(!truthy(v))` |
| `a and b` | `Bool(truthy(a) && truthy(b))` |
| `a or b` | `Bool(truthy(a) \|\| truthy(b))` |
| `branch { A } { B }` | `A` iff `truthy(cond)`, else `B` |

Per-operand coercion is load-bearing rather than incidental. It is what makes De
Morgan hold on *all* values, not just booleans: `not (a and b)` is
`!(truthy a && truthy b)`, and `(not a) or (not b)` is
`truthy(Bool(!truthy a)) || truthy(Bool(!truthy b))` — the same thing, because
`truthy(Bool(p)) = p`. Coercing the pair jointly, or making `and` return its
operand, would both break that.

Note what that argument does *not* establish. It needs only per-operand
coercion and `truthy(Bool(p)) = p`, and both hold just as well for the opposite
rule `truthy(v) = (v == Bool(true))`. De Morgan does not pick a pole; it rules
out joint coercion. The pole is a separate choice, made below.

**A branch takes the then arm on junk.** The else arm is reached only by a
literal `Bool(false)`, which is what lets `fold_branch` fold any literal. And
**`not junk = false`**: junk is not `false`, so it is true, so its negation is
`false`. There is no third truth value; that is the price of a two-valued
definition and it is worth paying either way round.

### Which pole is unique

`false` is, and the choice is worth stating because the two rules are duals and
the arguments are not overwhelming in either direction.

What it buys is that the *positive* answer is the cheap one. A predicate that
computes a real boolean is unaffected — `equal`, the `is_*` tests and the
comparisons all produce genuine `Bool`s, so they read the same under either
rule. What differs is only what happens to a value that was never a boolean at
all, and there "carry on" is the less surprising reading than "take the failure
path".

What it costs is that a check written as "is this not false" **passes on junk**.
A test that wants the stronger reading has to say `push true equal`.

The change was made deliberately and is invisible to the corpus: every one of
the 64 `.hana` integration tests runs the identical number of VM steps under
either rule, because nothing in real code lets a non-boolean reach a branch.

## The junk table

Every data operation is total, and every one of them answers with exactly what
it computes. `()` below is the empty tuple, `Value::unit()`.

| instruction | arity | on its domain | off it |
|---|---|---|---|
| `push c`, `pick d`, `roll d`, `drop` | unchanged | — | no domain to be off |
| `equal`, `is_int`, `is_bool`, `is_const_string`, `is_symbol`, `is_tuple`, `is_tuple n` | unchanged | — | no domain to be off |
| `not`, `and`, `or`, `tuple n` | unchanged | — | no domain to be off |
| `as_bool`, `as_int`, `as_tuple n` | `1 -> 1` | — | the default of the type; see below |
| `add`, `subtract`, `multiply` | `2 -> 1` | the sum | `Int 0` |
| `divide`, `modulo` | `2 -> 1` | the quotient | `Int 0` |
| `greater`, `less` | `2 -> 1` | the answer | `false` |
| `negate` | `1 -> 1` | `-x` | `Int 0` |
| `tuple_length` | `1 -> 1` | the count | `Int 0` |
| `const_string_len` | `1 -> 1` | the count | `Int 0` |
| `const_string_char_at` | `2 -> 1` | the code point | `Int 0` |
| `untuple n` | `1 -> n` | the `n` elements | `()` × n |
| `branch` | unchanged | then arm unless `Bool(false)` | no domain to be off |

Two rules govern the rest of the table.

**Junk is the default of the type the instruction computes.** `add` leaves an
`Int` on every pair of values, `less` a `Bool`, `untuple n` exactly `n` values.
Which is to say every instruction has a **codomain**, and it is the same
codomain on junk as anywhere else: the junk column is the coercions of the
section below, applied to the type the instruction was going to answer in.
`untuple n` *is* `as_tuple n` followed by taking a tuple of the right width
apart, and that is the whole definition rather than a coincidence.

**No instruction reports on itself.** There is no `bool` on top saying whether
the answer was computed or invented, because the question belongs to the caller
and the caller can ask it — `is_int` before the arithmetic, `pick 0 ; pick 0 ;
as_tuple n ; equal` before the unpacking. Asking it there is strictly better
than reading it afterwards: the check is made where the operands still are, so
the arm that says no still has them, and the code that does not care pays
nothing. A flag asked the question for every caller whether or not any of them
wanted it, and every site that did not want it paid a `drop` to say so.

The arity is fixed whichever way the data goes, which is what makes junk
*padding* rather than an outcome. A caller's stack does not depend on the data,
so the arity checker works on shape alone, and every rule that moves code past
an instruction reads one pair of numbers rather than reasoning about which case
it hit.

`Int` is the whole of arithmetic: an instruction that takes two numbers is
in-domain on two `Int`s and out of it on anything else. Integer arithmetic
wraps, so `i64::MIN` is not a special case anywhere, including `i64::MIN / -1`.

### Division by zero

`Int x / Int 0` and `Int x % Int 0` answer `0`, like any other pair with no
quotient to give. There is no answer to report and no need to invent a
different one for this case than for the rest.

### What junk is not

It is not a second control-flow outcome, and it is not a value a program can
tell apart by looking. `add` answering `0` on two symbols is the same `0` it
answers on `push 0 push 0 add`; the difference is in what was asked, not in what
came back. Whether a program ever *computes on junk* is the static question this
document makes askable and does not answer.

## The coercions

`as_bool`, `as_int` and `as_tuple n` force a value to a type. Each is the
identity where the value is already of that type, and hands back a default
where it is not:

| instruction | on its own type | everywhere else |
|---|---|---|
| `as_bool` | `Bool p` unchanged | `Bool(truthy(v))` |
| `as_int` | `Int x` unchanged | `Int 0` |
| `as_tuple n` | `Tuple` of exactly `n` unchanged | `Tuple` of `n` `()`s |

`as_bool` is exactly `truthy`, so its second column subsumes the first:
`truthy(Bool p) = p` is what makes it the identity on a bool, and nothing else
is needed to say what it does. For `as_tuple n` the width is part of the type,
as it is for `untuple n` — a tuple of the wrong length is as much a mismatch as
a symbol, being precisely the values `untuple n` has no `n` parts to give.

**A coercion is the junk of the table above, named on its own.** `as_int v` is
*defined* as the int if there is one and zero otherwise, which is exactly what
`add` answers with when it has no sum to give; the difference is only that a
coercion is handed a value rather than computing one. So the two halves of the
document are one rule: every instruction lands in a type, and where it has
nothing to land with it lands on that type's default.

What a coercion buys is a **codomain** stated where a program can use it, which
is the one thing this document's totality does not otherwise give you.
Case-splitting a value on `is_int` leaves it opaque in the arm where it is not
one, so no amount of rewriting concludes that what came out is an `Int`; after
`as_int` it is one by construction. Three consequences follow directly, and
`vm::totality_tests` holds the machine to all of them:

```
as_int ; as_int             =  as_int       and likewise for the other two
as_int ; is_int             =  drop ; push true
as_tuple n ; untuple n      =  untuple n
```

The first is why a coercion is idempotent; the second and third are why writing
one is worth more than reading a check. `as_bool` has a fourth: it is the
coercion `not`, `and`, `or` and `branch` already apply to their operands, so it
is absorbed by any of them — `as_bool ; branch` is `branch`.

## Asking the question

The arities in the table above are the ones `assemble` emits. `untuple 3`
leaves three values and `add` leaves one, and a sentence that needs to know
whether the instruction was reaching for something asks **before** it hands the
operands over:

```
#[arity(1, 6)]
sentence shares {
    pick 0
    untuple 3        // leaves 3: the parts, or three ()s
    dip 3 { untuple 3 }
}
```

There is no annotation for this and no way to turn it off. The two questions
worth asking are `is_int`, for anything arithmetic, and

```
pick 0 ; pick 0 ; as_tuple n ; equal
```

for anything about shape: a value is an `n`-tuple exactly when coercing it to
one changes nothing, and the two copies are what leave the value itself
underneath the answer. Both are cheap, both are total, and both are written at
the site that cares rather than at every site that does not.

A site that does not ask is a program deciding to compute on junk. There is no
instruction that turns that decision into a halt — that is what `assert` used to
be — so a site relying on its input's shape has to say what it does when the
shape is wrong. The [`?` operator](hana.md) is the short way to say "hand the
problem back to my caller", and it is written in exactly this shape: ask
`as_tuple 2`, take the result apart in the arm where there is one, and call the
value an error carrying itself in the arm where there is not.

### What the sugar does with it

`type` and `enum` checks used to ask `is_tuple`, then `tuple_length; push n;
equal`, and only then untuple. They ask once:

```
pick 0 ; pick 0 ; as_tuple n ; equal
branch { untuple n; ...element checks... }
       { drop; push false }
```

The value survives into both arms, so the else arm has something to discard
rather than padding to clear. At `n = 0` the coercion is the constant `()` and
the whole check is `push () ; equal`.

## What the laws buy, and what they cost

The point of all this is which local rewrites become sound. The wins:

- **Cancelling against a `drop` needs no whitelist.** Any single-output
  operator cancels against a following `drop`, becoming drops of its inputs.
- **Constant folding is *evaluation*.** Folding a literal window is running it,
  so anything the VM computes may be folded.
- **A branch on any literal folds**, since the direction on junk is defined.
- **`tuple n; untuple n` is still one-way.** It is the identity; `untuple n;
  tuple n` is not — it *junk-normalizes*, mapping every non-`n`-tuple to
  `((), …, ())`. That normalization has a name now: `untuple n; tuple n` is
  `as_tuple n`, which is a law rather than a warning.

And two things that did **not** become free.

### Copying before untupling, and what the guard costs

The rule one wants is

```
pick 0; untuple n   ==   untuple n; (pick (n-1))^n; dip n { tuple n }
```

justified under the old semantics by "both sides panic on exactly the inputs
where `x` is not an `n`-tuple". With no panic left to agree about, the two sides
visibly differ: the left keeps `x`, and the right hands back `untuple n;
tuple n` of `x` — which is to say `as_tuple n` of `x`. Sound before, unsound
after; the rule was *relying* on partiality to hide a normalization.

So it has to buy the condition back, and the guard it buys it with is the one
the whole language now uses:

```
pick 0; untuple n
  ==
pick 0; pick 0; as_tuple n; equal;
branch { untuple n; (pick (n-1))^n; dip n { tuple n } }
       { (tuple 0)^n }
```

Both arms are exact: on the then side the parts rebuild `x` because `x` was an
`n`-tuple, and on the else side the left's own answer is `x` under `n` `()`s,
which is what the arm pushes. The guard is four instructions and states the
domain exactly, where the old `is_tuple; tuple_length; push n; equal` prologue
was five and stated it in pieces.

That prologue has since become one instruction rather than four: `is_tuple`
takes an optional width, and `is_tuple n` is the whole question. The width is
part of the type in exactly the sense `untuple n` means it — a tuple of the
wrong length is as much a mismatch as a symbol, being precisely what `untuple
n` could not take apart — so the test that guards an `untuple n` or an
`as_tuple n` asks it in one place instead of assembling it from three. The
width stays *optional* on the test and required on the coercion: "a tuple of
some length" is a question with an answer, and it is what the surface's bare
`tuple` type spec means, but it is not a coercion anything could perform.

So the guard is shorter again, and the sugar is written with it:

```
pick 0 ; is_tuple n
branch { untuple n; ...element checks... }
       { drop; push false }
```

The `?` operator's guard is the same question and is written the same way —
`copy ; is_tuple 2`, where it used to copy twice, coerce one copy and compare.

Shortening it took a **law**, not just an instruction, and that is the part
worth recording. The coercing guard handed the rewriter an `equal` against a
value `tuple n` built, which `as-tuple-built` and the folding rows take apart;
a guard that asks `is_tuple n` hands over a test instead, and a test of a
built tuple had no row at all. Written without one, the barista's contract
claim stalls on a nest of `tuple n ; is_tuple n` nobody can decide. The row is
`as-tuple-built`'s sibling — `tuple m ; is_tuple n` = `tuple m ; push (m ==
n)`, the tuple kept for its other readers the way that law keeps it — and with
it in the table the claim closes in fewer rewrites than it did before, there
being less guard to rewrite.

### The single-arm hoist, which totality *did* buy

This is the payoff the whole change was for, and it arrives by a different road
than expected. The obvious hoist

```
branch { untuple 3; A } { B }   →   dip 1 { untuple 3 }; branch { A } { tuple 3; B }
```

does **not** work as written. It used to invent a panic on the path that took
the other arm; then it *junk-normalized* a value that `B` goes on to use, with
`tuple 3` unable to put it back.

Recovering `x` in the else arm is not available either: what `untuple n` left
there is `()`s, and no instruction after the fact says what they stood for.
Recovering would mean asking `as_tuple n` before the branch and threading the
answer into the arm, which is more machinery than the alternative needs.

**The hoist does not need an inverse. It needs a copy**:

```
branch { X; A } { B }
  ==
dip 1 { (pick (n-1))^n; X };  branch { dip m { drop^n }; A } { drop^m; B }
```

for `X : n -> m`. Run `X` speculatively on a *copy* before the branch, and let
each arm discard the half it did not want. The losing path never gives up its
own values, so nothing has to be reconstructed and `untuple n` is asked nothing
that `add` is not asked.

What this needs is exactly what this document establishes:

- `X` must be **total**, or the speculation fails on a path the original left
  alone. This is the whole reason the rule is possible; under the old semantics
  it was unsound for precisely the `untuple` case that matters, and it is why
  everything now is.
- `X` must have **no effect but the stack**.
- `X`'s arity must be **known locally**, which excludes calls — a call's arity
  lives in the library rather than the window.

Under the old semantics this rule was unsound for precisely the `untuple` case
that makes it worth having. Totality is what makes it statable at all: no
reconstruction, no guard, no imaginary values.

## What is not covered

- **A static safety judgment.** "This program never computes on junk" is exactly
  the question this document makes askable, and nothing here answers it. The
  previous Z3 typechecker modelled the old partial semantics and has been
  removed; anything that replaces it should be generated from the table above.

  `emit_does_pre_and_post` in `hana/barista.hana` is the smallest interesting
  instance: a program that should answer `true` on every input, where seeing
  why requires noticing that the precondition two branches earlier already
  established what the postcondition goes on to ask. Nothing in the workspace
  can say so today.

- ~~A way to discharge an `identity`.~~ `bin/prove` does, by equality
  saturation over the term model — see [docs/proving.md](proving.md). It
  inherits the laws this document makes sound, and two of them precisely:
  totality is what licenses discarding work (`drop-nat`) and reordering
  disjoint computations, and determinism is what licenses sharing them
  (`copy-nat`).
