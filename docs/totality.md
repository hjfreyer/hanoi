# Totality

Every **data** operation in the hanoi bytecode is a total function. An
operation applied to operands it was not written for does not fail; it returns
a **deterministic default**, called *junk* below. Failure is a separate thing,
reached only by instructions whose whole job is to fail.

This document is the normative specification of that. The junk table is the
spec; `vm::totality_tests` is its executable mirror, one assertion per row.

## Why total

The rewriter in `bin/rewrite` proves programs equal by splicing local windows.
Two programs that compute the same values are still not interchangeable if one
of them *rejects* an input the other accepts, so as long as ordinary operators
could fail, every rule had to carry a panic-preservation side condition, and
those conditions are not window-local. The damage was visible everywhere:

- `annihilate_drop` fired only on a hand-maintained whitelist of instructions
  that "cannot panic", so `add; drop` was not `drop; drop`.
- `fold_const` declined `push 1; push 2; and`, because `push false` is not a
  panic and the original was.
- `fold_branch` needed a literal `Bool`, because `push 1; branch` was a panic.
- `rebuild_copy` existed at all in order to launder an opaque value into a
  syntactically total shape, and even then the *reverse* — hoisting a partial
  computation out of a single branch arm — stayed out of reach.

Making the data operations total moves the question. Equivalence is now over
total functions, which a local window can decide. Whether a program is
*meaningful* — whether it ever computes on junk — becomes a separate static
judgment, layered on top rather than tangled into the equational theory.

## The partiality contract

Exactly three instructions can fail for a **semantic** reason, and they are the
three that exist to:

| instruction | fails when |
|---|---|
| `panic` | always |
| `assert` | `!truthy(v)` |
| `assert_eq` | `a != b` |

Everything else that can still stop a run is **meta-level or structural**, not a
property of the values:

| fault | where |
|---|---|
| stack underflow | `pop`/`peek`, and `drop`/`pick`/`roll`/`dip`/`tuple` |
| invalid sentence index | `execute`'s dispatch |
| gas limit exceeded | the step counter |

Structural faults are ruled out ahead of time rather than handled: arity
checking is mandatory on every `assemble` path (`bytecode/src/assembly.rs`), so
a sentence that would underflow does not assemble. The one remaining gap is an
entry point whose inferred arity has `inputs > 0` — it assembles, and then
underflows when run with an empty stack.

## Truthiness

```
truthy(v)  =  (v == Bool(true))
```

Applied **per operand**, and every boolean-shaped instruction is defined through
it:

| instruction | definition |
|---|---|
| `not v` | `Bool(!truthy(v))` |
| `a and b` | `Bool(truthy(a) && truthy(b))` |
| `a or b` | `Bool(truthy(a) \|\| truthy(b))` |
| `branch { A } { B }` | `A` iff `truthy(cond)`, else `B` |
| `assert v` | fails iff `!truthy(v)` |

Per-operand coercion is load-bearing rather than incidental. It is what makes De
Morgan hold on *all* values, not just booleans: `not (a and b)` is
`!(truthy a && truthy b)`, and `(not a) or (not b)` is
`truthy(Bool(!truthy a)) || truthy(Bool(!truthy b))` — the same thing, because
`truthy(Bool(p)) = p`. Coercing the pair jointly, or making `and` return its
operand, would both break that.

One consequence is surprising and correct: **`not junk = true`**. Junk is not
`true`, so it is falsy, so its negation is `true`. There is no third truth
value; that is the price of the two-valued definition and it is worth paying.

**A branch takes the else arm on junk.** The then arm is reached only by a
literal `Bool(true)`. This agrees with junk-being-falsy everywhere else, and it
is why `fold_branch` can now fold any literal.

## The junk table

`()` below is the empty tuple, `Value::Tuple(vec![])`.

| instruction | defined on | result elsewhere |
|---|---|---|
| `push c` | everything | — |
| `equal` | everything | — |
| `is_int`, `is_bool`, `is_float`, `is_symbol`, `is_tuple` | everything | — |
| `print` | everything | — |
| `tuple n` | any `n` values | — |
| `not` | everything | `Bool(!truthy(v))` |
| `and`, `or` | everything | `Bool(truthy(a) ⊕ truthy(b))` |
| `greater`, `less` | two numbers | `Bool(false)` |
| `add`, `subtract`, `multiply` | two numbers | `Int(0)` |
| `divide`, `modulo` | two numbers | `Int(0)` — see below |
| `negate` | a number | `Int(0)` |
| `untuple n` | an `n`-tuple | `n` copies of `()` |
| `tuple_length` | a tuple | `Int(0)` |
| `symbol_len` | a symbol | `Int(0)` |
| `symbol_char_at` | a symbol and an in-range index | `Int(0)` |
| `branch` | everything | else arm unless `Bool(true)` |
| `assert` | a truthy value | **panics** |
| `assert_eq` | two equal values | **panics** |
| `panic` | nothing | **panics** |

Where an instruction takes two numbers, a mixed `Int`/`Float` pair is still
in-domain and promotes to `Float`, exactly as before. "Elsewhere" means at least
one operand is not a number at all.

Integer arithmetic wraps (`wrapping_add` and friends), so `i64::MIN` is not a
special case anywhere, including `i64::MIN / -1`.

### Division by zero

Two worlds, deliberately kept apart:

- **Integer**: `Int x / Int 0 = Int 0` and `Int x % Int 0 = Int 0`. Following
  Lean, which totalizes division the same way rather than inventing an error
  value.
- **Float**: uniformly IEEE. The old special case that rejected `Float / Int 0`
  is gone — the `Int 0` coerces to `0.0` like any other mixed operand, so
  `1.0 / 0` is `inf` and `1.0 % 0` is `NaN`, which is what the same expression
  written `1.0 / 0.0` already did.

An `Int` divisor is not an excuse to leave the float world.

### Untupling is not tagged

`untuple n` on a non-tuple, or on a tuple of the wrong size, pushes `n` copies
of `()`. It does **not** push a tagged `J_n(x)` that remembers what it came
from, and `Tuple` stays a free constructor with no junk inhabitants of its own.

That is a real choice with a real cost, paid in the next section. The gain is
that the value domain stays exactly what a hanoi programmer can write.

## What the laws buy, and what they cost

The point of all this is which rewrites become sound. The wins:

- `annihilate_drop` needs no whitelist. Any single-output operator other than
  `print` cancels against a following `drop`, becoming drops of its inputs.
- `fold_const` and `fold_const_unary` are *evaluation*. Folding a literal
  window is running it, so anything the VM computes they may compute.
- `fold_branch` folds **any** literal condition, since the direction on junk is
  defined.
- `cancel_tuple` is unchanged, and still one-way. `tuple n; untuple n` is the
  identity; `untuple n; tuple n` is not — it *junk-normalizes*, mapping every
  non-`n`-tuple to `((), …, ())` rather than panicking. A different function, so
  still not removable.

And two things that did **not** become free.

### `rebuild_copy` needed a guard

The old rule was

```
pick 0; untuple n   ==   untuple n; (pick (n-1))^n; dip n { tuple n }
```

justified by "both sides panic on exactly the inputs where `x` is not an
`n`-tuple". With no panic left to agree about, the two sides now visibly differ:
the left keeps `x`, and the right hands back `untuple n; tuple n` of `x`, which
on junk is `((), …, ())`. Sound before, unsound now — the rule was *relying* on
partiality to hide a normalization.

Since untupling is untagged, nothing recovers `x` from the parts, so the rule
has to test instead:

```
pick 0; untuple n
  ==
pick 0; tuple_length; push n; equal;
branch { untuple n; (pick (n-1))^n; dip n { tuple n } }
       { (push ())^n }
```

for `n >= 1`. The guard needs no `is_tuple`: `tuple_length` of a non-tuple is
`Int 0`, which fails `= n`. The else arm needs no `untuple` either — in that arm
the answer is *known* to be `n` copies of `()`, which is the totality contract
paying for the guard it just required. The "construction is the proof" payload
lives in the then arm, where it always did.

### The single-arm hoist is still impossible

```
branch { untuple 3; A } { B }   →   dip 1 { untuple 3 }; branch { A } { tuple 3; B }
```

was blocked because `untuple` was partial and the hoist invented a panic on the
path that took the other arm. It is still blocked, for a new reason: on that
path the hoisted `untuple 3` now *junk-normalizes* a value that `B` may go on to
use, and `tuple 3` does not put it back. Totality removed the panic, not the
information loss. A tagged junk value would have closed this; the table above
chose not to have one.

## What is not covered

- **Float `equal`.** `0.0 == -0.0` holds while the two stay distinguishable, so
  `equal` is not identity. That predates this change and is why
  `specialize_equal` declines anything with a float in it.
- **A static safety judgment.** "This program never computes on junk" is exactly
  the question this document makes askable, and nothing here answers it. The
  previous Z3 typechecker modelled the old partial semantics and has been
  removed; anything that replaces it should be generated from the table above.
