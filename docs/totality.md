# Totality

Every **data** operation in the hanoi bytecode is a total function. An
operation applied to operands it was not written for does not fail; it returns
a **deterministic default**, called *junk* below, and — if it is one of the
twelve **fallible** instructions — a `bool` saying so. Failure is a separate
thing, reached only by the three instructions whose whole job is to fail, and
ruled out by `#[total]`.

This document is the normative specification of that. The fallible table is the
spec; `vm::totality_tests` is its executable mirror.

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
  It now folds any literal, `push 1; branch` taking the then arm.
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
| `assert` | `!truthy(v)`, i.e. `v == Bool(false)` |
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

### Claiming otherwise: `#[total]`

A sentence may declare that it *cannot* fail — that it neither executes one of
those three nor reaches anything that does, through a `jump`, a `dip` or either
branch arm. That is `#[total]`, and the compiler checks it.

The claim is **opt-in**, and the polarity is the whole design. The opposite —
requiring `#[partial]` on anything that can fail — was tried and collapsed under
its own coverage. It needed an exemption for branch arms, which have no source
to annotate; another for `test` declarations, where asserting is the point; and
worst of all one for composer templates, which are generic over the machine they
wrap and so are partial exactly when their argument is. Marking those partial
would have made *every* composed machine partial, and in a corpus where nearly
everything is composed that is enough to make the annotation say nothing.

Turning it around removes all three cases at once. Nothing is obliged to carry
an annotation, so generated code, inline blocks and tests need no special
treatment — they simply make no claim. What is checked is exactly what somebody
asserted.

And the *fact* is available everywhere regardless. `failure_reachability` is a
least fixpoint over the call graph and answers for every sentence, annotated or
not; `check_totality` is just the part that compares it against the claims. On
the `tests/` corpus **2189 of 3409 sentences are provably total**, with 58
carrying a checked `#[total]` — the `type` and `enum` sugar puts one on each
predicate it generates, which used to be an unverified assertion.

That count went *down* when the corpus started reading its flags rather than
having them dropped for it, and the drop is the measurement getting honest
rather than the corpus getting worse. A discarded flag cannot fail, so every
sentence that untupled a value it had no reason to trust counted as total while
quietly computing on junk. Saying `assert` instead records the reliance those
sentences always had — the reliance the pre-totality `untuple` enforced by
panicking.

The check is syntactic and therefore conservative: an `assert` on a branch that
cannot be taken still counts against the claim. That is the same bargain
`#[recursive]` makes, and it is what keeps this a reachability question rather
than a proof obligation.

## Truthiness

```
truthy(v)  =  (v != Bool(false))
```

**`false` is the unique falsy value.** A number, a symbol, a tuple — anything
that is not literally `false` — is true.

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
fallible instructions' flags all produce genuine `Bool`s, so they read the same
under either rule. What differs is only what happens to a value that was never
a boolean at all, and there "carry on" is the less surprising reading than
"take the failure path".

What it costs is `assert`, which fails exactly when its operand is falsy and so
now **passes on junk**. Only a literal `false` fails an assertion. An `assert`
here therefore checks that something did not definitely go wrong, rather than
that it definitely went right; a check that wants the stronger reading has to
say `push true equal assert` — or, better, come from an instruction that reports
with a flag, which is what the flags are for.

The change was made deliberately and is invisible to the corpus: every one of
the 64 `.hana` integration tests runs the identical number of VM steps under
either rule, because nothing in real code lets a non-boolean reach a branch.

## The fallible table

Every data operation is total. A **fallible** one additionally reports whether
its answer was computed or invented, by leaving a `bool` on top of its result.
`()` below is the empty tuple, `Value::unit()`.

| instruction | arity | on success | off its domain |
|---|---|---|---|
| `push c`, `pick d`, `roll d`, `drop` | unchanged | — | cannot fail |
| `equal`, `is_int`, `is_bool`, `is_float`, `is_symbol`, `is_tuple` | unchanged | — | cannot fail |
| `not`, `and`, `or`, `tuple n` | unchanged | — | cannot fail |
| `add`, `subtract`, `multiply` | `2 -> 2` | sum, `true` | `Int 0`, `false` |
| `divide`, `modulo` | `2 -> 2` | quotient, `true` | `Int 0`, `false` |
| `greater`, `less` | `2 -> 2` | the answer, `true` | `false`, `false` |
| `negate` | `1 -> 2` | `-x`, `true` | **`x`**, `false` |
| `tuple_length` | `1 -> 2` | the count, `true` | **`x`**, `false` |
| `symbol_len` | `1 -> 2` | the count, `true` | **`x`**, `false` |
| `symbol_char_at` | `2 -> 2` | the code point, `true` | `Int 0`, `false` |
| `untuple n` | `1 -> n+1` | the `n` elements, `true` | **`x`**, `()` × (n-1), `false` |
| `branch` | unchanged | then arm unless `Bool(false)` | cannot fail |
| `assert`, `assert_eq`, `panic` | unchanged | — | **panics** |

Two rules govern the rest of the table.

**The arity is fixed whichever way it goes.** A caller's stack does not depend
on the data, so the arity checker still works on shape alone, and every rule
that moves code past an instruction reads one pair of numbers rather than
reasoning about which branch it took. That is why failure pads with junk rather
than leaving fewer values.

**Failure preserves its inputs where the output arity has room.** The bolded
cells above are the instructions with one input and two slots: they hand the
value straight back, and `untuple n` keeps it in the deepest of the `n` slots it
filled with `()` padding above. Where there is no room — two operands and two
slots, as in `add` — the result slot takes a default instead, which is why
`add` does not bother.

That second rule is what makes the flag a tag on the **stack** rather than
inside `Value`. Untupling is now recoverable: read the flag, and either the
parts rebuild the value or the value is still sitting there. `Tuple` stays a
free constructor and no hana program can write a junk value, because there is
no junk value to write.

Where an instruction takes two numbers, a mixed `Int`/`Float` pair is in-domain
and promotes to `Float`. Integer arithmetic wraps, so `i64::MIN` is not a
special case anywhere, including `i64::MIN / -1`.

### Division by zero

Two worlds, deliberately kept apart:

- **Integer**: `Int x / Int 0` and `Int x % Int 0` **fail**, leaving `0` and
  `false`. There is no answer to report and now no need to invent one.
- **Float**: uniformly IEEE, and a **success**. `1.0 / 0` is `inf` and `1.0 % 0`
  is `NaN`, which is what `1.0 / 0.0` already did — an `Int` divisor coerces
  like any other mixed operand rather than being an excuse to leave the float
  world.

### What the flag is not

It is not a second control-flow outcome. A fallible instruction always
completes and always leaves the same number of values; the flag is data, and a
program is free to ignore it.

## Reading the flags

The arities in the table above are the ones `assemble` emits. `untuple 3`
leaves four values, `add` leaves two, and a sentence that writes one is
expected to say what happens when it is false:

```
#[arity(1, 8)]
sentence shares {
    pick 0
    untuple 3        // leaves 4: three parts and a flag
    dip 4 { untuple 3 }
}
```

There is no annotation for this and no way to turn it off. For one change there
was: `assemble` used to splice a `drop` in after every fallible instruction
unless a sentence said `#[flags]`, so that source written against the old
arities kept working while the corpus was converted. That scaffolding is gone
now that every sentence has been converted, which is what keeps a branch arm
from having a different instruction set than the sentence that wrote it.

Converting took the two answers a flag admits, and which one a site wants is
not a matter of taste:

* **`assert` the flag.** The sentence relies on its input being the shape it
  expected, so it says so. This is what the pre-totality instruction did, which
  is why the whole suite kept its step counts across the conversion: one
  flag-drop `assemble` used to splice in became one `assert` in the source.
* **Read it.** Where the code was already computing the answer the flag
  carries, the guard goes and the branch reads the flag instead — see the sugar
  below. This is the only answer available to a `#[total]` sentence, since
  `assert` would cost it the claim.

A third answer is honest only where the code genuinely does not care: an
explicit `drop`. It appears in rewriter fixtures whose subject is a rule's
window rather than the value, and nowhere in the corpus — a program that drops
a flag is a program that has decided to compute on junk, which is what the
implicit drop did for everyone.

### What the sugar does with it

`type` and `enum` checks used to ask `is_tuple`, then `tuple_length; push n;
equal`, and only then untuple — three instructions to recompute what `untuple`
reports for free. They now ask once:

```
untuple n
branch { ...element checks... }
       { drop^n; push false }
```

The else arm clears the slots `untuple` filled — the value itself in the
deepest, `()` padding above it — and answers `false`. No `assert` anywhere, so
the check keeps its `#[total]`. At `n = 0` the flag *is* the predicate and the
body is a bare `untuple 0`.

## What the laws buy, and what they cost

The point of all this is which rewrites become sound. The wins:

- `annihilate_drop` needs no whitelist. Any single-output operator cancels
  against a following `drop`, becoming drops of its inputs.
- `fold_const` and `fold_const_unary` are *evaluation*. Folding a literal
  window is running it, so anything the VM computes they may compute.
- `fold_branch` folds **any** literal condition, since the direction on junk is
  defined.
- `cancel_tuple` is unchanged, and still one-way. `tuple n; untuple n` is the
  identity; `untuple n; tuple n` is not — it *junk-normalizes*, mapping every
  non-`n`-tuple to `((), …, ())` rather than panicking. A different function, so
  still not removable.

And two things that did **not** become free.

### `rebuild_copy`, and what the flag paid for

The old rule was

```
pick 0; untuple n   ==   untuple n; (pick (n-1))^n; dip n { tuple n }
```

justified by "both sides panic on exactly the inputs where `x` is not an
`n`-tuple". With no panic left to agree about, the two sides visibly differ: the
left keeps `x`, and the right hands back `untuple n; tuple n` of `x`. Sound
before, unsound after — the rule was *relying* on partiality to hide a
normalization.

While untupling junk was untagged, nothing recovered `x` from the parts, and the
rule had to buy the condition back with a `tuple_length; push n; equal` guard.
It does not any more:

```
pick 0; untuple n
  ==
untuple n;
branch { (pick (n-1))^n; dip n { tuple n }; push true }
       { dip (n-1) { pick 0 }; push false }
```

**The guard the rewrite needs is the one the instruction already computed.** No
recomputation, no `is_tuple`, and an else arm with something to say rather than
junk to invent — the value `untuple n` could not take apart is still sitting in
the deepest of the slots it filled. Both arms are exact.

That is the clearest single argument for putting the flag on the stack.

### The single-arm hoist, which totality *did* buy

This is the payoff the whole change was for, and it arrives by a different road
than expected. The obvious hoist

```
branch { untuple 3; A } { B }   →   dip 1 { untuple 3 }; branch { A } { tuple 3; B }
```

does **not** work as written. It used to invent a panic on the path that took
the other arm; then it *junk-normalized* a value that `B` goes on to use, with
`tuple 3` unable to put it back.

The flag changes what is *possible* here — `untuple n` preserves its input on
failure, so the else arm could read the flag and recover `x` — but it does not
make the rewrite above correct, because that rewrite reads no flag. Recovering
would mean branching on it inside the arm, which is more machinery than the
alternative needs.

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
  it was unsound for precisely the `untuple` case that matters.
- `X` must have **no effect but the stack**.
- `X`'s arity must be **known locally**, which excludes calls — their bodies may
  hold an `assert`.

That is `speculate_branch` in `bin/rewrite`, and
`the_direct_route_closes_by_speculating` runs the whole derivation the sharing
problem was stuck on: hoist the arm's `untuple`, `sink` it back onto the check's,
`dup_natural` merges the two. No reconstruction, no guard, no imaginary values.

## What is not covered

- **Float `equal`.** `0.0 == -0.0` holds while the two stay distinguishable, so
  `equal` is not identity. That predates this change and is why
  `specialize_equal` declines anything with a float in it.
- **A static safety judgment.** "This program never computes on junk" is exactly
  the question this document makes askable, and nothing here answers it. The
  previous Z3 typechecker modelled the old partial semantics and has been
  removed; anything that replaces it should be generated from the table above.
