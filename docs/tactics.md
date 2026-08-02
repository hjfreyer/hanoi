# Tactics

`bin/rewrite` turns one sentence's compiled bytecode into a tree and prints it.
A **tactic** says how to rewrite that tree before printing.

Nothing is expanded unless you ask. The default listing shows one sentence,
naming every call it makes on a single line; `inline` is how you open one up.

```bash
cargo run --bin rewrite -- tests 'SimpleTuple::check' -t dip_normalize
```

A rewriting system has three separable parts, and a tactic is what makes the
second and third of them things you say rather than things the tool decides:

1. **Rules** — a fixed set of local transformations.
2. **Control** — order, choice, repetition.
3. **Traversal** — where in the tree to look.

## Rules

Every rule is a local splice on a window of at most two nodes. It either matches
and returns a replacement, or fails. `--list-rules` prints them.

| rule | window | replacement |
|---|---|---|
| `collapse` | `dip k { dip j { B } }` | `dip (k+j) { B }` |
| `expand` | `dip k { B }`, `k >= 2` | `dip 1 { dip (k-1) { B } }` |
| `factor_branch` | `branch { X A } { X B }` | `dip 1 { X }; branch { A } { B }` |
| `sink` | `X ; dip k { S }` | `dip (k-m+n) { S } ; X` |
| `fuse` | `dip k { A }; dip k { B }` | `dip k { A B }` |
| `annihilate_drop` | `X ; drop` | nothing, or `drop` |
| `pick_drop_to_roll` | `pick d ; dip (d+1) { drop }` | `roll d` |
| `noop` | `roll 0`, or an empty `dip` | nothing |
| `flatten_call` | `dip 0 { P }` | `P`, spliced in |
| `distribute_branch` | `branch { A } { B } ; X` | `branch { A X } { B X }` |
| `fold_branch` | `push true \| false ; branch { A } { B }` | the arm it selects |
| `inline` | a call | the block it names, spliced in |

`sink` is the interchange rule, and its side condition is the one piece of real
arithmetic here: writing `X`'s arity as `(n -> m)`, the dip's window must sit
entirely below everything `X` leaves behind — that is `k >= m` — and the same
window is `k - m + n` deep on the other side. One formula covers `push` (0→1),
`drop` (1→0), arithmetic (2→1), `pick d` (d+1→d+2), `roll d` (d+1→d+1) and a
nested dip alike.

`annihilate_drop` only fires for instructions that cannot panic: `push` and
`pick` cancel entirely, and the five `is_*` predicates leave the drop behind
(they consume a value to make the dropped one). `add; drop` is deliberately not
`drop; drop` — the add still rejects non-numeric operands, and cancelling it
would discard that check.

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

`inline` **splices**: the callee's body lands in the caller's sequence, with no
frame left behind. That matters more than it sounds, because rules only ever
see one sequence — leaving a `dip 0` wrapper would put the expanded code
somewhere no other rule could reach it, and `inline` would compose with almost
nothing. A `dip k` call for `k > 0` does keep its frame, since there the frame
is what the instruction means.

The cost is provenance: spliced code no longer says which sentence it came
from. That is exactly why nothing inlines by default — the un-expanded listing
names every call on one line, and you flatten only what you mean to.

```
$ rewrite tests 'State::check'                    #   48 lines, every call named
$ rewrite tests 'State::check' -t 'once(inline)'  #   69, one call opened
$ rewrite tests 'State::check' -t inline_all      # 1085, one flat sentence
```

Because splicing rescans where it landed, `each(inline)` already expands a
whole sequence transitively; `bu` is what additionally reaches into branch
arms. To expand *less*, use `once`, which takes a single call — and note that
it works on one sequence, so `repeat_n(k, once(inline))` counts calls at the
level you are looking at rather than descending into arms.

`flatten_call` does for a stray `dip 0` what `inline` does for a call. It is no
longer needed after inlining, which splices directly, but `sink` can still
produce one: `push 1; dip 1 { X }` becomes `dip 0 { X }; push 1`.

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
| `bu(t)` | children first, then here |
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
`factoring`, `annihilate`, `cleanup`, `distribute`, `flatten`, `all` and
`dip_normalize`. With no `-t` you get `default`, which is `id` — nothing is
expanded and nothing is rewritten. The first four plus
`dip_normalize` reproduce what the old `--dip-normalize`, `--factor-branches`
and `--annihilate` flags did.

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
