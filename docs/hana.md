# Hanoi Assembly (Hana) Reference Guide

This document provides a detailed reference for Hanoi Assembly (`.hana` files), covering the execution model, syntax conventions, instruction set details, and key gotchas when writing stack-based assembly code.

---

## 1. Execution Model & Stack Mechanics

Hanoi is a stack-oriented VM-executed language. Almost all instructions interact directly with a central value stack by pushing or popping elements.

### Value Types
The stack can contain elements of the following types:
- **Bool**: `true` or `false`.
- **Int**: Signed 64-bit integers (e.g., `42`, `-1`).
- **ConstString**: Immutable text (e.g., `const_string greeting "hello"`, or the literal `"hello"`). Two const strings are equal exactly when they read the same, and `const_string_len` and `const_string_char_at` read one.
- **Symbol**: A unique identity and nothing else (e.g., `symbol my_event`). Two declarations are two symbols, whatever they are named; a symbol carries no text, and prints as the fully qualified path it was declared under.
- **Tuple**: Nested structures grouping zero or more values (e.g., `(foo, (bar, 42))`).

A symbol is for a name a program *compares*; a const string is for text a program *reads*. Declaring one of each looks the same, but only the const string has characters to ask about:

```hana
symbol idle                       // an identity
const_string greeting "hello"     // five characters

sentence example {
    push idle
    const_string_len   // fails: a symbol has no text — the flag says so
    drop 0
    drop 0

    push greeting
    const_string_len   // 5, true
    drop 0
}
```

---

## 2. Tuple and Untuple Ordering

A tuple keeps the order its elements had on the stack: `tuple N` is a bracket
drawn around the top $N$ slots, and nothing inside it moves.

### Building a tuple
When you call `tuple N` (where $N > 0$), the top $N$ values leave the stack and
become the tuple's elements in the order they were sitting in. The **deepest**
of them is index 0 and the **top of the stack** — the one pushed last — is the
last element.

#### Example:
```hana
push bar
push foo
tuple 2
```
1. `push bar` puts `bar` on the stack.
2. `push foo` puts `foo` on the stack (at the top).
3. `tuple 2` takes both, `bar` first because it is deeper.

The resulting tuple on the stack is:
`(bar, foo)`

Written out, a tuple literal reads in push order: `push (bar, foo)` leaves the
same value as the three lines above.

### Symmetrical Destructuring with Untuple
`untuple N` pops a tuple and pushes its elements back in index order, index 0
first, so the **last element ends up on top** — exactly the slot it came from.

#### Example:
```hana
// Stack: [(bar, foo)]
untuple 2
// Stack now: [bar, foo] (where foo is at the top of the stack)
```

This symmetry allows a sequence of `tuple N` followed by `untuple N` to restore
the stack to its exact original state prior to tuple creation.

> [!NOTE]
> A stack listing and a tuple read the same way round: the rightmost element of
> `(bar, foo)` is the top of the stack, just as it is in `[bar, foo]`.

---

## 3. Sentences vs. Functions

Hanoi distinguishes between two types of execution blocks:

### Sentences
Declared using the `sentence` keyword. A sentence is an arbitrary sequence of bytecode instructions. It has no default arity or structural constraints.
```hana
sentence my_sentence {
    push 10
    push 20
    add
}
```

### Functions
Declared using the `function` keyword. A function is a specialized sentence representing a stack mapping that takes **exactly one input** and returns **exactly one output**. 
```hana
function double_value {
    pick 0
    add
}
```
> [!IMPORTANT]
> The parser automatically attaches an arity annotation of `#[arity(1, 1)]` to any block declared with the `function` keyword. If a function's instructions result in a different stack size transition, it will fail the arity check at compile time.

### Tests
Declared with `test` in front of `sentence`. `bin/test-runner` runs each one in
a fresh VM and reads what it left behind.

**A test answers with a result.** `((), ok)` says every check it made held;
`(payload, err)` says one did not, and the payload says what it saw. Nothing
about a failing test halts the machine — the runner prints the payload:

```
test arithmetic::add_numbers ... FAILED (err (5, 6)) (14 steps)
```

The checks come from `crate::prelude`, which is also where the tags come from:

- `check_equals` compares the top two values, and answers `((), ok)` or
  `((a, b), err)` with the pair that did not match.
- `check_true` is `check_equals` against `true`.

Each check is followed by [`?`](#the--operator), which carries the first failure
out of the test and leaves the `()` an ok carries for the `drop 0` after it. The
last check needs neither: it *is* the answer.

```hana
test sentence add_numbers {
    push 2
    push 3
    add
    jump crate::prelude::check_true   // the flag `add` left
    ?
    drop 0
    push 5
    jump crate::prelude::check_equals // the answer this test hands back
}
```

A test that ends on something else — cleaning up a machine state, say — says so
itself with `push ((), crate::prelude::ok)`.

A check inside a `dip` body or a branch arm cannot use `?`, since `?` reaches
only to the end of the sentence it is written in (see [the `?`
operator](#the--operator)). Such a check has to carry its answer out by hand.

A **test machine** — `test mod` — is a different thing with a different
protocol, driven by `prelude::start`, `prelude::pass` and `prelude::fail`. See
[docs/machines.md](machines.md).

### Identities
Declared using the `identity` keyword, and not a program at all: it *claims*
that two programs are interchangeable.

```hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

Both sides are written inline. Naming two sentences that already exist is
`{ jump a } = { jump b }`, so there is one form rather than two. The compiler
checks that the two sides leave the stack the same — the net change, not the
arity, since `pick 1 ; drop` = nothing is `(2 -> 2)` against `(0 -> 0)`.

Nothing calls an identity and nothing runs it, so it takes no `export` or `test`
marker, and only `#[arity]` means anything on one. The tactic that
*proves* it lives out of line, in the `.hant` beside the `.hana`, and
`bin/prove` checks that every stated identity has one. See
[docs/identities.md](identities.md).

---

## 4. Contract Annotations

Hanoi supports static checking at compile time via attributes. `#[arity]` is checked by the compiler today; `#[precondition]` and `#[postcondition]` were verified by the `typecheck` tool, currently removed from the codebase along with its Z3 dependency (see [docs/typecheck.md](typecheck.md) for the design):

- `#[arity(inputs, outputs)]`: Declares the stack arity (required for sentences that do not use the default `function` arity of `1 -> 1`).
- `#[precondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the input for the annotated function to be considered safe to call.
- `#[postcondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the output, given the precondition (if any) held on the input.

Precondition/postcondition functions are ordinary `1 -> 1` functions, but they are commonly generated with the `type`/`enum` sugar rather than written by hand:

- `type Name <spec>;` declares a value predicate from a spec of primitive type names (`int`, `bool`, `const_string`, `symbol`, `tuple`), literal values (including `"strings"`), tuples (`(spec, spec, ...)`), `|`-separated unions, or paths to other `type`/`enum` checks or `symbol`s. It expands to `mod Name { sentence check { ... } }`, exported.
- `enum Name { Variant(spec, ...), ... }` declares a tagged union: each `Variant` gets its own submodule with a fresh `tag` symbol and a `Body::check` for its payload tuple, and `Name::check` accepts any `(payload, tag)` pair matching one of the variants — the tag on top, where the code that reads it wants it.

### Example
```hana
function is_int_fn {
    is_int
}

#[precondition(is_int_fn)]
#[postcondition(is_int_fn)]
function identity {
    // returns input unchanged
}

type TestInt int;
type IntOrBool int | bool;

enum MyEnum {
    Case1(int, bool),
    Case2(symbol),
    Case3(),
}
```

---

## 5. Control Flow and Subroutines

- **Jumps**: Subroutine execution is initiated via `jump S`, which pushes the return address to a call stack and jumps to sentence `S`. Reaching the end of `S` pops the return address and returns control to the caller.
- **Dips**: `dip N { block }` (or `dip N S`) runs a block with the top `N` stack values hidden from it, restoring them on top of whatever the block leaves behind. `N` may be omitted, in which case it is 1. This is `jump` with an offset into the stack: `dip 0 S` and `jump S` are the same instruction.
- **Branches**: Conditional execution is implemented via `branch { then_block } { else_block }`. The VM pops the top stack element; if it is truthy, it executes `then_block`, otherwise it executes `else_block`. Truthiness is `v != false`, so only a literal `false` reaches the else block.
- **Nothing halts**: there is no instruction that ends a run over a value. A sentence that finds its input the wrong shape says so by answering — see [`?`](#the--operator) and [docs/totality.md](totality.md).

### Recursion is forbidden

**A sentence may not reach itself.** Not through a `jump`, not through a `dip`,
not through a branch arm, and not by going round through other sentences. The
call graph is acyclic, and the compiler refuses anything else:

```
error: Sentence 'loopy::counts_down' (index SentenceIndex(0)) reaches itself,
and recursion is forbidden: a sentence must have a finite expansion, so a loop
has to be written out as the steps it takes
```

The annotation that used to license a cycle, `#[recursive]`, is gone, and says
so rather than coming back as a name that might have been misspelled:

```
error: `#[recursive]` is not an annotation: recursion is forbidden
```

Arity inference is what enforces it, because a cycle is exactly where inference
cannot terminate: working out what a sentence leaves on the stack would mean
working out what that same sentence leaves on the stack.

So a loop is written as the steps it takes. Where a program used to call itself
until a machine stopped reducing, it now runs the reductions it takes and says
so when one was not there to make:

```hana
// One tau reduction, which the caller says must be available.
sentence tau_step {
    jump machine::tau_reduce
    untuple 2
    branch {
        // Stack: [new_state, did_reduce]
        branch { push crate::prelude::ok } { push crate::prelude::err }
        tuple 2
    } {
        // Not a (new_state, did_reduce) pair at all.
        drop 0
        push crate::prelude::err
        tuple 2
    }
}

test sentence drives_two_steps {
    tuple 0
    jump machine::init
    jump tau_step ?
    jump tau_step ?
    // ... and the machine is where the test says it is
}
```

That is a real restriction, and it is bought rather than free. What it buys:

- **Every sentence has an arity**, inferred rather than declared, so `#[arity]`
  is only ever a check on what the body does — never the last word on a body
  inference could not read.
- **Every sentence has a finite expansion.** `bin/rewrite` and `bin/prove` work
  by expanding calls, and termination is a property of the language rather than
  something a precondition has to ask about. See
  [docs/identities.md](identities.md).
- **Every analysis over the call graph terminates on its own.** Arity inference
  and the rewriter's tree-building walk it with no cycle case to carry, and
  failure reachability settles in one pass over each edge.
- **A program's step count is bounded by its text**, which is what makes the
  totality claim in [docs/totality.md](totality.md) about failure alone rather
  than about failure and divergence.

What it costs is unbounded iteration, which has to be expressed some other way —
today, by writing the steps out.

### The `?` operator

A **result** is the 2-tuple `(value, tag)`, where `tag` is `crate::prelude::ok`
or `crate::prelude::err`. `?` takes one apart: on `ok` the block carries on with
the value that was inside, and on `err` the block **ends there**, handing the
error back as its own answer.

```hana
mod prelude {
    symbol ok
    symbol err
}

// Halves an even number; an odd one is an error carrying the number.
#[arity(1, 1)]
sentence halve { /* ... leaves (n/2, ok) or (n, err) ... */ }

// Two halvings, the second reached only if the first succeeded.
#[arity(1, 1)]
sentence quarter {
    jump halve
    ?
    jump halve
}
```

`12` gives `(3, ok)`; `5` gives `(5, err)` without the second `halve` running at
all. Nothing declares `ok` and `err` for you — a program that uses `?` says what
its tags are, the way it says what its `main` is.

**It is sugar, and this is what it expands to.** Everything written after the
`?` moves into a branch arm:

```hana
untuple 2
branch { push crate::prelude::ok equal } { drop 0 push false }
branch { ...the rest of the block... } { push crate::prelude::err tuple 2 }
```

Three things follow from that shape:

- **`?` answers on every input.** The first branch reads the flag `untuple`
  leaves: a value that is not a 2-tuple is not a result, so `?` calls it an
  error carrying that value — which is exactly what `untuple` hands back (see
  [docs/totality.md](totality.md)).
- **The early return drops what the rest of the block would have consumed.** The
  two arms of a branch must agree on their net stack effect, and the arm that
  leaves early has not run the code that would have eaten the values underneath.
  So it drops them — exactly as many as the arity demands, no more. A value the
  rest of the block would have passed through is passed through by the early
  return too.
- **`?` leaves the *block* it is written in, not the sentence.** A branch arm and
  a `dip` body are blocks, so a `?` inside one ends that arm and the error lands
  in the code after the branch. Returning further than that is not something the
  language can express yet.

The drop count is measured, not declared, which is why `?` is the one piece of
sugar that is not expanded in phase 2: what the rest of the block consumes can
depend on a sentence that has not been compiled yet. See
[docs/compilation.md](compilation.md).

### Why `dip` and not `roll`

`pick` and `roll` take depths measured from the top of the stack, so what they
name depends on everything sitting above them. A block written against a
particular stack layout breaks as soon as a caller leaves an extra value
behind, and the checkers must reason about the whole stack to know what a
block touched.

`dip` states the layout instead of working around it. Because the hidden
values are inaccessible to the block, they are *provably* unchanged across it:
the arity checker charges them to the requirement but not to the net change,
and the Z3 encoding threads them through as the same terms rather than
rebuilding them.

The alternative — `tuple N`, shuffle, `untuple N` — is worse than it looks.
`untuple` does not halt on a value that is not a tuple of exactly that size,
but it does *fail*: it reports `false` and hands the value back (see
[docs/totality.md](totality.md)). Saving and restoring `N` values that way adds
`N` failure flags to reason about, purely as an artifact of the encoding. `dip`
makes them impossible to write.

```hana
// Reach past a value you want to keep:
push 1
push 2
push 99
dip { add }     // Stack: [3, 99]

// Hide more than one:
dip 2 { add }

// Nested dips accumulate their hidden regions:
dip { dip { add } }
```

---

## 6. Complete Opcode Reference

For a complete listing of all instructions available in Hanoi Assembly organized by functionality, please see the [Hanoi Assembly Opcode Reference](hana_reference.md).
