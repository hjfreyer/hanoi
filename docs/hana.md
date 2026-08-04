# Hanoi Assembly (Hana) Reference Guide

This document provides a detailed reference for Hanoi Assembly (`.hana` files), covering the execution model, syntax conventions, instruction set details, and key gotchas when writing stack-based assembly code.

---

## 1. Execution Model & Stack Mechanics

Hanoi is a stack-oriented VM-executed language. Almost all instructions interact directly with a central value stack by pushing or popping elements.

### Value Types
The stack can contain elements of the following types:
- **Bool**: `true` or `false`.
- **Int**: Signed 64-bit integers (e.g., `42`, `-1`).
- **Float**: 64-bit floating-point numbers (e.g., `3.14`).
- **Symbol**: Unique identifiers associated with string descriptions (e.g., `symbol my_event "Event description"`).
- **Tuple**: Nested structures grouping zero or more values (e.g., `(foo, (bar, 42))`).

---

## 2. Crucial Gotcha: Tuple and Untuple Ordering

Because Hanoi is stack-based, constructing and destructuring tuples has a reversing effect on elements relative to their push order.

### The Tuple Reversing Behavior
When you call `tuple N` (where $N > 0$), the VM pops $N$ elements from the stack one by one. The **top of the stack** (which was pushed last) is popped first and becomes **index 0** of the tuple. The element below it becomes index 1, and so on.

#### Example:
```hana
push bar
push foo
tuple 2
```
1. `push bar` puts `bar` on the stack.
2. `push foo` puts `foo` on the stack (at the top).
3. `tuple 2` pops two elements:
   - First pop: `foo` (becomes index 0 of the tuple).
   - Second pop: `bar` (becomes index 1 of the tuple).

The resulting tuple on the stack is:
`(foo, bar)`

### Symmetrical Destructuring with Untuple
To maintain symmetry, `untuple N` pops a tuple and pushes its elements back onto the stack in **reverse index order** (from index $N-1$ down to 0). This places **index 0 at the top of the stack**.

#### Example:
```hana
// Stack: [(foo, bar)]
untuple 2
// Stack now: [bar, foo] (where foo is at the top of the stack)
```

This symmetry allows a sequence of `tuple N` followed by `untuple N` to restore the stack to its exact original state prior to tuple creation.

> [!WARNING]
> Always remember that the last item pushed before a `tuple N` instruction becomes the first item (index 0) in the resulting tuple, and it will be at the top of the stack after calling `untuple N`.

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

---

## 4. Contract Annotations

Hanoi supports static assertion checking at compile time via attributes. `#[arity]`, `#[total]` and `#[recursive]` are checked by the compiler today; `#[precondition]` and `#[postcondition]` were verified by the `typecheck` tool, currently removed from the codebase along with its Z3 dependency (see [docs/typecheck.md](typecheck.md) for the design):

- `#[arity(inputs, outputs)]`: Declares the stack arity (required for sentences that do not use the default `function` arity of `1 -> 1`).
- `#[precondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the input for the annotated function to be considered safe to call.
- `#[postcondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the output, given the precondition (if any) held on the input.
- `#[total]`: Declares that the sentence cannot fail — it neither executes `panic`, `assert` or `assert_eq` nor reaches anything that does. **Checked** by the compiler, and opt-in: an unannotated sentence makes no claim, so generated code and branch arms need no annotation. See [docs/totality.md](totality.md).
- `#[recursive]`: Marks a sentence participating in a recursive call cycle so the verifier can model it.
- `#[flags]`: Makes the sentence read the success flags that fallible instructions leave. Without it the compiler drops each flag as it emits the instruction, which is why existing source is unaffected by them. See [docs/totality.md](totality.md).

Precondition/postcondition functions are ordinary `1 -> 1` functions, but they are commonly generated with the `type`/`enum` sugar rather than written by hand:

- `type Name <spec>;` declares a value predicate from a spec of primitive type names (`int`, `bool`, `float`, `symbol`, `tuple`), literal values, tuples (`(spec, spec, ...)`), `|`-separated unions, or paths to other `type`/`enum` checks or `symbol`s. It expands to `mod Name { sentence check { ... } }`, exported and automatically annotated `#[total]`.
- `enum Name { Variant(spec, ...), ... }` declares a tagged union: each `Variant` gets its own submodule with a fresh `tag` symbol and a `Body::check` for its payload tuple, and `Name::check` accepts any `(tag, payload)` pair matching one of the variants.

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
- **Branches**: Conditional execution is implemented via `branch { then_block } { else_block }`. The VM pops the top stack element; if it is truthy, it executes `then_block`, otherwise it executes `else_block`.
- **Panics**: If a condition fails, `panic` immediately halts VM execution. Safe assertion operations `assert` and `assert_eq` verify preconditions and abort the program on failure.

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
`untuple` no longer panics on a value that is not a tuple of exactly that size,
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
