# Hanoi Assembly (Hana) Opcode Reference

This document catalogs every instruction (opcode) available in Hanoi Assembly, organized by functionality.

**Every data operation is total.** An instruction applied to operands it was not
written for does not fail; it returns a deterministic default. Only `panic`,
`assert` and `assert_eq` can halt a run for a reason about values. A sentence
may claim it reaches none of them with `#[total]`, which the compiler checks.

Twelve instructions are additionally **fallible**: they leave a `bool` — written
`ok` in the transitions below — on top of their result saying whether the answer
was computed or invented, and where the output arity has room they hand their
input back rather than replacing it. Every sentence sees those flags; there is
no mode in which they are dropped for you. Fallible instructions are marked ⚑.

[docs/totality.md](totality.md) is the normative specification, including the
full table and why `not junk` is `true`.

### Stack Convention Notation
In the transition diagrams below:
- The stack is represented inside brackets `[...]`.
- The rightmost element is the **top of the stack** (TOS).
- The transition format is `[Before] -> [After]`.
- Ellipses `...` represent the rest of the stack, which remains unchanged.

---

## 1. Stack Operations

These opcodes manipulate the stack directly without modifying values.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `push` | `push <value>` | `[...] -> [..., value]` | Pushes a literal value (e.g., `42`, `true`, `3.14`, `"text"`, `()`, `(1, 2)`) or a path naming a declared `symbol` or `const_string` onto the top of the stack. |
| `drop` | `drop <depth>` | `[..., v_d, v_{d-1}, ..., v_0] -> [..., v_{d-1}, ..., v_0]` | Discards the stack element at the specified 0-indexed depth from the top (e.g., `drop 0` pops/drops the TOS). |
| `pick` | `pick <depth>` | `[..., v_d, ..., v_0] -> [..., v_d, ..., v_0, v_d]` | Copies the element at `<depth>` from the top and pushes the copy to the top. `pick 0` is equivalent to `dup`. |
| `roll` | `roll <depth>` | `[..., v_d, v_{d-1}, ..., v_0] -> [..., v_{d-1}, ..., v_0, v_d]` | Rotates the element at `<depth>` to the top, shifting intermediate elements down. `roll 1` is equivalent to `swap`. |

---

## 2. Arithmetic & Logic

These instructions perform mathematical or Boolean logic operations on stack values.

| Mnemonic | Alternate Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `add` ⚑ | — | `[..., a, b] -> [..., a + b, ok]` | Pops the top two numbers, adds them, and pushes the result. |
| `subtract` ⚑ | `sub` | `[..., a, b] -> [..., a - b, ok]` | Pops the top two numbers, subtracts $b$ (TOS) from $a$ (second-to-top), and pushes the result. |
| `multiply` ⚑ | `mul` | `[..., a, b] -> [..., a * b, ok]` | Pops the top two numbers, multiplies them, and pushes the result. |
| `divide` ⚑ | `div` | `[..., a, b] -> [..., a / b, ok]` | Pops the top two numbers, divides $a$ by $b$ (TOS), and pushes the result. Division by zero **fails**, answering `0`. |
| `modulo` ⚑ | `mod` | `[..., a, b] -> [..., a % b, ok]` | Pops the top two numbers, computes the remainder of $a / b$, and pushes the result. Integer modulo by zero **fails**; `1.0 % 0` succeeds with `NaN`. |
| `negate` ⚑ | `neg` | `[..., a] -> [..., -a, ok]` | Pops the top number, negates it numerically, and pushes the result. |
| `not` | — | `[..., v] -> [..., !truthy(v)]` | Pops the top value and pushes `false` unless it was exactly `false`. |
| `and` | — | `[..., a, b] -> [..., a && b]` | Pops the top two values, performs logical AND on their truthiness, and pushes the Boolean result. |
| `or` | — | `[..., a, b] -> [..., a \|\| b]` | Pops the top two values, performs logical OR on their truthiness, and pushes the Boolean result. |

Off their domain the fallible six report `false`, answering `0` where there is no room to
keep the operands and handing the value back where there is (`negate`). Integer
arithmetic wraps, so `i64::MIN` is not a special case anywhere. `not`, `and` and
`or` carry no flag — there is no input they cannot answer on — and truthiness is
applied per operand, which is what keeps De Morgan true on every value.
`truthy(v)` is `v != false`: `false` is the only falsy value, so a number, a
symbol, a const string or a tuple is true. See `docs/totality.md`.

---

## 3. Comparison Operations

These opcodes compare the top two stack values and push a Boolean result.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `equal` | `equal` | `[..., a, b] -> [..., a == b]` | Pops $a$ and $b$, checks if they are equal, and pushes `true` or `false`. |
| `greater` ⚑ | `greater` | `[..., a, b] -> [..., a > b, ok]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is greater than $b$ (TOS), and pushes the result. |
| `less` ⚑ | `less` | `[..., a, b] -> [..., a < b, ok]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is less than $b$ (TOS), and pushes the result. |

`equal` compares any two values and carries no flag. ⚑ `greater` and `less` are
fallible: they answer `false, false` unless both operands are numbers, and a NaN
fails too, being unordered rather than non-numeric.

---

## 4. Control Flow & Validation

These instructions control execution flow, jumps, and validation assertions.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `jump` | `jump <target>` | `[...] -> [...]` | Pushes the return address onto the call stack and transfers execution to the subroutine `<target>`. |
| `dip` | `dip <count>? <target>` | `[..., v_{k-1}, ..., v_0] -> [..., v_{k-1}, ..., v_0]` | Hides the top `<count>` values (default 1), runs `<target>` on what remains, then restores the hidden values on top of its results. `dip 0 <target>` is exactly `jump <target>`. |
| `branch` | `branch { then } { else }` | `[..., cond] -> [...]` | Pops $cond$. Executes the `then` block if $cond$ is exactly `true`, and the `else` block on **every** other value. |
| `panic` | `panic` | `[...] -> [halt]` | Halts VM execution immediately with a failure status. This and the two below are the only instructions that can, and a sentence reaching any of them cannot claim `#[total]`. |
| `assert` | `assert` | `[..., cond] -> [...]` | Pops $cond$. Halts and panics only if $cond$ is exactly `false`; anything else is truthy and passes. See `docs/totality.md`. |
| `assert_equal` | `assert_eq` | `[..., a, b] -> [...]` | Pops $a$ and $b$. Halts and panics if $a \neq b$. |

---

## 5. Composite Types (Tuples & Const Strings)

These operations construct, destructure, or query structured data types.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `tuple` | `tuple <size>` | `[..., v_0, ..., v_{N-1}] -> [..., (v_0, ..., v_{N-1})]` | Pops $N$ elements and packages them into a tuple, keeping their stack order: the deepest becomes index 0 and the TOS element $v_{N-1}$ becomes the last. |
| `untuple` ⚑ | `untuple <size>` | `[..., (v_0, ..., v_{N-1})] -> [..., v_0, ..., v_{N-1}, ok]` | Pops a tuple of size $N$ and pushes its elements back onto the stack in index order, leaving the last element ($v_{N-1}$) at the top — the slot it came from. Anything else **fails**, leaving the value itself in the deepest of the $N$ slots with `()` padding above it — so a caller that reads the flag has lost nothing. |
| `const_string_len` ⚑ | `const_string_len` | `[..., str] -> [..., len, ok]` | Pops a const string and pushes its character length as an Int. Fails on anything else, handing the value back. |
| `const_string_char_at` ⚑ | `const_string_char_at` | `[..., str, idx] -> [..., char, ok]` | Pops index $idx$ and const string $str$, then pushes the Unicode code point of the character at that index as an Int. Fails, answering `0`, if the index is out of range or either operand is the wrong type. |
| `tuple_length` ⚑ | `tuple_length` | `[..., tup] -> [..., len, ok]` | Pops a Tuple and pushes its element count as an Int. Fails on a non-tuple, handing the value back. |

---

## 6. Type Predicates

These instructions test the runtime type of the top stack value, pushing a Bool. They are also used internally by the compiler to implement `type`/`enum` declarations (see [docs/hana.md](hana.md#4-contract-annotations)).

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `is_int` | `is_int` | `[..., v] -> [..., is_int]` | Pops a value and pushes `true` if it is an Int, else `false`. |
| `is_bool` | `is_bool` | `[..., v] -> [..., is_bool]` | Pops a value and pushes `true` if it is a Bool, else `false`. |
| `is_const_string` | `is_const_string` | `[..., v] -> [..., is_const_string]` | Pops a value and pushes `true` if it is a ConstString, else `false`. |
| `is_symbol` | `is_symbol` | `[..., v] -> [..., is_symbol]` | Pops a value and pushes `true` if it is a Symbol, else `false`. |
| `is_tuple` | `is_tuple` | `[..., v] -> [..., is_tuple]` | Pops a value and pushes `true` if it is a Tuple, else `false`. |
