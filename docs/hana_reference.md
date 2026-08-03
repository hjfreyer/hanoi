# Hanoi Assembly (Hana) Opcode Reference

This document catalogs every instruction (opcode) available in Hanoi Assembly, organized by functionality.

**Every data operation is total.** An instruction applied to operands it was not
written for does not fail; it returns a deterministic default. Only `panic`,
`assert` and `assert_eq` can halt a run for a reason about values, and the
"junk" column below says what each of the others answers off its domain.
[docs/totality.md](totality.md) is the normative specification, including why
`not junk` is `true`.

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
| `push` | `push <value>` | `[...] -> [..., value]` | Pushes a literal value (e.g., `42`, `true`, `3.14`, `()`, `(1, 2)`) or a symbol onto the top of the stack. |
| `drop` | `drop <depth>` | `[..., v_d, v_{d-1}, ..., v_0] -> [..., v_{d-1}, ..., v_0]` | Discards the stack element at the specified 0-indexed depth from the top (e.g., `drop 0` pops/drops the TOS). |
| `pick` | `pick <depth>` | `[..., v_d, ..., v_0] -> [..., v_d, ..., v_0, v_d]` | Copies the element at `<depth>` from the top and pushes the copy to the top. `pick 0` is equivalent to `dup`. |
| `roll` | `roll <depth>` | `[..., v_d, v_{d-1}, ..., v_0] -> [..., v_{d-1}, ..., v_0, v_d]` | Rotates the element at `<depth>` to the top, shifting intermediate elements down. `roll 1` is equivalent to `swap`. |

---

## 2. Arithmetic & Logic

These instructions perform mathematical or Boolean logic operations on stack values.

| Mnemonic | Alternate Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `add` | — | `[..., a, b] -> [..., a + b]` | Pops the top two numbers, adds them, and pushes the result. |
| `subtract` | `sub` | `[..., a, b] -> [..., a - b]` | Pops the top two numbers, subtracts $b$ (TOS) from $a$ (second-to-top), and pushes the result. |
| `multiply` | `mul` | `[..., a, b] -> [..., a * b]` | Pops the top two numbers, multiplies them, and pushes the result. |
| `divide` | `div` | `[..., a, b] -> [..., a / b]` | Pops the top two numbers, divides $a$ by $b$ (TOS), and pushes the result. Integer division by zero is `0`; the float world stays IEEE, so `1.0 / 0` is `inf`. |
| `modulo` | `mod` | `[..., a, b] -> [..., a % b]` | Pops the top two numbers, computes the remainder of $a / b$, and pushes the result. Integer modulo by zero is `0`; `1.0 % 0` is `NaN`. |
| `negate` | `neg` | `[..., a] -> [..., -a]` | Pops the top number, negates it numerically, and pushes the result. |
| `not` | — | `[..., v] -> [..., !truthy(v)]` | Pops the top value and pushes `true` unless it was exactly `true`. |
| `and` | — | `[..., a, b] -> [..., a && b]` | Pops the top two values, performs logical AND on their truthiness, and pushes the Boolean result. |
| `or` | — | `[..., a, b] -> [..., a \|\| b]` | Pops the top two values, performs logical OR on their truthiness, and pushes the Boolean result. |

Off their domain: `add`, `subtract`, `multiply`, `divide`, `modulo` and
`negate` answer `0` when an operand is not a number. Integer arithmetic wraps,
so `i64::MIN` is not a special case anywhere. Truthiness is applied per operand,
which is what keeps De Morgan true on every value.

---

## 3. Comparison Operations

These opcodes compare the top two stack values and push a Boolean result.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `equal` | `equal` | `[..., a, b] -> [..., a == b]` | Pops $a$ and $b$, checks if they are equal, and pushes `true` or `false`. |
| `greater` | `greater` | `[..., a, b] -> [..., a > b]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is greater than $b$ (TOS), and pushes the result. |
| `less` | `less` | `[..., a, b] -> [..., a < b]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is less than $b$ (TOS), and pushes the result. |

`equal` compares any two values. `greater` and `less` answer `false` unless both
operands are numbers — and also on a NaN, which is unordered rather than
non-numeric.

---

## 4. Control Flow & Debugging

These instructions control execution flow, jumps, and validation assertions.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `jump` | `jump <target>` | `[...] -> [...]` | Pushes the return address onto the call stack and transfers execution to the subroutine `<target>`. |
| `dip` | `dip <count>? <target>` | `[..., v_{k-1}, ..., v_0] -> [..., v_{k-1}, ..., v_0]` | Hides the top `<count>` values (default 1), runs `<target>` on what remains, then restores the hidden values on top of its results. `dip 0 <target>` is exactly `jump <target>`. |
| `branch` | `branch { then } { else }` | `[..., cond] -> [...]` | Pops $cond$. Executes the `then` block if $cond$ is exactly `true`, and the `else` block on **every** other value. |
| `panic` | `panic` | `[...] -> [halt]` | Halts VM execution immediately with a failure status. |
| `assert` | `assert` | `[..., cond] -> [...]` | Pops $cond$. Halts and panics unless $cond$ is exactly `true` — a non-Boolean is a failed assertion rather than a separate error. |
| `assert_equal` | `assert_eq` | `[..., a, b] -> [...]` | Pops $a$ and $b$. Halts and panics if $a \neq b$. |
| `print` | `print` | `[..., v] -> [..., v]` | Peeks at the top value and prints it to stdout (useful for debugging/logging). |

---

## 5. Composite Types (Tuples & Symbols)

These operations construct, destructure, or query structured data types.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `tuple` | `tuple <size>` | `[..., v_{N-1}, ..., v_0] -> [..., (v_0, ..., v_{N-1})]` | Pops $N$ elements and packages them into a tuple. **Gotcha**: The TOS element $v_0$ becomes index 0 of the tuple. |
| `untuple` | `untuple <size>` | `[..., (v_0, ..., v_{N-1})] -> [..., v_{N-1}, ..., v_0]` | Pops a tuple of size $N$ and pushes its elements back onto the stack in reverse index order, leaving index 0 ($v_0$) at the top. Anything that is not an $N$-tuple comes apart into $N$ copies of `()`. |
| `symbol_len` | `symbol_len` | `[..., sym] -> [..., len]` | Pops a symbol and pushes its character length as an Int. `0` for a non-symbol. |
| `symbol_char_at`| `symbol_char_at` | `[..., sym, idx] -> [..., char]` | Pops index $idx$ and symbol $sym$, then pushes the Unicode code point of the character at that index as an Int. `0` if the index is out of range or either operand is the wrong type. |
| `tuple_length` | `tuple_length` | `[..., tup] -> [..., len]` | Pops a Tuple and pushes its element count as an Int. `0` for a non-tuple, so `tuple_length; push n; equal` decides "is an $n$-tuple" for every $n \geq 1$. |

---

## 6. Type Predicates

These instructions test the runtime type of the top stack value, pushing a Bool. They are also used internally by the compiler to implement `type`/`enum` declarations (see [docs/hana.md](hana.md#4-contract-annotations)).

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `is_int` | `is_int` | `[..., v] -> [..., is_int]` | Pops a value and pushes `true` if it is an Int, else `false`. |
| `is_bool` | `is_bool` | `[..., v] -> [..., is_bool]` | Pops a value and pushes `true` if it is a Bool, else `false`. |
| `is_float` | `is_float` | `[..., v] -> [..., is_float]` | Pops a value and pushes `true` if it is a Float, else `false`. |
| `is_symbol` | `is_symbol` | `[..., v] -> [..., is_symbol]` | Pops a value and pushes `true` if it is a Symbol, else `false`. |
| `is_tuple` | `is_tuple` | `[..., v] -> [..., is_tuple]` | Pops a value and pushes `true` if it is a Tuple, else `false`. |
