# Hanoi Assembly (Hana) Opcode Reference

This document catalogs every instruction (opcode) available in Hanoi Assembly, organized by functionality.

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
| `divide` | `div` | `[..., a, b] -> [..., a / b]` | Pops the top two numbers, divides $a$ by $b$ (TOS), and pushes the result. Panics if $b == 0$. |
| `modulo` | `mod` | `[..., a, b] -> [..., a % b]` | Pops the top two numbers, computes the remainder of $a / b$, and pushes the result. Panics if $b == 0$. |
| `negate` | `neg` | `[..., a] -> [..., -a]` | Pops the top number, negates it numerically, and pushes the result. |
| `not` | — | `[..., b] -> [..., !b]` | Pops the top Boolean, negates its value, and pushes the result. |
| `and` | — | `[..., a, b] -> [..., a && b]` | Pops the top two values, performs logical AND on their truthiness, and pushes the Boolean result. |
| `or` | — | `[..., a, b] -> [..., a \|\| b]` | Pops the top two values, performs logical OR on their truthiness, and pushes the Boolean result. |

---

## 3. Comparison Operations

These opcodes compare the top two stack values and push a Boolean result.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `equal` | `equal` | `[..., a, b] -> [..., a == b]` | Pops $a$ and $b$, checks if they are equal, and pushes `true` or `false`. |
| `greater` | `greater` | `[..., a, b] -> [..., a > b]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is greater than $b$ (TOS), and pushes the result. |
| `less` | `less` | `[..., a, b] -> [..., a < b]` | Pops $a$ and $b$, checks if $a$ (second-to-top) is less than $b$ (TOS), and pushes the result. |

---

## 4. Control Flow & Debugging

These instructions control execution flow, jumps, and validation assertions.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `jump` | `jump <target>` | `[...] -> [...]` | Pushes the return address onto the call stack and transfers execution to the subroutine `<target>`. |
| `branch` | `branch { then } { else }` | `[..., cond] -> [...]` | Pops $cond$. If $cond$ is truthy, executes the `then` block; otherwise, executes the `else` block. |
| `panic` | `panic` | `[...] -> [halt]` | Halts VM execution immediately with a failure status. |
| `assert` | `assert` | `[..., cond] -> [...]` | Pops $cond$. Halts and panics if $cond$ is falsey. |
| `assert_equal` | `assert_eq` | `[..., a, b] -> [...]` | Pops $a$ and $b$. Halts and panics if $a \neq b$. |
| `print` | `print` | `[..., v] -> [..., v]` | Peeks at the top value and prints it to stdout (useful for debugging/logging). |

---

## 5. Composite Types (Tuples & Symbols)

These operations construct, destructure, or query structured data types.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `tuple` | `tuple <size>` | `[..., v_{N-1}, ..., v_0] -> [..., (v_0, ..., v_{N-1})]` | Pops $N$ elements and packages them into a tuple. **Gotcha**: The TOS element $v_0$ becomes index 0 of the tuple. |
| `untuple` | `untuple <size>` | `[..., (v_0, ..., v_{N-1})] -> [..., v_{N-1}, ..., v_0]` | Pops a tuple of size $N$ and pushes its elements back onto the stack in reverse index order, leaving index 0 ($v_0$) at the top. |
| `symbol_len` | `symbol_len` | `[..., sym] -> [..., len]` | Pops a symbol and pushes its character length as an Int. |
| `symbol_char_at`| `symbol_char_at` | `[..., sym, idx] -> [..., char]` | Pops index $idx$ and symbol $sym$, then pushes the Unicode code point of the character at that index as an Int. |

---

## 6. Mathematical Sets

These instructions manipulate mathematical sets of values (`ValueSet`).

> [!WARNING]
> Set operations are deprecated/restricted in compile-time safety checker specifications, but are fully implemented and supported by the runtime VM.

| Mnemonic | Syntax | Stack Transition | Description |
| :--- | :--- | :--- | :--- |
| `set_contains` | `set_contains` | `[..., val, set] -> [..., is_member]` | Pops member value $val$ and set $set$, and pushes a Bool indicating membership. |
| `set_union` | `set_union` | `[..., set_a, set_b] -> [..., union_set]` | Pops two sets and pushes their union set. |
| `set_intersection`| `set_intersection`| `[..., set_a, set_b] -> [..., intersection_set]`| Pops two sets and pushes their intersection set. |
| `set_difference` | `set_difference` | `[..., set_a, set_b] -> [..., diff_set]` | Pops two sets and pushes their difference ($set\_a \setminus set\_b$). |
| `set_complement` | `set_complement` | `[..., set] -> [..., complement_set]` | Pops a set and pushes its complement set. |
| `set_singleton` | `set_singleton` | `[..., val] -> [..., singleton_set]` | Pops a value and pushes a singleton set containing that value. |
| `set_tuple` | `set_tuple <size>` | `[..., s_{N-1}, ..., s_0] -> [..., set_tuple]` | Pops $N$ sets and pushes a set tuple representing their Cartesian product. |
| `set_choose` | `set_choose` | `[..., set] -> [..., (has_element, element)]` | Pops a set, chooses an arbitrary member, and pushes a tuple `(has_element: bool, element)`. |
| `set_rename_prefix`| `set_rename_prefix`| `[..., set, from, to]` -> `[..., renamed_set]` | Pops a set and two symbols (`from`, `to`), and rewrites all events in `set` starting with `from` to start with `to`. |
