# Typecheck: Static Safety Verification Tool for Hanoi

> [!NOTE]
> The `typecheck` tool and its Z3 dependency have been removed from the codebase for now (it was restricting other development). The `#[precondition]`, `#[postcondition]`, `#[total]`, and `#[recursive]` annotations described below are still parsed and preserved in the `Library`, but nothing currently verifies them. This document is kept as a design reference for a future reimplementation.
>
> **The panic model below is stale.** It was written against a VM in which any operator could reject an operand — division by zero, `untuple` on a non-tuple, `and` on two ints. Every data operation is now total (see [docs/totality.md](totality.md)), so `Panic` is reachable only through `panic`, `assert` and `assert_eq`, and the interesting judgment has changed from "does this program panic" to "does this program compute on junk". A reimplementation should be generated from the junk table in `totality.md` rather than from the encoding described here.

Typecheck is a static analysis and formal safety verification tool for Hanoi. It allows developers to prove that specific functions never trigger a runtime panic under designated precondition checks. 

Rather than exporting SMT-LIB2 code, Typecheck compiles Hanoi sentences directly into Z3 recursive function definitions (`RecFuncDecl`) and solves the safety assertions programmatically using the Z3 solver API.

---

## 1. Syntax: The `#[precondition]` and `#[postcondition]` Attributes

### Preconditions
Any `sentence` or `function` in a `.hana` file can be verified by annotating it with the `#[precondition]` attribute, specifying a safety check function:

```hana
function safe_for_foo {
    is_int
}

#[precondition(safe_for_foo)]
function foo {
    push 1
    add
}
```

When Typecheck runs:
1. It validates that all recursive cycles in the compiled library are correctly annotated with the `#[recursive]` attribute.
2. It compiles all non-recursive sentences in the library into programmatic Z3 recursive function definitions.
3. It asserts that the safety precondition function (`safe_for_foo`) evaluates to `true`.
4. It checks whether the target function (`foo`) can evaluate to `Panic` under that precondition.

### Postconditions
You can also annotate a function with `#[postcondition(Q)]`. A postcondition asserts that the function's output value satisfies the check function `Q`, assuming the function's input satisfies its precondition (if any).

All three involved functions (the target function, the precondition, and the postcondition) must have arity `1 -> 1`.

```hana
function is_int_fn {
    is_int
}

#[precondition(is_int_fn)]
#[postcondition(is_int_fn)]
function identity {
    // returns input
}
```

To prove the postcondition holds, Typecheck uses Z3 to prove that:
$$\forall x. P(x) = \text{true} \implies Q(F(x)) = \text{true}$$

It does this by searching for a counterexample $x$ where:
1. $P(x) = \text{true}$
2. $Q(F(x)) \neq \text{true}$ (or $F(x)$ panics, or $Q$ panics)

If no such counterexample is found, the postcondition is proven.

### Total Functions
You can also annotate a function with `#[total]`. A total function assertion ensures that the function never triggers a runtime panic on *any* possible input.

```hana
#[total]
function identity {
    // returns input (never panics)
}
```

To prove totality, Typecheck attempts to find any input $x$ that causes $F(x) = \text{Panic}$. If no such input exists (the assertion is Unsat), the function is proven to be total.

---

## 2. Type Representation in Z3

### Monadic `Result` Type and Panic Propagation
To represent and propagate runtime panics, Typecheck wraps all stack variables and function returns in a monadic `Result` datatype containing either `Ok Val` or `Panic`:

* **Val**: Represents runtime values of types `Int`, `Bool`, `Float`, `ConstString`, `Symbol`, and `Tuple` (represented as Z3 ADT constructors).
* **Result**: Represents either a successful computation (`Ok`) wrapping a `Val`, or a execution abort (`Panic`).

### Preconditions & Primitive Operations
All primitive operations (such as additions, conditionals, and tuple accesses) assert correct type bounds on their input values. If an operation encounters a type mismatch (for example, attempting to add an `Int` and a `Bool`), it propagates a `Panic` result.

---

## 3. Symbols and const strings
Symbols are mapped to unique integer IDs and have no other content, so the only question to ask about one is whether it equals another. The string operations `const_string_len` and `const_string_char_at` read a `ConstString`, and are modeled in Z3 via nested conditional expressions matching on the registered static strings list.

---

## 4. Usage

Execute the `typecheck` command-line tool, pointing it to a directory containing a `main.hana` file:

```bash
cargo run --bin typecheck <directory>
```

For example:
```bash
cargo run --bin typecheck tests/
```

### Verification Output
If verification succeeds:
```
Checking precondition annotations for 'tests'...
[PASS] 'barista::customer_impl::accept_type' never panics when 'barista::customer_impl::anything' returns true
[PASS] 'barista::customer_impl::accept' never panics when 'barista::customer_impl::accept_type' returns true
[PASS] 'barista::customer_impl::emit' never panics when 'barista::customer_impl::is_state' returns true
Verification PASSED.
```

If verification fails (e.g. if the precondition is too weak or an operation can panic), Typecheck extracts the model and prints the counterexample:
```
Checking precondition annotations for 'tests'...
[FAIL] 'foo' can panic when 'safe_for_foo' returns true! (Counterexample: x = (ValInt 0))
Verification FAILED:
'foo' can panic when 'safe_for_foo' returns true (Counterexample: x = (ValInt 0))
```
