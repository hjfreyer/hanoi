# Z3ify: Static Safety Verification Tool for Hanoi

Z3ify is a static analysis and formal safety verification tool for Hanoi. It allows developers to prove that specific functions never trigger a runtime panic under designated precondition checks. 

Rather than exporting SMT-LIB2 code, Z3ify compiles Hanoi sentences directly into Z3 recursive function definitions (`RecFuncDecl`) and solves the safety assertions programmatically using the Z3 solver API.

---

## 1. Syntax: The `#[safety2]` Attribute

Any `sentence` or `function` in a `.hana` file can be verified by annotating it with the `#[safety2]` attribute, specifying a safety check function:

```hana
#[arity(1, 1)]
function safe_for_foo {
    is_int
}

#[arity(1, 1)]
#[safety2(safe_for_foo)]
function foo {
    push 1
    add
}
```

When Z3ify runs:
1. It validates that all recursive cycles in the compiled library are correctly annotated with the `#[recursive]` attribute.
2. It compiles all non-recursive sentences in the library into programmatic Z3 recursive function definitions.
3. It asserts that the safety precondition function (`safe_for_foo`) evaluates to `true`.
4. It checks whether the target function (`foo`) can evaluate to `Panic` under that precondition.

---

## 2. Type Representation in Z3

### Monadic `Result` Type and Panic Propagation
To represent and propagate runtime panics, Z3ify wraps all stack variables and function returns in a monadic `Result` datatype containing either `Ok Val` or `Panic`:

* **Val**: Represents runtime values of types `Int`, `Bool`, `Float`, `Symbol`, and `Tuple` (represented as Z3 ADT constructors).
* **Result**: Represents either a successful computation (`Ok`) wrapping a `Val`, or a execution abort (`Panic`).

### Preconditions & Primitive Operations
All primitive operations (such as additions, conditionals, and tuple accesses) assert correct type bounds on their input values. If an operation encounters a type mismatch (for example, attempting to add an `Int` and a `Bool`), it propagates a `Panic` result.

---

## 3. Symbols
Symbols are mapped to unique integer IDs. Symbol operations such as `symbol_len` and `symbol_char_at` are modeled in Z3 via nested conditional expressions matching on the registered static symbols list.

---

## 4. Usage

Execute the `z3ify` command-line tool, pointing it to a directory containing a `main.hana` file:

```bash
cargo run --bin z3ify <directory>
```

For example:
```bash
cargo run --bin z3ify tests/
```

### Verification Output
If verification succeeds:
```
Checking safety2 annotations for 'tests'...
[PASS] 'barista::customer_impl::accept_type' never panics when 'barista::customer_impl::anything' returns true
[PASS] 'barista::customer_impl::accept' never panics when 'barista::customer_impl::accept_type' returns true
[PASS] 'barista::customer_impl::emit' never panics when 'barista::customer_impl::is_state' returns true
Verification PASSED.
```

If verification fails (e.g. if the precondition is too weak or an operation can panic), Z3ify extracts the model and prints the counterexample:
```
Checking safety2 annotations for 'tests'...
[FAIL] 'foo' can panic when 'safe_for_foo' returns true! (Counterexample: x = (ValInt 0))
Verification FAILED:
'foo' can panic when 'safe_for_foo' returns true (Counterexample: x = (ValInt 0))
```
