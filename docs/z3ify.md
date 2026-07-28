# Z3ify: SMT-LIB2 REPL Export Tool for Hanoi

Z3ify is a static analysis and exploration tool for Hanoi. It allows developers to mark specific Hanoi sentences with the `#[z3ify]` attribute, compiling them and all recursively referenced sentences into clean, non-recursive Z3 SMT-LIB2 function definitions. The resulting output can be loaded directly into a Z3 REPL for manual verification and interactive theorem proving.

---

## 1. Syntax: The `#[z3ify]` Attribute

Any `sentence` or `function` in a `.hana` file can be annotated with `#[z3ify]`:

```hana
#[arity(2, 2)]
#[z3ify]
sentence swap {
    pick 1
    drop 2
}
```

When Z3ify runs, it translates the annotated sentence and any sentences called by it (transitively) into corresponding Z3 functions.

---

## 2. Type Representation in SMT-LIB2

### Monadic `Result` Type and Panic Propagation
To ensure runtime panics are correctly represented and propagated, Z3ify wraps all stack slots, return values, and helper signatures in a monadic `Result` datatype containing either `Ok Val` or `Panic`:

```smt2
(declare-datatypes () (
  (Val
    (ValInt (getInt Int))
    (ValBool (getBool Bool))
    (ValFloat (getFloat Int))           ; Floats are represented opaquely by integer IDs
    (ValSymbol (getSymbol Int))         ; Symbols are represented by unique integer IDs
    (ValTuple0)
    (ValTuple2 (getTuple2_0 Val) (getTuple2_1 Val))
    (ValTuple3 (getTuple3_0 Val) (getTuple3_1 Val) (getTuple3_2 Val))
  )
  (Result
    (Ok (getVal Val))
    (Panic)
  )
))
```

### Type Checking & Primitive Operations
All primitive operations (e.g. `val_add`, `val_sub`, `val_cond`) and selectors verify the runtime types of their arguments, returning `Panic` on mismatch:
*   **Arithmetic**: Requires both arguments to be `is-ValInt`.
*   **Branch Conditionals**: Requires the condition to satisfy `is-ValBool`.
*   **Tuple Selectors**: Require the argument to be `is-ValTuple<n>` (e.g. checking `is-ValTuple2` before calling `getTuple2_0`).

For example, the 2-tuple selectors are defined as:
```smt2
(define-fun val_getTuple2_0 ((t Result)) Result 
  (ite (and (is-Ok t) (is-ValTuple2 (getVal t))) 
       (Ok (getTuple2_0 (getVal t))) 
       Panic))
```

---

## 3. Symbols

Symbols are represented as unique integer IDs. To facilitate symbol string operations, Z3ify compiles all symbols into a single explicit `symbol_to_string` function mapping IDs to strings via nested `ite` (if-then-else) expressions:

```smt2
(define-fun symbol_to_string ((sym_id Int)) String
  (ite (= sym_id 0) "std::io"
  (ite (= sym_id 1) "std::io::stdout"
  ...
  "")))
```

All non-ASCII characters, control characters, and backslashes in symbol strings are safely converted to SMT-LIB2 hex escapes (e.g. `"caf\u{e9}"` for `"café"`) to guarantee solver satisfiability.

---

## 4. Function Translation

For a sentence `F` of arity $N \rightarrow M$:
*   Z3ify defines $M$ separate Z3 functions (one per output value), taking and returning values of type `Result`:
    ```smt2
    (define-fun |F_out_0| ((in_0 Result) ... (in_N-1 Result)) Result ...)
    (define-fun |F_out_1| ((in_0 Result) ... (in_N-1 Result)) Result ...)
    ```
*   If `F` calls another sentence `G` (which is recursively translated), the inputs to `G` are passed from the active stack, and the return values of `G` are mapped to `|G_out_0|(...)`, `|G_out_1|(...)`, etc.

---

## 5. Usage

Execute the `z3ify` command-line tool, pointing it to a `.hana` file or directory:

```bash
cargo run --bin z3ify <file_or_directory>
```

This compiles the code and prints the generated SMT-LIB2 script directly to standard output, which you can redirect to a file or pipe directly to Z3:

```bash
# Redirect to a file
cargo run --bin z3ify tests/ > output.smt2

# Pipe directly into Z3
cargo run --bin z3ify tests/ | z3 -in
```
