# Hanoi (Hana)

Hanoi is a stack-oriented, VM-executed language designed to explore static analysis, algebraic effects, and formal verification in the context of stateful concurrency. Program source is written in **Hanoi Assembly** (with the `.hana` extension). Hanoi models concurrent systems via **Communicating Sequential Processes (CSP)** style state machines.

> [!NOTE]
> This project is a research workspace containing the compiler/assembler, virtual machine runtime, testing tools, and a suite of formal contract verification experiments.

---

## Key Features

- **Stack-Oriented Execution**: A clean, instruction-driven virtual machine that uses a stack for operations, featuring standard manipulations (`drop`, `pick`, `roll`), arithmetic, and tuple structuring.
- **Scoped Stack Frames**: `dip N { ... }` runs a block with the top `N` stack values hidden from it, so the arity checker can treat those values as unchanged across the call rather than tracking them through it.
- **CSP State Machine Modeling**: Fully implements Communicating Sequential Processes (CSP) state machines. State machines are represented as modules with standardized hooks for managing state transitions, internal execution steps, and termination. See the [CSP Machines Documentation](docs/machines.md) for details.
- **Static Safety & Behavior Contracts** *(annotations only — verifier temporarily removed)*: Functions can be annotated with a precondition (`#[precondition(fn_name)]`), a postcondition (`#[postcondition(fn_name)]`), or a totality claim (`#[total]`). `#[total]` is checked by the compiler; the precondition and postcondition annotations are parsed and preserved, but the Z3-backed static verifier that proved them has been removed for now. See [docs/typecheck.md](docs/typecheck.md) for the design.
- **`type` / `enum` Predicate Sugar**: Declare reusable value predicates with `type Name <spec>;` (primitives — `int`, `bool`, `const_string`, `symbol`, `tuple` — literals, tuples, and `|`-unions) or `enum Name { Variant(spec, ...), ... }`, which expand into `Name::check` sentences usable directly as preconditions/postconditions.
- **Result-Answering Tests**: A `test sentence` hands back `((), ok)` or `(payload, err)` rather than halting the VM, built from `check_equals` and carried out by `?`. A failing test prints what it saw — `FAILED (err (5, 6))` — instead of stopping at an `assert`. See [the reference](docs/hana.md#tests).
- **`?` for Results**: A result is the 2-tuple `(value, ok)` or `(value, err)`, and `?` unwraps one or leaves the block early carrying the error. It is sugar for two branches with the rest of the block inside an arm — including the drops that make the early return leave the stack the way finishing would. See [the reference](docs/hana.md#the--operator).
- **Static Arity Verification**: An arity checker runs before execution to ensure that stack push/pop operations match function signatures, avoiding runtime stack underflows.
- **No Recursion**: A sentence may not reach itself, by any route, and the compiler refuses one that does. Arity inference is what enforces it — a cycle is where inference cannot terminate — so every sentence has an inferred arity and a finite expansion, and a loop is written as the steps it takes. See [the reference](docs/hana.md#recursion-is-forbidden).
- **Namespacing & Modularity**: Hierarchical module declarations (`mod name { ... }` or `mod name;`) with file-import support, relative/absolute path routing, and name visibility exports.
- **Stated Identities & Out-of-Line Proofs**: `identity A = B;` states that two programs are interchangeable; the tactic that proves it lives in the `.hant` beside the `.hana`, and `bin/prove` checks that every stated identity has a proof that discharges it. See [docs/identities.md](docs/identities.md).
- **Portable Derivations**: A proof's derivation — which equation, which arguments, which direction, which place, step by step — has a text format, and `bin/replay` checks a file of them against the corpus with no search involved. Finding a derivation and checking one are different jobs, so anything that can write the format can be checked by one small tool, whatever language it is written in. See [docs/derivations.md](docs/derivations.md).

---

## Assembly Syntax & Structure

Hanoi Assembly files (`.hana`) consist of modules, constants, sentences, and functions.

### Symbols and Const Strings
Two kinds of constant can be declared, and they divide the work a name does:
- `symbol name` declares a **unique identity**. Two declarations are two symbols however they are named, nothing can read anything out of one, and it prints as the fully qualified path it was declared under.
- `const_string name "text"` declares **text**. It is exactly its characters — two const strings reading the same are the same value — and `const_string_len` and `const_string_char_at` read them. A literal `"text"` may also be pushed directly.

```hana
symbol idle
const_string greeting "hello"
```

### Sentences and Functions
Hanoi supports two keywords to define execution blocks:
- `sentence`: Represents any sequence of operations.
- `function`: Represents a specialized sentence that takes exactly one input and returns exactly one output (implicitly annotated with an arity of `#[arity(1, 1)]`).

### Annotations
Sentences and functions can be annotated with metadata used by the compiler and static verification tools:
- `#[arity(inputs, outputs)]`: Declares the expected stack transition (implicit `#[arity(1, 1)]` for `function`).
- `#[precondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the input for the annotated function to be considered safe to call.
- `#[postcondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the output, given the precondition (if any) held on the input.
- `#[total]`: Declares that the sentence cannot fail — it neither executes `panic`, `assert` or `assert_eq` nor reaches anything that does. **Checked** by the compiler, and opt-in: an unannotated sentence makes no claim. See [docs/totality.md](docs/totality.md).

### Example: Contract Annotation & Verification
```hana
function is_int_fn {
    is_int
}

#[precondition(is_int_fn)]
#[postcondition(is_int_fn)]
function identity {
    // returns input unchanged
}

#[total]
function noop {
    pick 0
    drop 1
}
```

### Example: `type` / `enum` Predicate Sugar
```hana
type TestInt int;
type IntOrBool int | bool;
type SimpleTuple (int, bool);

enum MyEnum {
    Case1(int, bool),
    Case2(symbol),
    Case3(),
}

#[arity(0, 0)]
sentence test_type_and_enum {
    push 42
    jump TestInt::check
    assert

    push ((42, true), MyEnum::Case1::tag)
    jump MyEnum::check
    assert
}
```
Each `type`/`enum` declaration expands into a module with a `check` sentence (`Name::check`) that consumes a value and pushes a `Bool`, so it can be used directly as a `#[precondition(...)]` or `#[postcondition(...)]`. See [docs/typecheck.md](docs/typecheck.md) for the verification model design (currently unimplemented) and [docs/hana.md](docs/hana.md) for the complete `type`/`enum` grammar.

### Identities
A claim that two programs are interchangeable, stated in the source and proved
out of line:

```hana
// identities.hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

```
// identities.hant
proof testing_a_test = cleanup;
```

`./run_proofs.sh` checks every one. The proof is a tactic rather than part of
the program, because it depends on the rewriter's rule set and changes when that
does, while the claim it establishes does not. See
[docs/identities.md](docs/identities.md).

What the proof leaves behind is a derivation — one equation per step, each with
its arguments and the place it applies — and that has a file format of its own,
so a proof can be found by something other than a tactic and still be checked by
one tool. See [docs/derivations.md](docs/derivations.md).

---

## Conceptual Instruction Set Architecture (ISA)

The Hanoi VM supports a rich instruction set categorized into five main domains:

| Category | Instructions | Description |
| :--- | :--- | :--- |
| **Stack Ops** | `Push(V)`, `Drop`, `Pick(d)`, `Roll(d)` | Standard stack push, pop, copy/peek at depth, and rotate. `Pick` and `Roll` are the only instructions that address below the top of the stack. |
| **Arithmetic & Logic** | `Add`, `Subtract`, `Multiply`, `Divide`, `Modulo`, `Negate`, `Equal`, `Greater`, `Less`, `Not`, `And`, `Or` | Basic mathematical and Boolean logic operations. |
| **Control Flow** | `Dip(n, S)`, `Branch(S1, S2)`, `Panic`, `Assert`, `AssertEqual` | Subroutine execution under a hidden region of the stack (a plain `jump` is `Dip(0, S)`), conditional branching, and explicit panics. |
| **Composite Types** | `Tuple(n)`, `Untuple(n)`, `ConstStringLen`, `ConstStringCharAt`, `TupleLength` | Constructing and destructuring tuples, and reading the length and characters of const strings. |
| **Type Predicates** | `IsInt`, `IsBool`, `IsConstString`, `IsSymbol`, `IsTuple` | Runtime type tests, also used internally to compile `type`/`enum` predicates. |

---

## Project Architecture

The Hanoi codebase is structured as a cargo workspace with several key packages:

- **[bytecode](bytecode)**: The compiler frontend and validation pipeline.
  - [bytecode/src/assembly.rs](bytecode/src/assembly.rs): Parser and assembler that turns `.hana` source code into VM bytecode.
  - [bytecode/src/arity.rs](bytecode/src/arity.rs): Static arity checker for validating stack depths.
- **[rewrite](rewrite)**: The equational rewriter, and the two tools built on it.
  - `bin/rewrite`: a debugging aid — takes one sentence and shows what a tactic does to it.
  - `bin/prove`: a gate — takes a corpus and checks that every stated identity has a proof.
  - `bin/replay`: the same gate with the search taken away — takes derivations in the portable format and checks that they discharge what they name.
- **[vm](vm)**: The virtual machine execution engine.
  - [vm/src/lib.rs](vm/src/lib.rs): Core interpreter, instruction dispatch loop, and stack representation.
  - [vm/src/runtime.rs](vm/src/runtime.rs): Asynchronous CSP coordinator that drives state machine step cycles.
- **[test-runner](test-runner)**: CLI harness that compiles and runs integration test suites.
- **[tests](tests)**: A collection of test cases covering all VM features, string/data parsers, queues, and multi-agent CSP networks.

---

## Getting Started

### Prerequisites

1. **Rust**: Install the latest stable Rust toolchain (2024 edition is used).

### Building the Project

Compile the workspace binaries:
```bash
cargo build
```

### Running the Tests

Use the helper shell scripts at the project root to execute test suites:

- **Run all tests (Rust unit tests + Hanoi integration tests)**:
  ```bash
  ./run_all_tests.sh
  ```
- **Run Hanoi integration tests only**:
  ```bash
  ./run_tests.sh
  ```
- **Check every stated identity against its proof**, and then replay each
  derivation through the portable format with the search taken away:
  ```bash
  ./run_proofs.sh
  ```

---

## Documentation

- [docs/hana.md](docs/hana.md): Detailed guide for Hanoi Assembly syntax, stack behavior, contract annotations, and key gotchas.
- [docs/hana_reference.md](docs/hana_reference.md): Complete reference of all available opcodes, organized by functionality.
- [docs/typecheck.md](docs/typecheck.md): Detailed SMT verification and symbolic execution design for the `typecheck` tool (currently removed from the codebase; kept as a design reference).
- [docs/machines.md](docs/machines.md): Specification of Hanoi's Communicating Sequential Processes (CSP) state machine semantics.
- [docs/compilation.md](docs/compilation.md): The compilation pipeline — the sugar and core ASTs, and what each phase from tokens to bytecode may assume.
- [docs/tactics.md](docs/tactics.md): The tactic language the `rewrite` crate uses to inline and rewrite compiled bytecode — the rule set, the combinators, and the laws they obey.
- [docs/identities.md](docs/identities.md): Stating an identity in a `.hana`, proving it in the `.hant` beside it, and what `bin/prove` checks.
- [docs/derivations.md](docs/derivations.md): The text format a rewrite script is written in, and what `bin/replay` checks — the interface a proof producer in any language writes to.
