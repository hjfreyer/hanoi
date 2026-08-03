# Hanoi (Hana)

Hanoi is a stack-oriented, VM-executed language designed to explore static analysis, algebraic effects, and formal verification in the context of stateful concurrency. Program source is written in **Hanoi Assembly** (with the `.hana` extension). Hanoi models concurrent systems via **Communicating Sequential Processes (CSP)** style state machines.

> [!NOTE]
> This project is a research workspace containing the compiler/assembler, virtual machine runtime, testing tools, and a suite of formal contract verification experiments.

---

## Key Features

- **Stack-Oriented Execution**: A clean, instruction-driven virtual machine that uses a stack for operations, featuring standard manipulations (`drop`, `pick`, `roll`), arithmetic, and tuple structuring.
- **Scoped Stack Frames**: `dip N { ... }` runs a block with the top `N` stack values hidden from it, so the arity checker can treat those values as unchanged across the call rather than tracking them through it.
- **CSP State Machine Modeling**: Fully implements Communicating Sequential Processes (CSP) state machines. State machines are represented as modules with standardized hooks for managing state transitions, internal execution steps, and termination. See the [CSP Machines Documentation](docs/machines.md) for details.
- **Static Safety & Behavior Contracts** *(annotations only — verifier temporarily removed)*: Functions can be annotated with a precondition (`#[precondition(fn_name)]`), a postcondition (`#[postcondition(fn_name)]`), or a totality claim (`#[total]`). These annotations are parsed and preserved, but the Z3-backed static verifier that proved them has been removed for now. See [docs/typecheck.md](docs/typecheck.md) for the design.
- **`type` / `enum` Predicate Sugar**: Declare reusable value predicates with `type Name <spec>;` (primitives, literals, tuples, and `|`-unions) or `enum Name { Variant(spec, ...), ... }`, which expand into `Name::check` sentences usable directly as preconditions/postconditions.
- **Static Arity Verification**: An arity checker runs before execution to ensure that stack push/pop operations match function signatures, avoiding runtime stack underflows.
- **Namespacing & Modularity**: Hierarchical module declarations (`mod name { ... }` or `mod name;`) with file-import support, relative/absolute path routing, and name visibility exports.

---

## Assembly Syntax & Structure

Hanoi Assembly files (`.hana`) consist of modules, symbols, sentences, and functions.

### Sentences and Functions
Hanoi supports two keywords to define execution blocks:
- `sentence`: Represents any sequence of operations.
- `function`: Represents a specialized sentence that takes exactly one input and returns exactly one output (implicitly annotated with an arity of `#[arity(1, 1)]`).

### Annotations
Sentences and functions can be annotated with metadata used by the compiler and static verification tools:
- `#[arity(inputs, outputs)]`: Declares the expected stack transition (implicit `#[arity(1, 1)]` for `function`).
- `#[precondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the input for the annotated function to be considered safe to call.
- `#[postcondition(fn_name)]`: Names a `1 -> 1` function that must evaluate to `true` on the output, given the precondition (if any) held on the input.
- `#[total]`: Asserts the function never panics on *any* input.
- `#[recursive]`: Marks a sentence that participates in a recursive call cycle, required by the verifier before it can model it.

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

    push (MyEnum::Case1::tag, (42, true))
    jump MyEnum::check
    assert
}
```
Each `type`/`enum` declaration expands into a module with a `check` sentence (`Name::check`) that consumes a value and pushes a `Bool`, so it can be used directly as a `#[precondition(...)]` or `#[postcondition(...)]`. See [docs/typecheck.md](docs/typecheck.md) for the verification model design (currently unimplemented) and [docs/hana.md](docs/hana.md) for the complete `type`/`enum` grammar.

---

## Conceptual Instruction Set Architecture (ISA)

The Hanoi VM supports a rich instruction set categorized into five main domains:

| Category | Instructions | Description |
| :--- | :--- | :--- |
| **Stack Ops** | `Push(V)`, `Drop`, `Pick(d)`, `Roll(d)` | Standard stack push, pop, copy/peek at depth, and rotate. `Pick` and `Roll` are the only instructions that address below the top of the stack. |
| **Arithmetic & Logic** | `Add`, `Subtract`, `Multiply`, `Divide`, `Modulo`, `Negate`, `Equal`, `Greater`, `Less`, `Not`, `And`, `Or` | Basic mathematical and Boolean logic operations. |
| **Control Flow** | `Dip(n, S)`, `Branch(S1, S2)`, `Panic`, `Assert`, `AssertEqual` | Subroutine execution under a hidden region of the stack (a plain `jump` is `Dip(0, S)`), conditional branching, and explicit panics. |
| **Composite Types** | `Tuple(n)`, `Untuple(n)`, `SymbolLen`, `SymbolCharAt`, `TupleLength` | Constructing and destructuring tuples, and analyzing symbols (immutable strings). |
| **Type Predicates** | `IsInt`, `IsBool`, `IsFloat`, `IsSymbol`, `IsTuple` | Runtime type tests, also used internally to compile `type`/`enum` predicates. |

---

## Project Architecture

The Hanoi codebase is structured as a cargo workspace with several key packages:

- **[bytecode](bytecode)**: The compiler frontend and validation pipeline.
  - [bytecode/src/assembly.rs](bytecode/src/assembly.rs): Parser and assembler that turns `.hana` source code into VM bytecode.
  - [bytecode/src/arity.rs](bytecode/src/arity.rs): Static arity checker for validating stack depths.
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

---

## Documentation

- [docs/hana.md](docs/hana.md): Detailed guide for Hanoi Assembly syntax, stack behavior, contract annotations, and key gotchas.
- [docs/hana_reference.md](docs/hana_reference.md): Complete reference of all available opcodes, organized by functionality.
- [docs/typecheck.md](docs/typecheck.md): Detailed SMT verification and symbolic execution design for the `typecheck` tool (currently removed from the codebase; kept as a design reference).
- [docs/machines.md](docs/machines.md): Specification of Hanoi's Communicating Sequential Processes (CSP) state machine semantics.
- [docs/compilation.md](docs/compilation.md): The compilation pipeline — the sugar and core ASTs, and what each phase from tokens to bytecode may assume.
- [docs/tactics.md](docs/tactics.md): The tactic language `bin/rewrite` uses to inline and rewrite compiled bytecode — the rule set, the combinators, and the laws they obey.
