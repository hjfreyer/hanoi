# Hanoi (Hana)

Hanoi is a stack-oriented, VM-executed language designed to explore static analysis, algebraic effects, and formal verification in the context of stateful concurrency. Program source is written in **Hanoi Assembly** (with the `.hana` extension). Hanoi models concurrent systems via **Communicating Sequential Processes (CSP)** style state machines and uses an integrated static safety checker backed by the Z3 SMT solver to guarantee correctness.

> [!NOTE]
> This project is a research workspace containing the compiler/assembler, virtual machine runtime, testing tools, and a suite of formal contract verification experiments.

---

## Key Features

- **Stack-Oriented Execution**: A clean, instruction-driven virtual machine that uses a stack for operations, featuring standard manipulations (`drop`, `pick`, `roll`), arithmetic, and tuple structuring.
- **CSP State Machine Modeling**: Fully implements Communicating Sequential Processes (CSP) state machines. State machines are represented as modules with standardized hooks for managing state transitions, internal execution steps, and termination. See the [CSP Machines Documentation](docs/machines.md) for details.
- **Static Safety & Behavior Contracts**: Annotate functions with preconditions (`#[safety("...")]`) and postconditions (`#[behavior("...")]`). Hanoi uses symbolic execution to generate verification conditions and proves them using the Z3 SMT solver at compile time to guarantee panic-free execution.
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
Functions can be annotated with metadata used by the compiler and static verification tools:
- `#[arity(inputs, outputs)]`: Declares the expected stack transition.
- `#[safety("precondition")]`: Declares a logical precondition under which the function is guaranteed not to panic.
- `#[behavior("postcondition")]`: Declares the logical relationship between input stack elements (`in[k]`) and output stack elements (`out[j]`).

### Example: Contract Annotation & Verification
```hana
// A division wrapper that is statically guaranteed to never panic.
#[arity(2, 1)]
#[safety("is_numeric(in[0]) && is_numeric(in[1]) && in[0] != 0")]
#[behavior("out[0] == in[1] / in[0]")]
sentence safe_divide {
    divide
}

// Composed safety check:
// Pushing a value and duplicating it, then asserting equality, is statically proven safe.
#[arity(1, 2)]
#[behavior("out[0] == in[0] && out[1] == in[0]")]
sentence dup_val {
    pick 0
}

#[arity(2, 0)]
#[safety("in[0] == in[1]")]
sentence safe_assert_eq {
    assert_eq
}

#[arity(1, 0)]
sentence test_dup_safety {
    jump dup_val
    jump safe_assert_eq
}
```

---

## Conceptual Instruction Set Architecture (ISA)

The Hanoi VM supports a rich instruction set categorized into five main domains:

| Category | Instructions | Description |
| :--- | :--- | :--- |
| **Stack Ops** | `Push(V)`, `Drop(d)`, `Pick(d)`, `Roll(d)` | Standard stack push, drop at depth, copy/peek at depth, and rotate. |
| **Arithmetic & Logic** | `Add`, `Subtract`, `Multiply`, `Divide`, `Modulo`, `Negate`, `Equal`, `Greater`, `Less`, `Not`, `And`, `Or` | Basic mathematical and Boolean logic operations. |
| **Control Flow** | `Jump(S)`, `Branch(S1, S2)`, `Panic`, `Assert`, `AssertEqual` | Subroutine execution, conditional branching, and explicit panics. |
| **Composite Types** | `Tuple(n)`, `Untuple(n)`, `SymbolLen`, `SymbolCharAt` | Constructing and destructuring tuples, and analyzing symbols (immutable strings). |
| **Value Sets** | `SetContains`, `SetUnion`, `SetIntersection`, `SetDifference`, `SetComplement`, `SetSingleton`, `SetTuple(n)`, `SetRenamePrefix`, `SetChoose` | Comprehensive mathematical set operations. |

---

## Project Architecture

The Hanoi codebase is structured as a cargo workspace with several key packages:

- **[bytecode](bytecode)**: The compiler frontend and validation pipeline.
  - [bytecode/src/assembly.rs](bytecode/src/assembly.rs): Parser and assembler that turns `.hana` source code into VM bytecode.
  - [bytecode/src/arity.rs](bytecode/src/arity.rs): Static arity checker for validating stack depths.
  - [bytecode/src/safety](bytecode/src/safety): SMT-based safety contract checker that integrates with Z3.
- **[vm](vm)**: The virtual machine execution engine.
  - [vm/src/lib.rs](vm/src/lib.rs): Core interpreter, instruction dispatch loop, and stack representation.
  - [vm/src/runtime.rs](vm/src/runtime.rs): Asynchronous CSP coordinator that drives state machine step cycles.
- **[test-runner](test-runner)**: CLI harness that compiles and runs integration test suites.
- **[tests](tests)**: A collection of test cases covering all VM features, string/data parsers, queues, and multi-agent CSP networks.

---

## Getting Started

### Prerequisites

1. **Rust**: Install the latest stable Rust toolchain (2024 edition is used).
2. **Z3 SMT Solver**: Install Z3 to run the safety checker.
   - On Debian/Ubuntu: `sudo apt-get install z3`
   - On macOS (Homebrew): `brew install z3`

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

- [docs/hana.md](docs/hana.md): Detailed guide for Hanoi Assembly syntax, stack behavior, and key gotchas.
- [docs/hana_reference.md](docs/hana_reference.md): Complete reference of all available opcodes, organized by functionality.
- [SAFETY_CHECKER_DESIGN.md](SAFETY_CHECKER_DESIGN.md): Detailed SMT verification and symbolic execution design specification.
- [docs/machines.md](docs/machines.md): Specification of Hanoi's Communicating Sequential Processes (CSP) state machine semantics.
