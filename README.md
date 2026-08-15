# Hanoi (Hana)

Hanoi is a stack-oriented, VM-executed language designed to explore static analysis, algebraic effects, and formal verification in the context of stateful concurrency. Program source is written in **Hanoi Assembly** (with the `.hana` extension). Hanoi models concurrent systems via **Communicating Sequential Processes (CSP)** style state machines.

> [!NOTE]
> This project is a research workspace containing the compiler/assembler, virtual machine runtime, testing tools, and a suite of formal contract verification experiments.

---

## Key Features

- **Stack-Oriented Execution**: A clean, instruction-driven virtual machine that uses a stack for operations, featuring standard manipulations (`drop`, `pick`, `roll`), arithmetic, and tuple structuring.
- **Scoped Stack Frames**: `dip N { ... }` runs a block with the top `N` stack values hidden from it, so the arity checker can treat those values as unchanged across the call rather than tracking them through it. The instruction hides exactly one; `N` of them nested is what a width means.
- **Movement Without Depths**: the ISA moves values with `drop`, `copy`, `swap` and a one-deep `dip`, and nothing else. `pick d`, `roll d`, `drop d` and `dip N` are still what a program says, and the compiler writes each as the frames it stands for — a depth in an instruction is a pointer into the stack, and every law about one was an infinite family indexed by that pointer. See [docs/compilation.md](docs/compilation.md#why-the-depths-go-and-what-it-costs).
- **CSP State Machine Modeling**: Fully implements Communicating Sequential Processes (CSP) state machines. State machines are represented as modules with standardized hooks for managing state transitions, internal execution steps, and termination. See the [CSP Machines Documentation](docs/machines.md) for details.
- **Static Safety & Behavior Contracts** *(annotations only — verifier temporarily removed)*: Functions can be annotated with a precondition (`#[precondition(fn_name)]`) or a postcondition (`#[postcondition(fn_name)]`). Both are parsed and preserved, but the Z3-backed static verifier that proved them has been removed for now. See [docs/typecheck.md](docs/typecheck.md) for the design.
- **`type` / `enum` Predicate Sugar**: Declare reusable value predicates with `type Name <spec>;` (primitives — `int`, `bool`, `const_string`, `symbol`, `tuple` — literals, tuples, and `|`-unions) or `enum Name { Variant(spec, ...), ... }`, which expand into `Name::check` sentences usable directly as preconditions/postconditions.
- **Nothing Fails**: Every instruction answers on every input, with one value of the type it computes and nothing about how it got there. A data operation off its domain returns a deterministic default — `add` on two symbols is `0`, `untuple 3` of one is three `()`s — and a caller that needs to know asks before it hands the operands over. There is no `panic`, no `assert`, and no way for a program to end a run over a value: a problem is reported by answering with one. See [docs/totality.md](docs/totality.md).
- **Result-Answering Tests**: A `test sentence` hands back `((), ok)` or `(payload, err)` rather than halting the VM, built from `check_equals` and carried out by `?`. A failing test prints what it saw — `FAILED (err (5, 6))`. See [the reference](docs/hana.md#tests).
- **`?` for Results**: A result is the 2-tuple `(value, ok)` or `(value, err)`, and `?` unwraps one or leaves the block early carrying the error. It is sugar for two branches with the rest of the block inside an arm — including the drops that make the early return leave the stack the way finishing would. See [the reference](docs/hana.md#the--operator).
- **Static Arity Verification**: An arity checker runs before execution to ensure that stack push/pop operations match function signatures, avoiding runtime stack underflows.
- **No Recursion**: A sentence may not reach itself, by any route, and the compiler refuses one that does. Arity inference is what enforces it — a cycle is where inference cannot terminate — so every sentence has an inferred arity and a finite expansion, and a loop is written as the steps it takes. See [the reference](docs/hana.md#recursion-is-forbidden).
- **Namespacing & Modularity**: Hierarchical module declarations (`mod name { ... }` or `mod name;`) with file-import support, relative/absolute path routing, and name visibility exports.
- **Stated & Proved Identities**: `identity A = B;` states that two programs are interchangeable, and `bin/prove` discharges the claim by equality saturation over an algebraic term model — both sides of a goal go into one e-graph and the equations fire until they meet. A goal that sticks prints a **residual**: the smallest spelling each side reached, which is what says what to try next. See [docs/proving.md](docs/proving.md) and [docs/algebra.md](docs/algebra.md).

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

#[arity(0, 2)]
sentence test_type_and_enum {
    push 42
    jump TestInt::check
    // Stack: [true]

    push ((42, true), MyEnum::Case1::tag)
    jump MyEnum::check
    // Stack: [true, true]
}
```
Each `type`/`enum` declaration expands into a module with a `check` sentence (`Name::check`) that consumes a value and pushes a `Bool`, so it can be used directly as a `#[precondition(...)]` or `#[postcondition(...)]`. See [docs/typecheck.md](docs/typecheck.md) for the verification model design (currently unimplemented) and [docs/hana.md](docs/hana.md) for the complete `type`/`enum` grammar.

### Identities
A claim that two programs are interchangeable, stated in the source:

```hana
// identities.hana
identity testing_a_test { is_bool is_bool } = { drop 0 push true };
```

An identity is a claim rather than a program: it takes no `export` or `test`
marker and no contract annotation, and its two sides are compiled and named
`testing_a_test::lhs` and `::rhs` so that something can address them. The
compiler checks that the two sides leave the stack the same way, which is the
one property of the claim that holds however it might be proved.

`bin/prove` discharges the claims:

```bash
cargo run --bin prove -- tests
```

Every identity in `tests/identities.hana` closes on the rule set alone; the
pipeline, the equations, and the `.hant` stepping-stone file for goals that
need a bridge are described in [docs/proving.md](docs/proving.md).

---

## Conceptual Instruction Set Architecture (ISA)

The Hanoi VM supports a rich instruction set categorized into five main domains:

| Category | Instructions | Description |
| :--- | :--- | :--- |
| **Stack Ops** | `Push(V)`, `Drop`, `Copy`, `Swap` | Push, discard, duplicate the top value, exchange the top two. **No instruction takes a depth.** The surface language's `pick d`, `roll d` and `drop d` are spellings the compiler expands into frames around these. |
| **Arithmetic & Logic** | `Add`, `Subtract`, `Multiply`, `Divide`, `Modulo`, `Negate`, `Equal`, `Greater`, `Less`, `Not`, `And`, `Or` | Basic mathematical and Boolean logic operations. |
| **Control Flow** | `Jump(S)`, `Dip(S)`, `Branch(S1, S2)` | A call, a call under **one** hidden value, and conditional branching. `dip 3 { ... }` is three frames nested: a hidden region's width is a shape rather than a number, so no equation does arithmetic on it. |
| **Composite Types** | `Tuple(n)`, `Untuple(n)`, `ConstStringLen`, `ConstStringCharAt`, `TupleLength` | Constructing and destructuring tuples, and reading the length and characters of const strings. |
| **Type Predicates** | `IsInt`, `IsBool`, `IsConstString`, `IsSymbol`, `IsTuple` | Runtime type tests, also used internally to compile `type`/`enum` predicates. |

---

## Project Architecture

The Hanoi codebase is structured as a cargo workspace with several key packages:

- **[bytecode](bytecode)**: The compiler frontend and validation pipeline.
  - [bytecode/src/assembly.rs](bytecode/src/assembly.rs): Parser and assembler that turns `.hana` source code into VM bytecode.
  - [bytecode/src/arity.rs](bytecode/src/arity.rs): Static arity checker for validating stack depths.
- **[vm](vm)**: The virtual machine execution engine.
  - [vm/src/lib.rs](vm/src/lib.rs): Core interpreter, instruction dispatch loop, and stack representation.
  - [vm/src/runtime.rs](vm/src/runtime.rs): Asynchronous CSP coordinator that drives state machine step cycles.
- **[rewrite](rewrite)**: The prover.
  - [rewrite/src/term.rs](rewrite/src/term.rs): The algebraic term model — programs as two arity-exact operators (`;` and `*`) over a handful of leaves.
  - [rewrite/src/rules.rs](rewrite/src/rules.rs): The equations, as e-graph rewrites.
  - [rewrite/src/strategy.rs](rewrite/src/strategy.rs): The goal pipeline (peel, descend, saturate, inline) behind `bin/prove`.
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
- [docs/totality.md](docs/totality.md): Why every instruction answers on every input, and what that buys.
- [docs/proving.md](docs/proving.md): How `bin/prove` discharges identities — the goal pipeline, the e-graph, and the `.hant` stepping-stone files.
- [docs/algebra.md](docs/algebra.md): The equational theory itself — every structural law with its side conditions, and the map to the category-theory literature it comes from.
