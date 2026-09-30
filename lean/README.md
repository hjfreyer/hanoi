# Hanoi in Lean

Experiments in stating Hanoi's machines, and the claims about them, in Lean 4.
The first is a translation of the coffee shop from
[`hana/barista.hana`](../hana/barista.hana), written the way Lean would have
it rather than the way Hanoi does.

## Layout

| File | What it holds |
| --- | --- |
| `Hanoi/Machine.lean` | The machine interface of [`docs/machines.md`](../docs/machines.md); the driver loop as pure functions (`inject`, `fire`, `quiesce`, `run`); the transition relation `Tr` and the `WellFormed` invariants; Hanoi's `compose_*` templates as functions: `concurrent`, `hide`, `relabel`. |
| `Hanoi/Queue.lean` | The FIFO queue of [`hana/queue.hana`](../hana/queue.hana), generic in its element type. |
| `Hanoi/Barista.lean` | Customers, barista, and the network they form, open and hidden. |
| `Hanoi/Barista/Tests.lean` | The `test sentence`s of `barista.hana`, as `#guard`s and as `decide` proofs. |
| `Hanoi/Barista/Proofs.lean` | What is left to prove once the types have done their part. |
| `Main.lean` | `lake exe barista`: a morning at the shop, printed. |

## Building

Install [elan](https://github.com/leanprover/elan). `lean-toolchain` pins the
Lean version and `lake` fetches it on first use.

```bash
cd lean
lake build        # elaborates everything, which checks every #guard and example
lake exe barista  # runs the open shop and prints the events it fires
```

There are no dependencies, Mathlib included: core Lean has everything the
translation needs.

## How the translation departs from Hanoi

The *model* is Hanoi's: a machine accepts events passively, emits one event
actively, takes silent steps, and reports whether it is done. The *rendering*
is Lean's.

- **A structure, parameterised by state.** `Machine Event State` has the seven
  hooks as fields. The state is a type parameter, as in Mathlib's `DFA α σ`, so
  a composite's state is a product and `DecidableEq` and `Repr` come for free.
- **`Option`, not `(value, flag)`.** `emit : State → Option Event` and
  `tau : State → Option State` replace the `(event, has_event)` and
  `(state, did_reduce)` pairs.
- **Partial by type, not by junk.** Hanoi's `process` answers `()` on an event
  that does not apply; `step : State → Event → Option State` answers `none`.
- **Inductive alphabets and state spaces.** Tagged tuples such as
  `((id, drink), coffee)` become constructors, `Event.coffee (o : Order)`, and
  dispatch on a tag becomes pattern matching. Hanoi's path notation for the
  queue's channels is one constructor, `Event.queue`, and `Machine.relabel`
  lifts the generic queue into the shop's alphabet through it.
- **Parameters are parameters.** Hanoi keeps a customer's id and drink in its
  state and closes over them with `compose_static_closure`. Here `customer id
  drink` is a function returning a machine, and the state is the phase alone.
- **Composition is a function.** `compose_concurrent`, `compose_hidden`, and
  `compose_prefix` are `Machine.concurrent`, `Machine.hide` and
  `Machine.relabel`, each a few lines, with the same semantics as the templates
  in `lang/bytecode/src/templates/`.
- **The queue appends.** Hanoi's queue walks its cons-list one cell per `tau`
  step to append at the back, because Hanoi has no recursion. The Lean queue
  does `items ++ [x]`, so its `Descending` and `Rebuilding` states do not
  exist and the hidden shop settles in five silent steps where Hanoi takes
  seven. Its three "about to answer" states are one `replying reply next`.
- **Tests are theorems, when they want to be.** Each scenario is a value in the
  `Option` monad, checked by `#guard` at build time. The same equations are
  also stated as `example … := by decide`, which has the kernel evaluate them.
- **Two tests and two proofs disappear.** `verify_customer_is_event` and
  `verify_emit_totality` check that values have the shapes the machine
  expects; the two `.hant` proofs establish that `emit` answers a well-formed
  pair on a well-formed state. All four are the types of the definitions.

What Hanoi's own guarantees do not carry over is worth naming too. A Hanoi
sentence has a finite expansion and cannot recurse; `Machine.run` and
`Machine.quiesce` take a fuel argument instead, and a `List` can grow without
bound.

## Where to go next

- **Well-formedness of the network.** `Proofs.lean` proves `WellFormed` for
  the leaf machines. Proving that `concurrent`, `hide` and `relabel` preserve
  it gives the whole shop the property by construction.
- **The transition relation.** `Machine.Tr` is the labelled transition system
  a library such as [CSLib](https://github.com/leanprover/cslib) works with,
  with `none` as the silent label. Its `Bisimulation`, `TraceEq` and weak
  equivalences are how to state that `hiddenShop` behaves as a specification
  machine does.
- **Invariant checking.** [Veil](https://github.com/verse-lab/veil) is a Lean
  DSL for transition systems with SMT-discharged invariants; the shop is a
  natural test case for it.
- **The rest of the templates.** `compose_done`, `compose_emit_static` and
  `compose_accept_static` build Hanoi's `test mod` machines; they are small
  functions on `Machine` too.
