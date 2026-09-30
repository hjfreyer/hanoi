/-!
# CSP machines

A Hanoi machine (`docs/machines.md`) is a deterministic labelled transition
system whose states each *accept* some events from the environment, *emit* at
most one event of their own accord, may take a silent `tau` step, and report
two termination flags.

This is that interface as Lean would state it:

* `Option` wherever Hanoi returns a `(value, has_value)` pair;
* a transition function that is partial by type (`Option State`) rather than
  by answering `()` on inputs off its domain;
* the state as a type parameter, the way Mathlib's `DFA α σ` is parameterised,
  so that a composite machine's state is a product and inherits `DecidableEq`
  and `Repr`;
* Hanoi's `compose_*` templates as ordinary functions on machines.
-/

namespace Hanoi

/-- A CSP machine over the alphabet `Event`, with states `State`. -/
structure Machine (Event State : Type) where
  /-- The starting state. Hanoi's `init` takes parameters; in Lean a
  parameterised machine is a function returning a `Machine`. -/
  init : State
  /-- Passive: will the machine take `e` from its environment in this state? -/
  accept : State → Event → Bool
  /-- Active: the one event the machine offers of its own accord, if any. -/
  emit : State → Option Event
  /-- The transition on an event, whether it was accepted or emitted.
  `none` when the event does not apply in this state. -/
  step : State → Event → Option State
  /-- A silent transition, if one is available. -/
  tau : State → Option State
  /-- Has the machine terminated? -/
  isDone : State → Bool
  /-- Is the machine content to stop here? A done machine must be. -/
  isReadyToFinish : State → Bool

namespace Machine

variable {E S : Type}

/-- The machine takes part in `e` at `s`: it accepts `e`, or `e` is what it emits. -/
def offers [DecidableEq E] (M : Machine E S) (s : S) (e : E) : Bool :=
  M.accept s e || M.emit s == some e

/-! ## Driving a machine

Hanoi's runtime (`lang/vm/src/runtime.rs`) alternates between letting the
machine run on its own and handing it events from the environment. These are
the pieces of that loop, as pure functions. -/

/-- The environment offers `e`. Taken only when the machine accepts it. -/
def inject (M : Machine E S) (s : S) (e : E) : Option S :=
  if M.accept s e then M.step s e else none

/-- The machine fires the event it emits, if any: the event, and the state after it. -/
def fire (M : Machine E S) (s : S) : Option (E × S) := do
  let e ← M.emit s
  let s' ← M.step s e
  pure (e, s')

/-- The machine fires `e`, which must be exactly what it emits. -/
def emits [DecidableEq E] (M : Machine E S) (s : S) (e : E) : Option S := do
  let (e', s') ← M.fire s
  guard (e' = e)
  pure s'

/-- Take silent steps until none is available, or `fuel` runs out. -/
def quiesce (M : Machine E S) : (fuel : Nat) → S → S
  | 0, s => s
  | fuel + 1, s =>
    match M.tau s with
    | some s' => M.quiesce fuel s'
    | none => s

/-- Run the machine on its own: silent steps are taken and emitted events are
fired, until neither is available or `fuel` runs out. Returns the events fired,
in order, and the final state. -/
def run (M : Machine E S) : (fuel : Nat) → S → List E × S
  | 0, s => ([], s)
  | fuel + 1, s =>
    match M.tau s with
    | some s' => M.run fuel s'
    | none =>
      match M.fire s with
      | some (e, s') =>
        let (es, s'') := M.run fuel s'
        (e :: es, s'')
      | none => ([], s)

/-! ## The machine as a labelled transition system

The view a library such as CSLib takes: a relation between states, labelled by
events, with `none` as the silent label. -/

/-- `M.Tr s l s'`: `M` moves from `s` to `s'` on label `l`. -/
inductive Tr (M : Machine E S) : S → Option E → S → Prop
  | event {s e s'} :
      (M.accept s e = true ∨ M.emit s = some e) → M.step s e = some s' → M.Tr s (some e) s'
  | tau {s s'} : M.tau s = some s' → M.Tr s none s'

/-- The invariants Hanoi's docs state in prose: the machine can take every
event it accepts or emits, and a done machine is ready to finish. -/
structure WellFormed (M : Machine E S) : Prop where
  step_of_accept : ∀ s e, M.accept s e = true → (M.step s e).isSome
  step_of_emit : ∀ s e, M.emit s = some e → (M.step s e).isSome
  ready_of_done : ∀ s, M.isDone s = true → M.isReadyToFinish s = true

/-! ## Composition

Hanoi's `compose_*` templates. `compose_static_closure` has no counterpart
here: it is function application. -/

section Composition

variable {E' S₁ S₂ : Type} [DecidableEq E]

/-- Parallel composition, Hanoi's `compose_concurrent`.

Events satisfying `sync` are shared: both sides take them together, and one
side may emit such an event only if the other takes part in it. Every other
event is taken by whichever side offers it, the left side first. -/
def concurrent (p : Machine E S₁) (q : Machine E S₂) (sync : E → Bool) :
    Machine E (S₁ × S₂) where
  init := (p.init, q.init)
  accept
    | (s₁, s₂), e =>
      if sync e then p.accept s₁ e && q.accept s₂ e
      else p.accept s₁ e || q.accept s₂ e
  emit
    | (s₁, s₂) =>
      -- What `q` emits, provided `p` takes part where it must.
      let fromQ := (q.emit s₂).filter fun e => !sync e || p.offers s₁ e
      match p.emit s₁ with
      | some e => if !sync e || q.offers s₂ e then some e else fromQ
      | none => fromQ
  step
    | (s₁, s₂), e =>
      if sync e then Prod.mk <$> p.step s₁ e <*> q.step s₂ e
      else if p.offers s₁ e then (·, s₂) <$> p.step s₁ e
      else if q.offers s₂ e then (s₁, ·) <$> q.step s₂ e
      else none
  tau
    | (s₁, s₂) => ((·, s₂) <$> p.tau s₁) <|> ((s₁, ·) <$> q.tau s₂)
  isDone
    | (s₁, s₂) =>
      (p.isDone s₁ && q.isReadyToFinish s₂) || (q.isDone s₂ && p.isReadyToFinish s₁)
  isReadyToFinish
    | (s₁, s₂) => p.isReadyToFinish s₁ || q.isReadyToFinish s₂

/-- Hiding, Hanoi's `compose_hidden`. Events satisfying `hidden` become
internal: the environment can neither offer nor observe them, and the machine
firing one is a silent step. -/
def hide (p : Machine E S) (hidden : E → Bool) : Machine E S where
  init := p.init
  accept s e := !hidden e && p.accept s e
  emit s := (p.emit s).filter (!hidden ·)
  step := p.step
  tau s := p.tau s <|> ((p.emit s).filter hidden >>= p.step s)
  isDone := p.isDone
  isReadyToFinish := p.isReadyToFinish

/-- Relabelling along an embedding of alphabets, Hanoi's `compose_prefix` and
`compose_rename_prefix`. `inj` spells the machine's events in the larger
alphabet, and `proj` reads them back, answering `none` for an event that is
not the machine's. -/
def relabel (p : Machine E S) (inj : E → E') (proj : E' → Option E) : Machine E' S where
  init := p.init
  accept s e' := (proj e').any (p.accept s)
  emit s := inj <$> p.emit s
  step s e' := proj e' >>= p.step s
  tau := p.tau
  isDone := p.isDone
  isReadyToFinish := p.isReadyToFinish

end Composition

end Machine

end Hanoi
