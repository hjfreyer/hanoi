import CCS.Bisimulation
import CoffeeShop.Progress

/-!
# The shop, as its customers see it

A specification: each customer asks for coffee and then drinks their usual,
and nothing else ever happens. The shop is weakly bisimilar to it. That says
the two theorems of the previous files at once, and more: nothing the
environment can observe tells the shop apart from the specification.
-/

namespace CoffeeShop

open CCS

namespace Spec

inductive Phase
  | idle | waiting
  deriving DecidableEq, Repr

/-- `Spec(c) = want(c). enjoy(c, c.usual)‾. Spec(c)` -/
inductive Step (c : Customer) : Phase → Act Msg → Phase → Prop
  | want : Step c .idle (.inp (.want c)) .waiting
  | enjoy : Step c .waiting (.out (.enjoy c c.usual)) .idle

abbrev lts (c : Customer) : LTS Phase (Act Msg) := ⟨Step c⟩

/-- What the specification sees of a customer's phase. -/
def abs : Customer.Phase → Phase
  | .idle => .idle
  | .thirsty | .waiting | .served _ => .waiting

@[simp] theorem abs_idle : abs .idle = .idle := rfl
@[simp] theorem abs_thirsty : abs .thirsty = .waiting := rfl
@[simp] theorem abs_waiting : abs .waiting = .waiting := rfl
@[simp] theorem abs_served (d : Drink) : abs (.served d) = .waiting := rfl

end Spec

/-- `Spec = Spec(alice) ∥ Spec(bob)` -/
abbrev spec : LTS (Spec.Phase × Spec.Phase) (Act Msg) := Spec.lts .alice ∥ Spec.lts .bob

/-- The relation: a shop state satisfying the invariant, against what its
customers' phases look like from outside. -/
structure Spec.R (s : Shop.State) (t : Spec.Phase × Spec.Phase) : Prop where
  inv : Inv s
  abs : t = (Spec.abs (s.phase .alice), Spec.abs (s.phase .bob))

theorem tau_abs {s s' c} (ht : shop.Tr s .tau s') :
    Spec.abs (s'.phase c) = Spec.abs (s.phase c) := by
  cases tr_move ht <;> cases c <;> simp

theorem silent_abs {s s' c} (h : shop.Silent s s') :
    Spec.abs (s'.phase c) = Spec.abs (s.phase c) := by
  induction h with
  | refl => rfl
  | tail _ ht ih => rw [tau_abs ht, ih]

theorem inv_silent {s s'} (h : Inv s) (hs : shop.Silent s s') : Inv s' := by
  induction hs with
  | refl => exact h
  | tail _ ht ih => exact inv_step ih ht

/-- The specification matches every step of the shop. -/
theorem Spec.forward {s t a s'} (hR : Spec.R s t) (ht : shop.Tr s a s') :
    ∃ t', spec.Weak t a t' ∧ Spec.R s' t' := by
  obtain ⟨hI, rfl⟩ := hR
  have hI' := inv_step hI ht
  cases tr_move ht with
  | wantA => exact ⟨_, .of_tr (.left .want), hI', rfl⟩
  | wantB => exact ⟨_, .of_tr (.right .want), hI', rfl⟩
  | @enjoyA pb xs b d =>
    obtain rfl : d = .latte := hI.served .alice d rfl
    exact ⟨_, .of_tr (.left .enjoy), hI', rfl⟩
  | @enjoyB pa xs b d =>
    obtain rfl : d = .espresso := hI.served .bob d rfl
    exact ⟨_, .of_tr (.right .enjoy), hI', rfl⟩
  | orderA | orderB | next | coffeeA | coffeeB => exact ⟨_, .of_silent .refl, hI', rfl⟩

/-- The shop matches every step of the specification, up to silent steps. -/
theorem Spec.backward {s t a t'} (hR : Spec.R s t) (ht : spec.Tr t a t') :
    ∃ s', shop.Weak s a s' ∧ Spec.R s' t' := by
  obtain ⟨hI, rfl⟩ := hR
  obtain ⟨⟨⟨pa, pb⟩, xs⟩, b⟩ := s
  simp only [Shop.State.phase_alice, Shop.State.phase_bob] at ht
  generalize hqa : Spec.abs pa = qa at ht
  generalize hqb : Spec.abs pb = qb at ht
  cases ht with
  | left h =>
    cases h with
    | want =>
      cases pa <;> simp at hqa
      exact ⟨_, .of_tr Move.wantA.tr, inv_step hI Move.wantA.tr, by simp [hqb]⟩
    | enjoy =>
      -- Alice has asked for coffee; the shop serves her, and then she drinks.
      obtain ⟨s₁, hs, hp⟩ := served_of_inv hI (c := .alice) (by cases pa <;> simp_all)
      obtain ⟨⟨⟨pa₁, pb₁⟩, xs₁⟩, b₁⟩ := s₁
      simp at hp
      subst hp
      refine ⟨_, .act hs Move.enjoyA.tr .refl, inv_step (inv_silent hI hs) Move.enjoyA.tr, ?_⟩
      have := silent_abs (c := .bob) hs
      simp_all
  | right h =>
    cases h with
    | want =>
      cases pb <;> simp at hqb
      exact ⟨_, .of_tr Move.wantB.tr, inv_step hI Move.wantB.tr, by simp [hqa]⟩
    | enjoy =>
      obtain ⟨s₁, hs, hp⟩ := served_of_inv hI (c := .bob) (by cases pb <;> simp_all)
      obtain ⟨⟨⟨pa₁, pb₁⟩, xs₁⟩, b₁⟩ := s₁
      simp at hp
      subst hp
      refine ⟨_, .act hs Move.enjoyB.tr .refl, inv_step (inv_silent hI hs) Move.enjoyB.tr, ?_⟩
      have := silent_abs (c := .alice) hs
      simp_all
  | comm h₁ h₂ _ => cases h₁ <;> cases h₂

/-- The shop is, to its environment, two customers who each ask for coffee
and drink their usual. -/
theorem shop_bisimilar_spec : shop.WeakBisimilar spec Shop.init (.idle, .idle) :=
  ⟨Spec.R, fun _ _ hR => ⟨fun _ _ => Spec.forward hR, fun _ _ => Spec.backward hR⟩,
    inv_init, rfl⟩

end CoffeeShop
