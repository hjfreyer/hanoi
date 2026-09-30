import CCS.Bisimulation
import CoffeeShop.Safety

/-!
# Everyone gets served

The shop never stalls on a customer: while somebody is thirsty or waiting it
has a silent step to take, and each silent step brings it measurably closer
to serving them. So from any reachable state, a customer who has asked for
coffee can be handed their usual by the shop's own steps alone.
-/

namespace CoffeeShop

open CCS Shop

/-- Silent steps never take a customer to or from `idle`; only the
environment does that. -/
theorem tau_idle {s s' c} (ht : shop.Tr s .tau s') :
    (s'.phase c = .idle ↔ s.phase c = .idle) := by
  cases tr_move ht <;> cases c <;> simp

/-- The shop can always do something for a customer who is thirsty or waiting. -/
theorem progress {s c} (h : Inv s) (hc : s.phase c = .thirsty ∨ s.phase c = .waiting) :
    ∃ s', shop.Tr s .tau s' := by
  obtain ⟨⟨⟨pa, pb⟩, xs⟩, b⟩ := s
  have hla := h.located .alice
  have hlb := h.located .bob
  cases c <;> simp at hc hla hlb <;> rcases hc with rfl | rfl
  · exact ⟨_, Move.orderA.tr⟩
  · -- Alice is waiting, so her order is in the shop's hands: queued, or being made.
    rcases b with _ | ⟨_ | _, d⟩
    · cases xs with
      | nil => simp at hla
      | cons o xs => exact ⟨_, Move.next.tr⟩
    · exact ⟨_, Move.coffeeA.tr⟩
    · -- The barista is making Bob's, so Bob is waiting for it.
      have hd := h.usual ⟨.bob, d⟩ (by simp)
      simp at hd
      subst hd
      cases pb <;> simp at hlb
      exact ⟨_, Move.coffeeB.tr⟩
  · exact ⟨_, Move.orderB.tr⟩
  · rcases b with _ | ⟨_ | _, d⟩
    · cases xs with
      | nil => simp at hlb
      | cons o xs => exact ⟨_, Move.next.tr⟩
    · have hd := h.usual ⟨.alice, d⟩ (by simp)
      simp at hd
      subst hd
      cases pa <;> simp at hla
      exact ⟨_, Move.coffeeA.tr⟩
    · exact ⟨_, Move.coffeeB.tr⟩

/-- How far a customer is from being served: three steps when they have yet
to order, two while their order is queued, one while it is being made. -/
def Shop.State.work₁ (s : Shop.State) (c : Customer) : Nat :=
  match s.phase c, s.barista with
  | .thirsty, _ => 3
  | .waiting, .idle => 2
  | .waiting, .brewing o => if o = c.order then 1 else 2
  | .idle, _ | .served _, _ => 0

/-- How much the shop has left to do. -/
def Shop.State.work (s : Shop.State) : Nat := s.work₁ .alice + s.work₁ .bob

theorem Shop.State.work₁_le_work (s : Shop.State) (c : Customer) : s.work₁ c ≤ s.work := by
  cases c <;> simp [work] <;> omega

/-- A customer who is thirsty or waiting has work left. -/
theorem Shop.State.work₁_pos {s : Shop.State} {c : Customer}
    (hc : s.phase c = .thirsty ∨ s.phase c = .waiting) : 1 ≤ s.work₁ c := by
  obtain ⟨⟨⟨pa, pb⟩, xs⟩, b⟩ := s
  cases c <;> simp at hc <;> rcases hc with rfl | rfl <;> rcases b with _ | ⟨_ | _, _ | _⟩ <;>
    simp [work₁]

/-- Every silent step lowers the work. -/
theorem work_lt {s s'} (h : Inv s) (ht : shop.Tr s .tau s') : s'.work < s.work := by
  have hla := h.located .alice
  have hlb := h.located .bob
  cases tr_move ht with
  | @orderA pb xs b =>
    -- Alice was not being served yet, so ordering takes her from 3 to 2.
    cases pb <;> rcases b with _ | ⟨_ | _, _ | _⟩ <;> simp_all [State.work, State.work₁]
  | @orderB pa xs b =>
    cases pa <;> rcases b with _ | ⟨_ | _, _ | _⟩ <;> simp_all [State.work, State.work₁]
  | @next pa pb o xs =>
    -- The order at the front is a waiting customer's; it goes from 2 to 1.
    have ho := h.usual o (by simp)
    rcases o with ⟨_ | _, _ | _⟩ <;> simp at ho <;> cases pa <;> cases pb <;>
      simp_all [State.work, State.work₁]
  | @coffeeA pb xs d =>
    -- The drink was made to Alice's order; she goes from 1 to 0.
    have hd : d = .latte := by simpa using h.usual ⟨.alice, d⟩ (by simp)
    subst hd
    cases pb <;> simp_all [State.work, State.work₁]
  | @coffeeB pa xs d =>
    have hd : d = .espresso := by simpa using h.usual ⟨.bob, d⟩ (by simp)
    subst hd
    cases pa <;> simp_all [State.work, State.work₁]

/-- From a state that satisfies the invariant, a customer who has asked for
coffee can be handed their usual by silent steps alone. -/
theorem served_of_inv {s c} (h : Inv s) (hc : s.phase c ≠ .idle) :
    ∃ s', shop.Silent s s' ∧ s'.phase c = .served c.usual := by
  suffices ∀ n s, s.work ≤ n → Inv s → s.phase c ≠ .idle →
      ∃ s', shop.Silent s s' ∧ s'.phase c = .served c.usual from
    this _ s (Nat.le_refl _) h hc
  intro n
  induction n with
  | zero =>
    intro s hw h hc
    have hw₁ := s.work₁_le_work c
    match hp : s.phase c with
    | .idle => exact absurd hp hc
    | .served d => exact ⟨s, .refl, by rw [hp, h.served c d hp]⟩
    | .thirsty | .waiting => have := s.work₁_pos (c := c) (by simp [hp]); omega
  | succ n ih =>
    intro s hw h hc
    match hp : s.phase c with
    | .idle => exact absurd hp hc
    | .served d => exact ⟨s, .refl, by rw [hp, h.served c d hp]⟩
    | .thirsty | .waiting =>
      obtain ⟨s₁, ht⟩ := progress (c := c) h (by simp [hp])
      have hw₁ := work_lt h ht
      obtain ⟨s', hs, hp'⟩ :=
        ih s₁ (by omega) (inv_step h ht) fun hi => hc ((tau_idle ht).mp hi)
      exact ⟨s', .head ht hs, hp'⟩

/-- Every customer who asks for coffee gets served, and gets their usual:
from any reachable state, the shop's own steps can take a customer who is
not idle to holding their usual drink. -/
theorem everyone_served {s c} (h : shop.Reach Shop.init s) (hc : s.phase c ≠ .idle) :
    ∃ s', shop.Silent s s' ∧ s'.phase c = .served c.usual :=
  served_of_inv (inv_reach h) hc

end CoffeeShop
