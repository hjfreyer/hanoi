import CoffeeShop.Semantics

/-!
# Everyone gets the right drink

An invariant of the reachable states, and from it: whenever a customer
drinks, what they drink is their usual.
-/

namespace CoffeeShop

open CCS Shop

/-- The orders the barista has in hand. -/
def Barista.State.orders : Barista.State → List Order
  | .idle => []
  | .brewing o => [o]

@[simp] theorem Barista.State.orders_idle : Barista.State.idle.orders = [] := rfl
@[simp] theorem Barista.State.orders_brewing (o : Order) :
    (Barista.State.brewing o).orders = [o] := rfl

/-- The orders the shop has taken and not yet handed over: queued, then in
the making. -/
def Shop.State.inFlight (s : Shop.State) : List Order := s.queue ++ s.barista.orders

@[simp] theorem Shop.State.inFlight_mk (pa pb : Customer.Phase) (xs : List Order)
    (b : Barista.State) : State.inFlight (((pa, pb), xs), b) = xs ++ b.orders := rfl

/-- How many copies of a customer's order the shop holds, by where the
customer is: one while they wait for it, none otherwise. -/
def Customer.Phase.pending : Customer.Phase → Nat
  | .waiting => 1
  | .idle | .thirsty | .served _ => 0

@[simp] theorem Customer.Phase.pending_idle : Customer.Phase.idle.pending = 0 := rfl
@[simp] theorem Customer.Phase.pending_thirsty : Customer.Phase.thirsty.pending = 0 := rfl
@[simp] theorem Customer.Phase.pending_waiting : Customer.Phase.waiting.pending = 1 := rfl
@[simp] theorem Customer.Phase.pending_served (d : Drink) :
    (Customer.Phase.served d).pending = 0 := rfl

/-- What holds in every reachable state. -/
structure Inv (s : Shop.State) : Prop where
  /-- A waiting customer's order is in the shop's hands exactly once, and
  nobody else's is there at all. -/
  located : ∀ c, s.inFlight.count c.order = (s.phase c).pending
  /-- Every order in the shop's hands is its customer's usual. -/
  usual : ∀ o ∈ s.inFlight, o = o.customer.order
  /-- A customer holding coffee holds their usual. -/
  served : ∀ c d, s.phase c = .served d → d = c.usual

theorem inv_init : Inv Shop.init where
  located c := by cases c <;> simp [Shop.init]
  usual o h := by simp [Shop.init] at h
  served c d h := by cases c <;> simp [Shop.init] at h

theorem inv_step {s a s'} (h : Inv s) (ht : shop.Tr s a s') : Inv s' := by
  obtain ⟨hl, hu, hs⟩ := h
  cases tr_move ht with
  | wantA | wantB | enjoyA | enjoyB =>
    -- Nothing in the shop's hands changes.
    refine ⟨fun c => ?_, fun o ho => hu o (by simpa using ho), fun c d hd => ?_⟩
    · have := hl c; cases c <;> simpa using this
    · have := hs c d; cases c <;> simp at hd this ⊢ <;> exact this hd
  | orderA | orderB =>
    -- One more order at the back of the queue: its customer's, who was not
    -- being served yet.
    refine ⟨fun c => ?_, fun o ho => ?_, fun c d hd => ?_⟩
    · have := hl c
      cases c <;> simp at this ⊢ <;> omega
    · simp at ho
      rcases ho with ho | rfl | ho
      · exact hu o (by simp [ho])
      · rfl
      · exact hu o (by simp [ho])
    · have := hs c d; cases c <;> simp at hd this ⊢ <;> exact this hd
  | @next pa pb o xs =>
    -- The order at the front of the queue moves into the barista's hands.
    refine ⟨fun c => ?_, fun o' ho => ?_, fun c d hd => ?_⟩
    · have := hl c
      cases c <;> simp [List.count_cons] at this ⊢ <;> omega
    · simp at ho
      rcases ho with ho | rfl
      · exact hu o' (by simp [ho])
      · exact hu o' (by simp)
    · have := hs c d; cases c <;> simp at hd this ⊢ <;> exact this hd
  | @coffeeA pb xs d =>
    -- The drink handed over was made to order, so it is Alice's usual.
    have hd : d = .latte := by simpa using hu ⟨.alice, d⟩ (by simp)
    subst hd
    refine ⟨fun c => ?_, fun o ho => hu o (by simp at ho; simp [ho]), fun c d hd => ?_⟩
    · have := hl c
      cases c <;> simp at this ⊢ <;> omega
    · have := hs c d; cases c <;> simp at hd this ⊢ <;> first | exact hd.symm | exact this hd
  | @coffeeB pa xs d =>
    have hd : d = .espresso := by simpa using hu ⟨.bob, d⟩ (by simp)
    subst hd
    refine ⟨fun c => ?_, fun o ho => hu o (by simp at ho; simp [ho]), fun c d hd => ?_⟩
    · have := hl c
      cases c <;> simp at this ⊢ <;> omega
    · have := hs c d; cases c <;> simp at hd this ⊢ <;> first | exact hd.symm | exact this hd

/-- The invariant holds of every reachable state. -/
theorem inv_reach {s} (h : shop.Reach Shop.init s) : Inv s := by
  induction h with
  | refl => exact inv_init
  | step _ ht ih => exact inv_step ih ht

/-- Whenever a customer drinks, they drink their usual. -/
theorem right_drink {s s' c d} (h : shop.Reach Shop.init s)
    (ht : shop.Tr s (.out (.enjoy c d)) s') : d = c.usual := by
  have hI := inv_reach h
  cases tr_move ht with
  | enjoyA => exact hI.served .alice d rfl
  | enjoyB => exact hI.served .bob d rfl

/-- The same, along any run from the opening of the shop. -/
theorem right_drink_path {s ls c d} (h : shop.Path Shop.init ls s)
    (hm : Act.out (Msg.enjoy c d) ∈ ls) : d = c.usual := by
  suffices ∀ s₀ ls s, shop.Reach Shop.init s₀ → shop.Path s₀ ls s →
      Act.out (Msg.enjoy c d) ∈ ls → d = c.usual from this _ _ _ .refl h hm
  clear h hm
  intro s₀ ls s hr hp hm
  induction hp with
  | nil => simp at hm
  | cons ht _ ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact right_drink hr ht
    · exact ih (hr.step ht) hm

end CoffeeShop
