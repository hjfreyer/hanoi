import Hanoi.Barista

/-!
# What is left to prove

`hana/barista.hant` directs the proofs of two claims about the customer's
`emit`: that on a well-formed state it answers a well-formed `(event, flag)`
pair, and the same claim stated as `#[type(is_state -> emit_postcondition)]`.
They are the corpus's biggest goals, and here they are the type of `emit`,
`Customer.Phase → Option Event`. There is nothing to prove.

What remains are the invariants `docs/machines.md` states in prose, which
`Machine.WellFormed` writes down. Each is a finite case analysis.
-/

namespace Hanoi.CoffeeShop

theorem customer_wellFormed (id : CustomerId) (drink : Drink) :
    (customer id drink).WellFormed where
  step_of_accept s e h := by
    cases s <;> cases e <;> simp_all [customer]
  step_of_emit s e h := by
    cases s <;> simp [customer] at h <;> subst h <;> simp [customer]
  ready_of_done s h := by
    simp [customer] at h

theorem barista_wellFormed : barista.WellFormed where
  step_of_accept s e h := by
    cases s <;> cases e <;> simp_all [barista] <;> split at h <;> simp_all
  step_of_emit s e h := by
    cases s <;> simp [barista] at h <;> subst h <;> simp [barista]
  ready_of_done s h := by
    simp [barista] at h

end Hanoi.CoffeeShop
