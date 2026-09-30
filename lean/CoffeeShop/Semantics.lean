import CoffeeShop.Basic

/-!
# What the shop can do

The steps of the shop, read off the composition once and for all. `Move`
lists them with the states written out: a customer's own step, or a
handshake between two actors. `tr_move` says the shop takes no other step,
and `Move.tr` that it takes all of these; everything proved about the shop
goes through them rather than through the four nested compositions.
-/

namespace CoffeeShop

open CCS Customer.Phase Barista.State

/-- The moves of the shop. -/
inductive Move : Shop.State → Act Msg → Shop.State → Prop
  | wantA {pb xs b} :
      Move (((idle, pb), xs), b) (.inp (.want .alice)) (((thirsty, pb), xs), b)
  | wantB {pa xs b} :
      Move (((pa, idle), xs), b) (.inp (.want .bob)) (((pa, thirsty), xs), b)
  /-- Alice places her order with the queue. -/
  | orderA {pb xs b} :
      Move (((thirsty, pb), xs), b) .tau (((waiting, pb), xs ++ [Customer.alice.order]), b)
  | orderB {pa xs b} :
      Move (((pa, thirsty), xs), b) .tau (((pa, waiting), xs ++ [Customer.bob.order]), b)
  /-- The queue hands the barista the order at its front. -/
  | next {pa pb o xs} :
      Move (((pa, pb), o :: xs), idle) .tau (((pa, pb), xs), brewing o)
  /-- The barista hands Alice the drink made for her. -/
  | coffeeA {pb xs d} :
      Move (((waiting, pb), xs), brewing ⟨.alice, d⟩) .tau (((served d, pb), xs), idle)
  | coffeeB {pa xs d} :
      Move (((pa, waiting), xs), brewing ⟨.bob, d⟩) .tau (((pa, served d), xs), idle)
  | enjoyA {pb xs b d} :
      Move (((served d, pb), xs), b) (.out (.enjoy .alice d)) (((idle, pb), xs), b)
  | enjoyB {pa xs b d} :
      Move (((pa, served d), xs), b) (.out (.enjoy .bob d)) (((pa, idle), xs), b)

/-- The shop takes every move. -/
theorem Move.tr {s a s'} (h : Move s a s') : shop.Tr s a s' := by
  cases h with
  | wantA => exact .mk (.left (.left (.left .want))) rfl
  | wantB => exact .mk (.left (.left (.right .want))) rfl
  | orderA => exact .mk (.left (.comm (.left .order) (.push _ _) nofun)) trivial
  | orderB => exact .mk (.left (.comm (.right .order) (.push _ _) nofun)) trivial
  | next => exact .mk (.comm (.right (.pop _ _)) (.take _) nofun) trivial
  | coffeeA => exact .mk (.comm (.left (.left (.coffee _))) (.serve _ _) nofun) trivial
  | coffeeB => exact .mk (.comm (.left (.right (.coffee _))) (.serve _ _) nofun) trivial
  | enjoyA => exact .mk (.left (.left (.left (.enjoy _)))) rfl
  | enjoyB => exact .mk (.left (.left (.right (.enjoy _)))) rfl

/-- The shop takes no other step. -/
theorem tr_move {s a s'} (h : shop.Tr s a s') : Move s a s' := by
  obtain ⟨⟨⟨pa, pb⟩, xs⟩, b⟩ := s
  obtain ⟨⟨⟨pa', pb'⟩, xs'⟩, b'⟩ := s'
  obtain ⟨h, hfree⟩ := h
  cases h with
  | left h =>
    cases h with
    | left h =>
      cases h with
      | left h => cases h <;> simp [Act.Free, Msg.internal] at hfree <;> constructor
      | right h => cases h <;> simp [Act.Free, Msg.internal] at hfree <;> constructor
      | comm h₁ h₂ _ => cases h₁ <;> cases h₂
    | right h => cases h <;> simp [Act.Free, Msg.internal] at hfree
    | comm h₁ h₂ hne =>
      cases h₁ with
      | left h => cases h <;> cases h₂ <;> constructor
      | right h => cases h <;> cases h₂ <;> constructor
      | comm => exact absurd rfl hne
  | right h => cases h <;> simp [Act.Free, Msg.internal] at hfree
  | comm h₁ h₂ hne =>
    cases h₁ with
    | left h =>
      cases h with
      | left h => cases h <;> cases h₂ <;> constructor
      | right h => cases h <;> cases h₂ <;> constructor
      | comm => exact absurd rfl hne
    | right h => cases h <;> cases h₂ <;> constructor
    | comm => exact absurd rfl hne

end CoffeeShop
