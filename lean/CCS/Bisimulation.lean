import CCS.Basic

/-!
# Behavioural equivalence

Two systems are bisimilar when each can match the other's steps forever. The
weak version lets silent steps go unmatched, which is what makes it possible
to compare a system that has internal workings with a specification that has
none.
-/

namespace CCS.LTS

variable {S T α : Type}

section Silent

variable (M : LTS S (Act α))

/-- `Silent s s'`: `s'` is reached from `s` by silent steps alone. -/
inductive Silent : S → S → Prop
  | refl {s} : Silent s s
  | tail {s t u} : Silent s t → M.Tr t .tau u → Silent s u

/-- The weak step `s ⇒a⇒ s'`: `a` with any number of silent steps around it,
or, for `a` itself silent, any number of silent steps. -/
inductive Weak : S → Act α → S → Prop
  | silent {s s'} : M.Silent s s' → Weak s .tau s'
  | act {s t a u s'} : M.Silent s t → M.Tr t a u → M.Silent u s' → Weak s a s'

variable {M}

theorem Silent.single {s s'} (h : M.Tr s .tau s') : M.Silent s s' := .tail .refl h

theorem Silent.trans {s t u} (h₁ : M.Silent s t) (h₂ : M.Silent t u) : M.Silent s u := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

theorem Silent.head {s t u} (h₁ : M.Tr s .tau t) (h₂ : M.Silent t u) : M.Silent s u :=
  (Silent.single h₁).trans h₂

/-- A step is a weak step. -/
theorem Weak.of_tr {s a s'} (h : M.Tr s a s') : M.Weak s a s' := .act .refl h .refl

/-- Silent steps are a weak silent step. -/
theorem Weak.of_silent {s s'} (h : M.Silent s s') : M.Weak s .tau s' := .silent h

/-- Silent steps before a weak step leave it a weak step. -/
theorem Weak.silent_left {s t a u} (h₁ : M.Silent s t) (h₂ : M.Weak t a u) : M.Weak s a u := by
  cases h₂ with
  | silent h => exact .silent (h₁.trans h)
  | act h h' h'' => exact .act (h₁.trans h) h' h''

end Silent

/-- `R` relates states of `M` and `N` that match each other's steps. -/
def IsBisimulation (M : LTS S L) (N : LTS T L) (R : S → T → Prop) : Prop :=
  ∀ s t, R s t →
    (∀ l s', M.Tr s l s' → ∃ t', N.Tr t l t' ∧ R s' t') ∧
    (∀ l t', N.Tr t l t' → ∃ s', M.Tr s l s' ∧ R s' t')

/-- Strong bisimilarity: some bisimulation relates the two states. -/
def Bisimilar (M : LTS S L) (N : LTS T L) (s : S) (t : T) : Prop :=
  ∃ R, IsBisimulation M N R ∧ R s t

/-- `R` relates states of `M` and `N` that match each other's steps up to
silent steps. -/
def IsWeakBisimulation (M : LTS S (Act α)) (N : LTS T (Act α)) (R : S → T → Prop) : Prop :=
  ∀ s t, R s t →
    (∀ a s', M.Tr s a s' → ∃ t', N.Weak t a t' ∧ R s' t') ∧
    (∀ a t', N.Tr t a t' → ∃ s', M.Weak s a s' ∧ R s' t')

/-- Weak bisimilarity: some weak bisimulation relates the two states. -/
def WeakBisimilar (M : LTS S (Act α)) (N : LTS T (Act α)) (s : S) (t : T) : Prop :=
  ∃ R, IsWeakBisimulation M N R ∧ R s t

end CCS.LTS
