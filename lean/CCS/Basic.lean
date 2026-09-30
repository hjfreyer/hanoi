/-!
# Labelled transition systems, and the operators of CCS

A concurrent system is a labelled transition system: a set of states and a
relation saying where each labelled step from a state leads. Milner's CCS
gives a handful of ways to build such systems from smaller ones. This file
has the two the coffee shop needs: parallel composition, in which the two
sides move independently or handshake on complementary actions, and
restriction, which stops the environment from taking part in named actions.
-/

namespace CCS

/-- A labelled transition system over labels `Label`. -/
structure LTS (State Label : Type) where
  /-- `Tr s l s'`: from `s`, a step labelled `l` leads to `s'`. -/
  Tr : State → Label → State → Prop

namespace LTS

variable {S L : Type} (M : LTS S L)

/-- `Reach s s'`: `s'` can be reached from `s`. -/
inductive Reach (s : S) : S → Prop
  | refl : Reach s s
  | step {t l u} : Reach s t → M.Tr t l u → Reach s u

/-- `Path s ls s'`: taking the labels `ls` in order leads from `s` to `s'`. -/
inductive Path : S → List L → S → Prop
  | nil {s} : Path s [] s
  | cons {s l t ls u} : M.Tr s l t → Path t ls u → Path s (l :: ls) u

/-- Some step is available. -/
def Enabled (s : S) : Prop := ∃ l s', M.Tr s l s'

end LTS

/-- The actions of CCS over names `α`: a name (an input), its co-name (an
output), and the silent action. Value passing is encoded by letting names
carry values: `order o` is a name for each order `o`. -/
inductive Act (α : Type)
  | tau
  | inp (a : α)
  | out (a : α)
  deriving DecidableEq, Repr

namespace Act

variable {α : Type}

/-- The complementary action: what the other party to a handshake does. -/
def co : Act α → Act α
  | tau => tau
  | inp a => out a
  | out a => inp a

@[simp] theorem co_tau : (tau : Act α).co = tau := rfl
@[simp] theorem co_inp (a : α) : (inp a).co = out a := rfl
@[simp] theorem co_out (a : α) : (out a).co = inp a := rfl

/-- The action is not on one of the names `H` restricts. -/
def Free (H : α → Bool) : Act α → Prop
  | tau => True
  | inp a | out a => H a = false

@[simp] theorem free_tau (H : α → Bool) : (tau : Act α).Free H := trivial
@[simp] theorem free_inp (H : α → Bool) (a : α) : (inp a).Free H ↔ H a = false := Iff.rfl
@[simp] theorem free_out (H : α → Bool) (a : α) : (out a).Free H ↔ H a = false := Iff.rfl

end Act

namespace LTS

variable {S T α : Type}

/-- The steps of `P ∥ Q`: either side moves on its own, or both move on
complementary actions, and the handshake is silent. -/
inductive Par.Tr (P : LTS S (Act α)) (Q : LTS T (Act α)) : S × T → Act α → S × T → Prop
  | left {s a s' t} : P.Tr s a s' → Par.Tr P Q (s, t) a (s', t)
  | right {s t a t'} : Q.Tr t a t' → Par.Tr P Q (s, t) a (s, t')
  | comm {s t a s' t'} : P.Tr s a s' → Q.Tr t a.co t' → a ≠ .tau →
      Par.Tr P Q (s, t) .tau (s', t')

/-- Parallel composition. -/
abbrev par (P : LTS S (Act α)) (Q : LTS T (Act α)) : LTS (S × T) (Act α) := ⟨Par.Tr P Q⟩

@[inherit_doc par] infixl:65 " ∥ " => par

/-- The steps of `P \ H`: those of `P` that are not on a restricted name. A
handshake on a restricted name has already become a silent step inside `P`. -/
inductive Restrict.Tr (P : LTS S (Act α)) (H : α → Bool) : S → Act α → S → Prop
  | mk {s a s'} : P.Tr s a s' → a.Free H → Restrict.Tr P H s a s'

/-- Restriction: the environment takes no part in actions on the names `H`. -/
abbrev restrict (P : LTS S (Act α)) (H : α → Bool) : LTS S (Act α) := ⟨Restrict.Tr P H⟩

end LTS

end CCS
