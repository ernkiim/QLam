import QLam.Syntax
import QLam.Semantics
import QLam.Typing

------------------------------------------------------------------------
-- (Beginnings of) typing properties of the quantum lambda calculus

section Properties

open FinPFun
open Tm
open has_type

variable
  (Γ Δ Δ₁ Δ₂ : Ctx)
  (t t' t₁ t₂ : Tm)
  (A B C : Ty)
  (x y : Var)

-- Quantum closures should be well-scoped (i.e. they should close the terms)
def well_formed (C : Closure) :=
   maxQref C.term ≤ C.qubits


@[grind →]
-- The condition 'x ∉ Γ' in lin_var ensures Γ and Δ have disjoint domain
theorem disjoint_dom_of_has_type (D : Γ;Δ ⊢ t ∶ A) : Disjoint (Dom Γ) (Dom Δ) := by
  (induction D <;> try simp) <;> try grind
  case arr_intro h _ ih =>
    simp! at ih
    exact Finset.disjoint_of_erase_left h ih

-- Want well-formed closures to reduce to well-formed closures
theorem wf_preservation : ∀ {C p C'},
    well_formed C → steps C p C' → well_formed C' := by
  sorry

-- Want well-typed closures to reduce to closures of the same type
-- Recall qrefs have type 'qbit' with no assumptions in our presentation
theorem type_preservation : ∀ {C p C' A},
    (∅;∅ ⊢ C.term ∶ A) → steps C p C' → ∅;∅ ⊢ C.term ∶ A := by
  sorry

theorem progress : ∀ {C A}, 
    well_formed C → (∅;∅ ⊢ C.term ∶ A) →
    value C.term ∨ ∃p C', step C p C' := by
  sorry

end Properties
