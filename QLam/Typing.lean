import QLam.Syntax
import QLam.Semantics
import QLam.FinPFun

open FinPFun
open Tm
open Ty

-- Types are defined in Syntax
section Typing

-- Contexts are finite maps from variables to types
abbrev Ctx := Var →f Ty

-- Types of some built-in unitaries
def U_type : U n → Ty × Ty
| U.I    => (qbit, qbit)
| U.H    => (qbit, qbit)
| U.X    => (qbit, qbit)
| U.Y    => (qbit, qbit)
| U.Z    => (qbit, qbit)
| U.SWAP => (qbit ⨂ qbit, qbit ⨂ qbit)
| U.CNOT => (qbit ⨂ qbit, qbit ⨂ qbit)

@[grind]
inductive has_type : Ctx → Ctx → Tm → Ty → Prop where

| qref_qbit : has_type Γ ∅ (qref i) qbit
| new_qbit  : has_type Γ ∅ new qbit
| meas_bit  : has_type Γ Δ t qbit → has_type Γ Δ (meas t) (Ty.bang bit)
| gate_type : has_type Γ ∅ (gate u) ((U_type u).1 ⊸ (U_type u).2)
 
| int_var : ⟨x, A⟩ ∈ Γ.graph → has_type Γ ∅ (var x) A
| lin_var : x ∉ Γ.Dom → has_type Γ (singleton ⟨x, A⟩) (var x) A
 
| unit_intro : has_type Γ ∅ tt unit
| unit_elim (h : Disjoint (Dom Δ₁) (Dom Δ₂)) :
    has_type Γ Δ₁ t unit →
    has_type Γ Δ₂ u A →
    has_type Γ (conj Δ₁ Δ₂ h) (let_tt t u) A
 
| tens_intro (h : Disjoint (Dom Δ₁) (Dom Δ₂)) :
    has_type Γ Δ₁ t A →
    has_type Γ Δ₂ u B →
    has_type Γ (conj Δ₁ Δ₂ h) (pair t u) (A ⨂ B)
 
| tens_elim
  (h₁ : Disjoint (Dom Δ₁) (Dom Δ₂))
  (h₂ : x ∉ Dom Δ₂)
  (h₃ : y ∉ Dom Δ₂)
  (h₄ : x ≠ y) :
    has_type Γ Δ₁ u (tens A B) →
    has_type Γ (⟨x, A⟩ :[by grind]: (⟨y, B⟩ :[h₃]: Δ₂)) t C →
    has_type Γ (conj Δ₁ Δ₂ h₁) (let_pair x y A B u t) C
    
| arr_intro (h : x ∉ Dom Δ) :
    -- Shadow in the int. context
    has_type (erase Γ x) (⟨x,A⟩ :[h]: Δ) t B →
    has_type Γ Δ (lam x A t) (A ⊸ B)
| arr_elim (h : Disjoint (Dom Δ₁) (Dom Δ₂)) :
    has_type Γ Δ₁ u (A ⊸ B) →
    has_type Γ Δ₂ t A →
    has_type Γ (conj Δ₁ Δ₂ h) (app u t) B
 
| bang_intro :
    has_type Γ ∅ t A →
    has_type Γ ∅ (Tm.bang t) A
| bang_elim (h₁ : Disjoint (Dom Δ₁) (Dom Δ₂)) (h₂ : x ∉ Dom Δ₂):
    has_type Γ Δ₁ u (Ty.bang A) →
    -- Shadow in the int. context
    has_type (Γ :+ ⟨x, A⟩) Δ₂ t B →
    has_type Γ (conj Δ₁ Δ₂ h₁) (let_bang x A u t) B
 
| zero_bit : has_type Γ ∅ zero bit
| one_bit : has_type Γ ∅ zero bit
| if_type (h : Disjoint (Dom Δ₁) (Dom Δ₂)) :
  has_type Γ Δ₁ t bit →
  has_type Γ Δ₂ u A →
  has_type Γ Δ₂ v A →
  has_type Γ (conj Δ₁ Δ₂ h) (if_then_else t u v) A

notation Γ:90 ";" Δ:90 " ⊢ " t " ∶ " A => has_type Γ Δ t A

end Typing
