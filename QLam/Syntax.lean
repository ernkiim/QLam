import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import QLam.QuantumState

abbrev Var := String

------------------------------------------------------------------------
-- Syntax of terms in the quantum lambda calculus.

section Syntax

-- Types
inductive Ty : Type where
| unit : Ty
| bit : Ty
| qbit : Ty
| arr : Ty → Ty → Ty
| tens : Ty → Ty → Ty
| bang : Ty → Ty
deriving DecidableEq, Repr
open Ty

notation "𝟙" => unit
infixr:1000 "⊸" => arr
infixl:1001 "⨂" => tens

-- Terms with quantum references represented by plain Nats
inductive Tm : Type where
| var : Var → Tm
| tt : Tm
| let_tt : Tm → Tm → Tm
| pair : Tm → Tm → Tm
| let_pair : Var → Var → Ty → Ty → Tm → Tm → Tm
| lam : Var → Ty → Tm → Tm
| app : Tm → Tm → Tm
| bang : Tm → Tm
| let_bang : Var → Ty → Tm → Tm → Tm
| zero : Tm
| one : Tm
| if_then_else : Tm → Tm → Tm → Tm
| qref : ℕ → Tm
| new : Tm
| meas : Tm → Tm
| gate : U n → Tm
deriving DecidableEq, Repr
open Tm

instance : Coe Var (Tm) := ⟨var⟩
instance : Coe Bool (Tm) := ⟨(if · then zero else one)⟩

-- Substitution of closed terms
@[simp, grind unfold]
def subst (x : Var) (t : Tm) : Tm → Tm
| var y => if x = y then t else y
| tt => tt
| let_tt t' t'' => let_tt (subst x t t') (subst x t t'')
| pair t₁ t₂ => pair (subst x t t₁) (subst x t t₂)
| let_pair y z A B t' t'' => let_pair y z A B (subst x t t')
  (if x = y ∨ x = z then t'' else (subst x t t''))
| lam y A t' => lam y A (if x = y then t' else subst x t t')
| app t₁ t₂ => app (subst x t t₁) (subst x t t₂)
| Tm.bang t' => bang (subst x t t')
| let_bang y A t' t'' =>
  let_bang y A (subst x t t') (if x = y then t'' else subst x t t'')
| zero => zero
| one => one
| if_then_else t₁ t₂ t₃ =>
  if_then_else (subst x t t₁) (subst x t t₂) (subst x t t₃)
| qref n => qref n
| new => new
| meas t' => meas (subst x t t')
| gate u => gate u

@[simp, grind unfold]
def FV : Tm → Finset Var -- how pleasant
| var x => {x}
| tt => ∅
| let_tt t t' => FV t ∪ FV t'
| pair t₁ t₂ => FV t₁ ∪ FV t₂
| let_pair x y _ _ t t' => FV t ∪ (FV t' \ {x,y})
| lam x _ t => FV t \ {x}
| app t₁ t₂ => FV t₁ ∪ FV t₂
| Tm.bang t => FV t
| let_bang x _ t t' => FV t ∪ (FV t' \ {x})
| zero => ∅
| one => ∅
| if_then_else t₁ t₂ t₃ => FV t₁ ∪ FV t₂ ∪ FV t₃
| qref _ => ∅
| new => ∅
| meas t => FV t
| gate _ => ∅

@[simp, grind unfold]
def maxQref : Tm → ℕ
| qref n        => n
| let_tt t u    => max (maxQref t) (maxQref u)
| pair t u      => max (maxQref t) (maxQref u)
| let_pair _ _ _ _ t u => max (maxQref t) (maxQref u)
| lam _ _ t     => maxQref t
| app t u       => max (maxQref t) (maxQref u)
| Tm.bang t        => maxQref t
| let_bang _ _ t u => max (maxQref t) (maxQref u)
| if_then_else t u v => max (maxQref t) (max (maxQref u) (maxQref v))
| meas t        => maxQref t
| _              => 0

end Syntax


--------------------------------------------------------------
-- Closures terms paired with sufficiently large quantum state

section Closure

open Ty
open Tm

@[ext]
structure Closure where
  qubits : ℕ
  state : Vect (2 ^ qubits)
  term : Tm

-- Replace qref 'i' with a bit 'b', shifting higher indices down
def k (i : Fin (n + 1)) (b : Bool) : Tm → Tm
| qref j =>
  if j < i then
    qref j
  else if j = i then
    b
  else
    qref (j - 1)
| var x => Tm.var x
| tt => tt
| let_tt t t' => let_tt (k i b t) (k i b t')
| pair t t' => pair (k i b t) (k i b t')
| let_pair x y A B t t' => let_pair x y A B (k i b t) (k i b t')
| lam x A t => lam x A (k i b t)
| app t t' => app (k i b t) (k i b t')
| Tm.bang t => Tm.bang (k i b t)
| let_bang x A t t' => let_bang x A (k i b t) (k i b t')
| zero => zero
| one => one
| if_then_else t₁ t₂ t₃ =>
  if_then_else (k i b t₁) (k i b t₂) (k i b t₃)
| new => new
| meas t => meas (k i b t)
| gate u => gate u

end Closure
