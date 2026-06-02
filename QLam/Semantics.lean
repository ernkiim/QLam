import Mathlib.Data.Matrix.Basic

import QLam.Syntax
import QLam.QuantumState

open Matrix
open Tm

------------------------------------------------------------------------
-- Values
inductive value : Tm → Prop where
| qref_val : value (qref i)
| lam_val : value (lam x A t)
| true_val : value true
| false_val : value false
| gate_val : value (gate u)
| tt_val : value tt
| pair_val : value v → value w → value (pair v w)

------------------------------------------------------------------------
-- Probabilistic reduction semantics
inductive step : Closure → ℝ → Closure → Prop where
| beta_app : step ⟨n, Q, app (lam x _ t) u⟩ 1 ⟨n, Q, subst x u t⟩
| comp_app_1 : step ⟨n, Q, u⟩ p ⟨n', Q', u'⟩ →
    step ⟨n, Q, app t u⟩ p ⟨n', Q', app t u'⟩ 
| comp_app_2 : value v → step ⟨n, Q, t⟩ p ⟨n', Q', t'⟩ →
    step ⟨n, Q, app t v⟩ p ⟨n', Q', app t' v⟩
| comp_pair_1 : step ⟨n, Q, u⟩ p ⟨n', Q', u'⟩ → 
    step ⟨n, Q, pair u t⟩ p ⟨n', Q', pair u' t⟩
| comp_pair_2 : step ⟨n, Q, u⟩ p ⟨n', Q', u'⟩ → 
    step ⟨n, Q, pair t u⟩ p ⟨n', Q', pair t u'⟩
| if_true  : step ⟨n, Q, if_then_else false t _⟩ 1 ⟨n, Q, t⟩
| if_false : step ⟨n, Q, if_then_else false _ t⟩ 1 ⟨n, Q, t⟩
| comp_if : step ⟨n, Q, u⟩ p ⟨n', Q', u'⟩ →
    step ⟨n, Q, if_then_else u t v⟩ p ⟨n', Q', if_then_else u' t v⟩
 -- partial_meas_prob and _proj are undefined placeholders
| measure (b : Bool) :
   step
     ⟨n + 1, Q, meas (qref i)⟩
     (partial_meas_prob b i Q)
     ⟨n, partial_meas_proj b i Q, b⟩
-- gates are applied to adjacent qubits, use SWAP
| gate_app (u : U n) (Q : Vect (2 ^ d)) :
  ∀ l, (h : l + n ≤ d) →
    step
      ⟨d, Q, app (gate u) (qref l)⟩
      1
      ⟨d, (pad_range l d u.to_matrix h) * Q, qref l⟩
| mk_new : step ⟨n, Q, new⟩ 1 ⟨n + 1, Q ⊗ ket0, qref n⟩ 
| beta_let_bang : step ⟨n, Q, let_bang x A t u⟩ 1 ⟨n, Q, subst x t u⟩
| beta_let_pair : step
    ⟨n, Q, let_pair x y A B (pair t₁ t₂) u⟩
    1
    ⟨n, Q, subst x t₁ (subst y t₂ u)⟩

-- Accumulate total probability
inductive steps : Closure → ℝ → Closure → Prop where
| refl : steps c 1 c
| tran : step c p c' → steps c' p' c'' → steps c (p * p') c''
