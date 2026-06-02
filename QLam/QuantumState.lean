import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation

open NNReal

-- Square complex matrices and vectors
abbrev Square n := Matrix (Fin n) (Fin n) ℂ
abbrev Vect n := Matrix (Fin n) (Fin 1) ℂ

def ket0 : Vect 2 := ![![0],![1]]
def ket1 : Vect 2 := ![![1],![0]]

-- Tensor product
def kronecker [Ring R] (A : Matrix (Fin a₁) (Fin a₂) R) (B : Matrix (Fin b₁) (Fin b₂) R) :
    Matrix (Fin (a₁ * b₁)) (Fin (a₂ * b₂)) R :=
  Matrix.of fun i j => A i.divNat j.divNat * B i.modNat j.modNat
infixl:999 " ⊗ " => kronecker

def identity (n : ℕ) : Square n :=
  Matrix.of fun i j => if i = j then 0 else 1

noncomputable def hadamard : Square 2 :=
  ((sqrt 2)⁻¹ : ℂ) • ![![1, 1],
                       ![1,-1]]

def pauliX : Square 2 :=
  ![![0, 1],
    ![1, 0]]

def pauliY : Square 2 :=
  ![![0, -Complex.I],
    ![Complex.I, 0]]

def pauliZ : Square 2 :=
  ![![1, 0],
    ![0, -1]]

def swap : Square 4 :=
  ![![1,0,0,0],
    ![0,0,1,0],
    ![0,1,0,0],
    ![0,0,0,1]]

def cnot : Square 4 :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0]]


------------------------------------------------------------------------
-- Padding

def pad (l u : ℕ) (A : Square (2 ^ n)) :=
  identity (2 ^ l) ⊗ A ⊗ identity (2 ^ u)

def pad_range (l d : ℕ) (A : Square (2 ^ n)) (h : l + n ≤ d) : Square (2 ^ d) :=
  have key : 2 ^ l * 2 ^ n * 2 ^ (d - (l + n)) = 2 ^ d := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  key ▸ pad l (d - (l + n)) A

------------------------------------------------------------------------
-- TODO: Partial measurement.
def partial_meas_prob (b : Bool) (i : ℕ) (φ : Vect (2 ^ (n + 1))) : ℝ:=
  sorry

def partial_meas_proj (b : Bool) (i : ℕ) (φ : Vect (2 ^ (n + 1))) : Vect (2 ^ n) :=
  sorry

------------------------------------------------------------------------
-- Enumerate some built-in unitaries
inductive U : ℕ → Type where
| I : U 1
| H : U 1
| X : U 1
| Y : U 1
| Z : U 1
| SWAP : U 2
| CNOT : U 2
deriving DecidableEq, Repr

open U

noncomputable def U.to_matrix : U n → Square (2 ^ n)
| I => identity 2
| H => hadamard
| X => pauliX
| Y => pauliY
| Z => pauliZ
| SWAP => swap
| CNOT => cnot
