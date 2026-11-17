import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Adjugate tensor coordinates and changes of frame

Frozen concrete specification: selected theorem proof holes are intentional.
No solution module is imported. Reviewed against the intended mathematical contract.
Pinned target: Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

The coordinate is specified by the full matrix identity `z lambda = u adj(D)`.
It is NOT defined to be the scalar formula we wish to prove.
No Selmer complex, arithmetic functional or determinant-functor bridge is
constructed in this module. All matrix identities use the explicit adjugate
convention recorded in the accompanying mathematical specification.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Column times row, without an implicit pairing convention. -/
def tensor (z lam : n → K) : Matrix n n K := fun i j => z i * lam j

/-- Concrete cofactor specification of the class-functional coordinate. -/
def HasCoordinate (D : Matrix n n K) (z lam : n → K) (u : K) : Prop :=
  tensor z lam = u • D.adjugate

theorem coordinate_of_frame
    (D N : Matrix n n K) (B T : (Matrix n n K)ˣ)
    (z lam e ell : n → K) (u : K)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * N)
    (hz : z = (B : Matrix n n K) *ᵥ e)
    (hlam : lam ᵥ* (T : Matrix n n K) = ell)
    (hnormal : HasCoordinate N e ell u) :
    HasCoordinate D z lam
      ((B : Matrix n n K).det / (T : Matrix n n K).det * u) := by sorry

def normal (k : n) : Matrix n n K :=
  Matrix.diagonal (fun i => if i = k then 0 else 1)

/-- The adjugate is the projector onto the unique kernel coordinate. -/
theorem coordinate_of_closed_frame
    (D : Matrix n n K) (B T : (Matrix n n K)ˣ)
    (z lam : n → K) (k : n)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * normal k)
    (hz : z = (B : Matrix n n K) *ᵥ Pi.single k 1)
    (hclosed : lam ᵥ* D = 0) :
    HasCoordinate D z lam
      ((B : Matrix n n K).det / (T : Matrix n n K).det *
        (lam ᵥ* (T : Matrix n n K)) k) := by sorry

lemma adjugate_ne_zero_of_frame
    (D : Matrix n n K) (B T : (Matrix n n K)ˣ) (k : n)
    (hD : D * (B : Matrix n n K) = (T : Matrix n n K) * normal k) :
    D.adjugate ≠ 0 := by sorry

theorem coordinate_unique
    (D : Matrix n n K) (z lam : n → K) (u w : K)
    (hadj : D.adjugate ≠ 0)
    (hu : HasCoordinate D z lam u) (hw : HasCoordinate D z lam w) : u = w := by sorry

end Research.DerivativeSwitch.ScalarRatio
