import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp

/- Frozen specification: concrete definitions, intentional theorem proof holes.
Imports match the paired solution module; no solution import. -/

namespace Research.BoundaryScalar

open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def axis (p : ι) : ι → K := Pi.single p 1

def singularNormal (p : ι) : Matrix ι ι K :=
  diagonal fun i => if i = p then 0 else 1

def exchange (p q : ι) : Matrix ι ι K :=
  (1 : Matrix ι ι K).submatrix (Equiv.swap p q) id

def finiteNormal (p q : ι) : Matrix ι ι K :=
  exchange p q * singularNormal p

theorem adjugate_singularNormal (p : ι) :
    (singularNormal (K := K) p).adjugate = vecMulVec (axis p) (axis p) := by sorry

theorem adjugate_finiteNormal (p q : ι) (hpq : p ≠ q) :
    (finiteNormal (K := K) p q).adjugate =
      -vecMulVec (axis p) (axis q) := by sorry

theorem tensor_of_normal_form
    (D B T N : Matrix ι ι K) (z l z' l' : ι → K) (c : K)
    (hDB : D * B = T * N) (hz : z = B *ᵥ z') (hl : l ᵥ* T = l')
    (hcanonical : vecMulVec z' l' = c • N.adjugate) (hT : T.det ≠ 0) :
    vecMulVec z l = (c * B.det / T.det) • D.adjugate := by sorry

theorem finite_tensor
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (z l : ι → K)
    (hDB : D * B = T * finiteNormal p q) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) :
    vecMulVec z l =
      (-(l ᵥ* T) q * B.det / T.det) • D.adjugate := by sorry

theorem singular_tensor
    (p : ι) (D B T : Matrix ι ι K) (z l : ι → K)
    (hDB : D * B = T * singularNormal p) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) :
    vecMulVec z l =
      ((l ᵥ* T) p * B.det / T.det) • D.adjugate := by sorry

theorem finite_cross_ne_zero
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (l : ι → K)
    (hDB : D * B = T * finiteNormal p q)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hl : l ≠ 0) :
    (l ᵥ* T) q ≠ 0 := by sorry

theorem singular_cross_ne_zero
    (p : ι) (D B T : Matrix ι ι K) (l : ι → K)
    (hDB : D * B = T * singularNormal p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hl : l ≠ 0) :
    (l ᵥ* T) p ≠ 0 := by sorry

theorem finite_coordinate_iff
    (p q : ι) (hpq : p ≠ q) (D B T : Matrix ι ι K) (z l : ι → K) (u : K)
    (hDB : D * B = T * finiteNormal p q) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hB : B.det ≠ 0) (hl : l ≠ 0) :
    vecMulVec z l = u • D.adjugate ↔ u = -(l ᵥ* T) q * B.det / T.det := by sorry

theorem singular_coordinate_iff
    (p : ι) (D B T : Matrix ι ι K) (z l : ι → K) (u : K)
    (hDB : D * B = T * singularNormal p) (hz : z = B *ᵥ axis p)
    (hclosed : l ᵥ* D = 0) (hT : T.det ≠ 0) (hB : B.det ≠ 0) (hl : l ≠ 0) :
    vecMulVec z l = u • D.adjugate ↔ u = (l ᵥ* T) p * B.det / T.det := by sorry

theorem boundary_scalar_formula
    (p q : ι) (hpq : p ≠ q)
    (DF DS BF BS T : Matrix ι ι K) (zF zS lF lS : ι → K)
    (delta eta : K) (hdelta : delta ≠ 0) (heta : eta ≠ 0) (hT : T.det ≠ 0)
    (hDF : DF * BF = T * finiteNormal p q)
    (hDS : DS * BS = T * singularNormal p)
    (hzF : zF = BF *ᵥ axis p) (hzS : zS = BS *ᵥ axis p)
    (hlF : lF ᵥ* DF = 0) (hlS : lS ᵥ* DS = 0)
    (hlFne : lF ≠ 0) (hlSne : lS ≠ 0)
    (hBF : BF.det = eta) (hBS : BS.det = delta * eta) :
    let qF := (lF ᵥ* T) q
    let qS := (lS ᵥ* T) p
    let uF := -eta * qF / T.det
    let uS := delta * eta * qS / T.det
    vecMulVec zF lF = uF • DF.adjugate ∧
      vecMulVec zS lS = uS • DS.adjugate ∧
      qF ≠ 0 ∧ qS ≠ 0 ∧ uF ≠ 0 ∧ uS ≠ 0 ∧
      delta * uF / uS = -qF / qS := by sorry

theorem scalar_comparison (delta eta theta qF qS : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hqS : qS ≠ 0) :
    delta * (-qF * eta / theta) / (qS * (delta * eta) / theta) = -qF / qS := by sorry

theorem normalized_scalar_comparison (delta eta theta q : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hq : q ≠ 0) :
    delta * (-q * eta / theta) / (q * (delta * eta) / theta) = -1 := by sorry

theorem scalar_comparison_of_unit {R : Type*} [CommRing R]
    (f : R →+* K) (e : Rˣ) (delta eta theta qF qS : K)
    (hdelta : delta ≠ 0) (heta : eta ≠ 0) (htheta : theta ≠ 0) (hqS : qS ≠ 0)
    (hunit : qF = f (e : R) * qS) :
    delta * (-qF * eta / theta) / (qS * (delta * eta) / theta) =
      f ((-e : Rˣ) : R) := by sorry

end Research.BoundaryScalar
