import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Geometric and arithmetic Frobenius on a representation and its dual

For the geometric normalization of the cohomological representation, a lift `σ`
of arithmetic Frobenius is evaluated at `σ⁻¹`. Its dual is then arithmetically
normalized, with the same full characteristic polynomial. Coefficient extension
and passage to the trace use that very same matrix data.
-/

namespace ModularFrobeniusDual

open Matrix Polynomial

section Dual

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S] {n : ℕ}

/-- The contragredient in the basis dual to the chosen basis of `ρ`. -/
def dual (ρ : G →* GL (Fin n) R) : G →* GL (Fin n) R where
  toFun σ := ⟨(ρ σ⁻¹ : Matrix (Fin n) (Fin n) R).transpose,
    (ρ σ : Matrix (Fin n) (Fin n) R).transpose,
    by rw [← transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' σ τ := Units.ext (by
    simp only [_root_.mul_inv_rev, map_mul, Units.val_mul, transpose_mul])

theorem continuous_dual [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace R]
    (ρ : G →* GL (Fin n) R) (hρ : Continuous ρ) : Continuous (dual ρ) := by
  rw [Units.continuous_iff]
  exact ⟨((Units.continuous_val.comp hρ).comp continuous_inv).matrix_transpose,
    (Units.continuous_val.comp hρ).matrix_transpose⟩

@[simp] theorem dual_eq_one_iff (ρ : G →* GL (Fin n) R) (σ : G) :
    dual ρ σ = 1 ↔ ρ σ = 1 := by
  constructor
  · intro h
    have hi := congrArg (fun A : GL (Fin n) R => (↑A⁻¹ : Matrix (Fin n) (Fin n) R)) h
    change (ρ σ : Matrix (Fin n) (Fin n) R).transpose = 1 at hi
    exact Units.ext (by simpa using congrArg Matrix.transpose hi)
  · intro h
    apply Units.ext
    change (ρ σ⁻¹ : Matrix (Fin n) (Fin n) R).transpose = 1
    rw [map_inv, h, inv_one, Units.val_one, transpose_one]

theorem charpoly_dual (ρ : G →* GL (Fin n) R) (σ : G) :
    (dual ρ σ : Matrix (Fin n) (Fin n) R).charpoly =
      (ρ σ⁻¹ : Matrix (Fin n) (Fin n) R).charpoly :=
  charpoly_transpose _

/-- Scalar extension commutes with taking the contragredient, with no basis change. -/
theorem map_dual (φ : R →+* S) (ρ : G →* GL (Fin n) R) :
    (GeneralLinearGroup.map φ).comp (dual ρ) = dual ((GeneralLinearGroup.map φ).comp ρ) := by
  ext σ : 1
  apply Units.ext
  rfl

end Dual

/-- Convert the convention `det (1 - X M)` into a monic characteristic polynomial.
The reflection uses degree two of `M.charpoly`, not the degree of the Euler polynomial. -/
theorem charpoly_of_eulerPolynomial {R : Type*} [CommRing R] [Nontrivial R]
    (M : Matrix (Fin 2) (Fin 2) R) (a b : R)
    (h : M.charpolyRev = 1 - C a * X + C b * X ^ 2) :
    M.charpoly = X ^ 2 - C a * X + C b := by
  have hr : M.charpoly.reflect 2 = 1 - C a * X + C b * X ^ 2 := by
    rw [← M.reverse_charpoly] at h
    simpa [Polynomial.reverse, M.charpoly_natDegree_eq_dim] using h
  have h1 : reflect 2 (1 : R[X]) = X ^ 2 := by
    simpa only [C_1, one_mul] using (reflect_C (1 : R) 2)
  have hX : reflect 2 (C a * X) = C a * X := by
    simpa only [show revAt 2 1 = 1 from rfl, pow_one] using
      (reflect_C_mul_X_pow 2 1 (c := a))
  have hX2 : reflect 2 (C b * X ^ 2) = C b := by
    rw [reflect_C_mul_X_pow, show revAt 2 2 = 0 from rfl, pow_zero, mul_one]
  have h' := congrArg (reflect 2) hr
  simpa only [reflect_reflect, reflect_add, reflect_sub, h1, hX, hX2] using h'

/-- A geometric characteristic polynomial gives both the arithmetic characteristic polynomial
on the scalar-extended dual and the geometric trace on the original scalar-extended matrix. -/
theorem arithmetic_charpoly_and_geometric_trace {G R S : Type*} [Group G]
    [CommRing R] [Nontrivial R] [CommRing S] (φ : R →+* S) (ρ : G →* GL (Fin 2) R)
    (σ : G) (a b : R)
    (h : (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) R).charpoly = X ^ 2 - C a * X + C b) :
    ((dual ρ σ : Matrix (Fin 2) (Fin 2) R).map φ).charpoly =
        X ^ 2 - C (φ a) * X + C (φ b) ∧
      φ (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) R).trace = φ a := by
  constructor
  · rw [charpoly_map, charpoly_dual, h]
    simp
  · congr 1
    rw [trace_eq_neg_charpoly_coeff, h]
    simp [Polynomial.coeff_C]

end ModularFrobeniusDual
