import NativeTateCongruenceMatrices
import AdicImageSeparationSeparated

/-!
# Original torsion kernels in matrix congruence kernels

The finite matrix representation is built from the original Galois
representation on compatible Tate points. Fixing the original torsion
points at a level implies identity in the actual matrix reduction.
-/

noncomputable section
set_option autoImplicit false

namespace NativeTateCongruence

open CategoryTheory AlgebraicGeometry MonObj Matrix

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Actual finite torsion fixedness gives actual matrix congruence,
using the constructed shift quotient of the original Tate module. -/
theorem level_identity_of_original_points_fixed (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime]
    (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))))
    (σ : Ω ≃ₐ[K] Ω) (n : ℕ)
    (hfix : ∀ x : A.Pt Ω, x ^ (ell ^ (n + 1)) = 1 → A.galAct σ x = x) :
    IntegralCongruence.level ell n (originalTateMatrix A ell b σ) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  let f := originalTateRep (Ω := Ω) A ell σ
  let t : PkgI3.Tate.T ell (Additive (A.Pt Ω)) := f (b j) - b j
  have ht : t.1 (n + 1) = 0 := by
    change Additive.ofMul (A.galAct σ (Additive.toMul ((b j).1 (n + 1)))) - (b j).1 (n + 1) = 0
    rw [hfix _ (PkgI3.Tate.pow_smul_eq_zero (b j).2 (n + 1))]
    exact sub_self _
  obtain ⟨s, hs⟩ := (projection_zero_iff_divisible t (n + 1)).mp ht
  have hz : PadicInt.toZModPow (n + 1) (b.repr t i) = 0 := by
    rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    simp [← Nat.cast_pow, ZMod.natCast_self]
  have he : b.repr t i = (originalTateMatrix A ell b σ).val i j - (1 : Matrix d d ℤ_[ell]) i j := by
    rw [original_matrix_entry]
    simp [t, f, map_sub, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [he, map_sub] at hz
  apply sub_eq_zero.mp
  simpa [IntegralCongruence.level, Matrix.one_apply] using hz

/-- Matrix equality is equality of the original Tate operators. -/
theorem original_matrix_eq_iff (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
    (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))))
    (σ τ : Ω ≃ₐ[K] Ω) :
    originalTateMatrix A ell b σ = originalTateMatrix A ell b τ ↔
      originalTateRep A ell σ = originalTateRep A ell τ := by
  constructor
  · intro h
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val h
  · intro h
    apply Units.ext
    change (LinearMap.toMatrixAlgEquiv b) (originalTateRep A ell σ) =
      (LinearMap.toMatrixAlgEquiv b) (originalTateRep A ell τ)
    rw [h]

#check level_identity_of_original_points_fixed
#print axioms level_identity_of_original_points_fixed
#print axioms original_matrix_eq_iff

end NativeTateCongruence
