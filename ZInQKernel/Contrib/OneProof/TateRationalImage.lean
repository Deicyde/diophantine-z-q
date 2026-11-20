import ZInQKernel.Contrib.OneProof.TateStableImage
import Mathlib.RingTheory.Localization.BaseChange

/-! # Galois-invariant rational Tate subspaces are endomorphism images -/

noncomputable section

open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

namespace ZInQ.Contrib.TateFiniteApproximation

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Every vector in the rationalization of an integral ℓ-adic module has a
nonzero denominator. This includes modules with torsion. -/
private theorem exists_denominator {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] M) :
    ∃ (d : ℚ_[ℓ]), d ≠ 0 ∧ ∃ w : M, d • x = 1 ⊗ₜ[ℤ_[ℓ]] w := by
  obtain ⟨⟨w, s⟩, hs⟩ := IsLocalizedModule.surj (ℤ_[ℓ])⁰ (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] M 1) x
  refine ⟨algebraMap ℤ_[ℓ] ℚ_[ℓ] s.1,
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])).mpr (nonZeroDivisors.coe_ne_zero s),
    w, ?_⟩
  change (s.1 : ℤ_[ℓ]) • x = 1 ⊗ₜ[ℤ_[ℓ]] w at hs
  simpa only [IsScalarTower.algebraMap_smul] using hs

variable {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)

/-- Given the Gaudron–Rémond bound and stable height, every invariant subspace
of the rational Tate module is the image of an ℓ-adic combination of algebraic
endomorphisms after extension of scalars. -/
theorem exists_endomorphism_with_rational_range
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height)
    (U : Submodule ℚ_[ℓ] (A.V ℓ))
    (hU : ∀ (σ : Field.absoluteGaloisGroup K) (v : A.V ℓ), v ∈ U → A.galRep ℓ σ v ∈ U) :
    ∃ ξ : ℤ_[ℓ] ⊗[ℤ] End A, LinearMap.range ((tateHomZl ℓ A A ξ).baseChange ℚ_[ℓ]) = U := by
  let i := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let W := (U.restrictScalars ℤ_[ℓ]).comap i
  have hW (σ : Field.absoluteGaloisGroup K) (w : A.T ℓ) (hw : w ∈ W) : A.galT σ w ∈ W := by
    exact hU σ (i w) hw
  obtain ⟨N, hN, h⟩ := exists_uniform_endomorphism_for_stable_submodules A hGR g height hdim hheight
  obtain ⟨ξ, hu, hWim⟩ := h ℓ W hW
  let u := tateHomZl ℓ A A ξ
  let v := u.baseChange ℚ_[ℓ]
  refine ⟨ξ, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨d, hd, w, he⟩ := exists_denominator (ℓ := ℓ) (M := A.T ℓ) x
    apply (U.smul_mem_iff hd).mp
    change d • v x ∈ U
    rw [← map_smul, he]
    exact hu ⟨w, rfl⟩
  · intro x hx
    obtain ⟨d, hd, w, he⟩ := exists_denominator (ℓ := ℓ) (M := A.T ℓ) x
    have hw : w ∈ W := by
      change 1 ⊗ₜ[ℤ_[ℓ]] w ∈ U
      rw [← he]
      exact U.smul_mem _ hx
    obtain ⟨y, hy⟩ := hWim w hw
    have hN' : (N : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    apply ((LinearMap.range v).smul_mem_iff hd).mp
    apply ((LinearMap.range v).smul_mem_iff hN').mp
    rw [he]
    refine ⟨i y, ?_⟩
    change i (u y) = (N : ℚ_[ℓ]) • i w
    rw [show u y = N • w from hy, map_nsmul, Nat.cast_smul_eq_nsmul]

end ZInQ.Contrib.TateFiniteApproximation
