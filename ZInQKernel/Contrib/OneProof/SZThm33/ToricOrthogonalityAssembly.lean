import ZInQKernel.Contrib.OneProof.DirectWeil.InertiaCoisotropy

noncomputable section

open TensorProduct
open scoped CategoryTheory.MonObj

namespace SZRaynaud

section BaseChange

variable {R F U W T : Type*} [CommRing R] [Field F] [Algebra R F]
  [AddCommGroup U] [AddCommGroup W] [AddCommGroup T]
  [Module R U] [Module R W] [Module R T]

/-- Vanishing on two lattices implies orthogonality of their rational images. -/
theorem range_baseChange_le_orthogonal_of_tmul
    (B : LinearMap.BilinForm F (F ⊗[R] T)) (i : U →ₗ[R] T) (j : W →ₗ[R] T)
    (h : ∀ (x : U) (y : W), B (1 ⊗ₜ[R] i x) (1 ⊗ₜ[R] j y) = 0) :
    (j.baseChange F).range ≤ B.orthogonal (i.baseChange F).range := by
  rintro _ ⟨w, rfl⟩
  apply (B.mem_orthogonal_iff).mpr
  rintro _ ⟨u, rfl⟩
  have hs (a : F) (t : T) : a ⊗ₜ[R] t = a • ((1 : F) ⊗ₜ[R] t) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  induction w using TensorProduct.inductionOn with
  | tmul b y =>
    induction u using TensorProduct.inductionOn with
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hs a, hs b]
      simp only [map_smul, LinearMap.smul_apply, h, smul_zero]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end BaseChange

open PkgI3 PkgI3.AbVar ReductSplit

/-- With the fixed and toric ranks, integral orthogonality implies exactly
the inertia condition in the forward implication of the criterion. -/
theorem levelTwo_of_integral_toric_orthogonality
    {K Ω U W : Type} [Field K] [Field Ω] [Algebra K Ω]
    (A : AbVar K) (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime]
    [FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)]
    [AddCommGroup U] [AddCommGroup W] [Module ℤ_[ℓ] U] [Module ℤ_[ℓ] W]
    (i : U →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ) (j : W →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ)
    (hI : (i.baseChange ℚ_[ℓ]).range = inertiaFixedSpace A w ℓ)
    (hJ : (j.baseChange ℚ_[ℓ]).range ≤ (i.baseChange ℚ_[ℓ]).range)
    (hDim : Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) ≤
      Module.finrank ℚ_[ℓ] (i.baseChange ℚ_[ℓ]).range + Module.finrank ℚ_[ℓ] (j.baseChange ℚ_[ℓ]).range)
    (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)) (hB : B.Nondegenerate)
    (hρ : ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ x y : VΩ A Ω ℓ,
      B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y)
    (hO : ∀ (x : U) (y : W), B (1 ⊗ₜ[ℤ_[ℓ]] i x) (1 ⊗ₜ[ℤ_[ℓ]] j y) = 0) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  apply (coisotropic_iff_levelTwo A w ℓ B hB hρ).mp
  rw [← hI]
  exact coisotropic_of_toric_rank B hB _ _ hJ (range_baseChange_le_orthogonal_of_tmul B i j hO) hDim

end SZRaynaud
