import ZInQKernel.Contrib.OneProof.DirectWeil.AmbientWeilPairing

noncomputable section

open HDec.InertiaHoms ReductSplit PicDict.DirectPairing
open scoped CategoryTheory.MonObj

namespace SZRaynaud

variable {K E Ω : Type} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
  (e : E ≃ₐ[K] Ω) (w : ValuationSubring Ω)

/-- Transport of inertia to the valuation ring induced by a change of algebraic closure. -/
theorem isInertia_comap_closureEquiv (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    PkgI2.IsInertia (w.comap (e : E →+* Ω)) (e.trans (σ.trans e.symm)) := by
  rw [PkgI2.IsInertia, isInertia_iff] at hσ ⊢
  exact inertia_transport e.toRingEquiv w σ.toRingEquiv hσ.1 hσ.2

theorem comap_closureEquiv_eq (O : ValuationSubring K)
    (hw : w.comap (algebraMap K Ω) = O) :
    (w.comap (e : E →+* Ω)).comap (algebraMap K E) = O := by
  ext x
  rw [← hw]
  change e (algebraMap K E x) ∈ w ↔ algebraMap K Ω x ∈ w
  rw [e.commutes]

variable (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The rational Tate inertia criterion is independent of the chosen algebraic closure. -/
theorem levelTwo_of_closureEquiv
    (h : ∀ σ : E ≃ₐ[K] E, PkgI2.IsInertia (w.comap (e : E →+* Ω)) σ → ∀ τ : E ≃ₐ[K] E, PkgI2.IsInertia (w.comap (e : E →+* Ω)) τ →
      ∀ x : VΩ A E ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  let f := LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (tateEquiv A e (ℓ := ℓ))
  have equivariance (σ : Ω ≃ₐ[K] Ω) (x : VΩ A E ℓ) :
      f (galVΩ A ℓ (e.trans (σ.trans e.symm)) x) = galVΩ A ℓ σ (f x) := by
    let g := (tateEquiv A e (ℓ := ℓ)).toLinearMap
    have h₀ : g.comp (galTΩ A ℓ (e.trans (σ.trans e.symm))) = (galTΩ A ℓ σ).comp g := by
      ext y : 1
      exact tateEquiv_gal A e σ y
    have h₁ := congrArg (LinearMap.baseChange ℚ_[ℓ]) h₀
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h₁
    exact LinearMap.congr_fun h₁ x
  intro σ hσ τ hτ x
  obtain ⟨y, rfl⟩ := f.surjective x
  have eq := h _ (isInertia_comap_closureEquiv e w σ hσ) _ (isInertia_comap_closureEquiv e w τ hτ) y
  simpa only [equivariance, map_sub] using congrArg f eq

end SZRaynaud
