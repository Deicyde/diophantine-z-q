import ZInQKernel.Contrib.OneProof.SZThm33.IntermediateTate
import ZInQKernel.Contrib.OneProof.DirectWeil.AmbientWeilPairing
import ZInQKernel.Contrib.OneProof.StrictHenselizationPair
import ZInQKernel.Contrib.AbVarBC.Dim

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open ReductSplit (TΩ)

namespace SZRaynaud

open PicDict.DirectPairing (polarization tateEquiv tatePairing)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (w : ValuationSubring Ω)

/-- An inertia element regarded as acting over the fraction field of the
strict henselization in the chosen algebraic closure. -/
def overInertiaField (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) : Ω ≃ₐ[(GapSHPair.inertiaField (K := K) w)] Ω :=
  { σ.toRingEquiv with
    commutes' := fun t => GapSHPair.inertia_fixes w hσ t.property }

theorem overInertiaField_restrictScalars (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    (overInertiaField w σ hσ).restrictScalars K = σ := AlgEquiv.ext fun _ => rfl

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : PkgI3.AbVar K)

include w in
theorem isAlgClosure_over_inertiaField : IsAlgClosure (GapSHPair.inertiaField (K := K) w) Ω :=
  ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) (GapSHPair.inertiaField (K := K) w)⟩

/-- A polarization over the inertia field gives a form on the original
rational Tate space. Both the inertia isometry and the original integral
pairing of the chosen line are retained. -/
theorem exists_strictWeilForm (L : (A.baseChange (GapSHPair.inertiaField (K := K) w)).X.left.Pic)
    (e : AlgebraicClosure (GapSHPair.inertiaField (K := K) w) ≃ₐ[(GapSHPair.inertiaField (K := K) w)] Ω)
    (hℓ : (ℓ : (GapSHPair.inertiaField (K := K) w)) ≠ 0) (hu : IsUnit (ℓ : w))
    (hL : {x : (A.baseChange (GapSHPair.inertiaField (K := K) w)).Pt (AlgebraicClosure (GapSHPair.inertiaField (K := K) w)) |
      polarization (A.baseChange (GapSHPair.inertiaField (K := K) w)) L x = 1}.Finite)
    (g : ℕ) (hg : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)),
      Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      (∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ x y : VΩ A Ω ℓ,
        B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y) ∧
      ∀ x y : TΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) Ω ℓ,
        B (1 ⊗ₜ[ℤ_[ℓ]] intermediateTateEquiv A (GapSHPair.inertiaField (K := K) w) ℓ x)
          (1 ⊗ₜ[ℤ_[ℓ]] intermediateTateEquiv A (GapSHPair.inertiaField (K := K) w) ℓ y) = 0 ↔
          tatePairing (A.baseChange (GapSHPair.inertiaField (K := K) w)) L hℓ ((tateEquiv (A.baseChange (GapSHPair.inertiaField (K := K) w)) e).symm x)
            ((tateEquiv (A.baseChange (GapSHPair.inertiaField (K := K) w)) e).symm y) = 0 := by
  obtain ⟨hfin, C, hdim, hC, hAlt, hGal, hZero⟩ := exists_ambientWeilForm_of_finite_kernel
    (A.baseChange (GapSHPair.inertiaField (K := K) w)) L e hℓ hL g ((A.dim_baseChange (GapSHPair.inertiaField (K := K) w)).trans hg)
  let f := intermediateRationalTateEquiv A (GapSHPair.inertiaField (K := K) w) ℓ
  let B := LinearMap.BilinForm.congr f C
  refine ⟨Module.Finite.of_surjective f.toLinearMap f.surjective, B,
    f.finrank_eq.symm.trans hdim, hC.congr f, fun x => hAlt (f.symm x), ?_, ?_⟩
  · intro σ hσ x y
    let τ := overInertiaField w σ hσ
    have hτ : PkgI2.IsInertia w τ := ReductSplit.isInertia_restrict (GapSHPair.inertiaField (K := K) w) w σ τ (fun _ => rfl) hσ
    have hres : τ.restrictScalars K = σ := overInertiaField_restrictScalars w σ hσ
    have eq (z : VΩ A Ω ℓ) : f.symm (galVΩ A ℓ σ z) = galVΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) ℓ τ (f.symm z) := by
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, intermediateRationalTateEquiv_action A (GapSHPair.inertiaField (K := K) w) ℓ τ,
        hres, LinearEquiv.apply_symm_apply]
    have : IsAlgClosure (GapSHPair.inertiaField (K := K) w) Ω := isAlgClosure_over_inertiaField w
    simp only [B, LinearMap.BilinForm.congr_apply, eq, hGal,
      cyclotomicCharacter_eq_one_of_inertia w hu τ hτ, Units.val_one, map_one, one_mul]
  · intro x y
    have ht (z : TΩ (A.baseChange (GapSHPair.inertiaField (K := K) w)) Ω ℓ) :
        f.symm (1 ⊗ₜ[ℤ_[ℓ]] intermediateTateEquiv A (GapSHPair.inertiaField (K := K) w) ℓ z) = 1 ⊗ₜ[ℤ_[ℓ]] z := by
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul]
    simpa only [B, LinearMap.BilinForm.congr_apply, ht] using hZero x y

end SZRaynaud
