import ZInQKernel.Contrib.OneProof.SZThm33
import ZInQKernel.Contrib.OneProof.SZThm33.RationalFixedTate

noncomputable section

open TensorProduct
open PkgI2 (IsInertia)
open ReductSplit
open scoped CategoryTheory.MonObj

namespace SZRaynaud

/-- The implication from semistability to square-zero inertia is the part
of the criterion used to obtain the manuscript's wild inertia statement. -/
theorem elliot_of_semistable_levelTwo
    (forward : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
      w.comap (algebraMap K Ω) = O → ∀ (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
        IsUnit (ℓ : O) → HasSemistableReductionSZ A O →
        ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, IsInertia w τ →
          ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x) :
    ElliotWildInertiaTrivial := by
  intro K _ _ O _ Ω _ _ _ w hw A hA ℓ _ hℓO σ hσ hwild t
  have hV := forward K O Ω w hw A ℓ hℓO hA σ hσ σ hσ ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t)
  have hT : galTΩ A ℓ σ (galTΩ A ℓ σ t - t) = galTΩ A ℓ σ t - t := by
    apply tate_one_tmul_injective
    change ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] _) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] _
    simpa only [galVΩ, LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub] using hV
  have hsquare : galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0 := by
    calc
      _ = galTΩ A ℓ σ (galTΩ A ℓ σ t - t) - (galTΩ A ℓ σ t - t) := by
        rw [map_sub]
        abel
      _ = 0 := sub_eq_zero.mpr hT
  apply Subtype.ext
  funext n
  let x : A.Pt Ω := Additive.toMul (t.1 n)
  have ht : t.1 n = Additive.ofMul x := rfl
  have hx : x ^ (ℓ ^ n) = 1 := pow_smul_tate t n
  have hu := unipSq_of_tate A ℓ σ t n x ht hsquare
  obtain ⟨N, hcop, hit⟩ := wildPeriodCoprime_proof K O Ω w hw A ℓ hℓO σ hσ hwild n x hx
  have hfix : A.galAct σ x = x :=
    PkgI2.fixed_of_unipSq_of_iterate (ObjBridge.toGrp A) σ x ℓ n N 1 (by rwa [pow_one]) hx hu
      (by rwa [pow_one])
  exact congrArg Additive.ofMul hfix

end SZRaynaud
