import ZInQKernel.Contrib.OneProof.StrictHenselizationPair
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Points
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Imperfect
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
import ZInQKernel.Contrib.CMSerreTateSupport.InertiaBridgeV002

/-!
# The actual fixed field of inertia on separable scalars
-/

noncomputable section

open scoped Pointwise IntermediateField
open ZInQ.Contrib.CloudR2NOS.Valuation

namespace SZRaynaud

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (w : ValuationSubring Ω)

/-- Surjectivity of inertia restriction at the specified prolongation,
with no assumption on the residue field or characteristic. -/
theorem exists_inertia_at_prolongation
    (M : IntermediateField K Ω) (τ : M ≃ₐ[K] M)
    (hτ : PkgI2.IsInertia (w.comap (algebraMap M Ω)) τ) :
    ∃ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ ∧ ∀ x : M, σ x = τ x := by
  have : Normal K Ω := IsAlgClosure.normal K Ω
  have : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) ↥M⟩
  let v₀ := w.comap (algebraMap M Ω)
  obtain ⟨v, ρ, hv, hρ, hc⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq
      K (Ω := Ω) v₀ τ ((isInertia_iff_mem_inertiaSubgroupIn v₀ τ).mp hτ)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_comap_eq w v hv.symm
  let gK := g.restrictScalars K
  have hgK : gK • w = v := hg
  have hi : PkgI2.IsInertia (gK • w) ρ := by
    rw [hgK]
    exact (isInertia_iff_mem_inertiaSubgroupIn v ρ).mpr hρ
  refine ⟨gK⁻¹ * ρ * gK, isInertia_conj_of_isInertia_smul w gK hi, fun x => ?_⟩
  have hgx : gK x = x := g.commutes x
  have hginv : gK⁻¹ (τ x : Ω) = τ x := g.symm.commutes (τ x)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgx]
  exact (congrArg (fun z : Ω => gK⁻¹ z) (hc x)).trans hginv

/-- A separable scalar fixed by absolute inertia belongs to the project's
strict-henselization inertia field. -/
theorem mem_inertiaField_of_fixed_of_isSeparable (x : Ω) (hx : IsSeparable K x)
    (hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → σ x = x) :
    x ∈ GapSHPair.inertiaField (K := K) w := by
  let F := K⟮x⟯
  have : FiniteDimensional K F := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  have : Algebra.IsSeparable K F := (IntermediateField.isSeparable_adjoin_iff_isSeparable K Ω).mpr
    (fun y hy => by rwa [Set.mem_singleton_iff.mp hy])
  obtain ⟨M, hM, hle⟩ := GapSHPair.isFG_of F
  have hxm : x ∈ M := hle (IntermediateField.mem_adjoin_simple_self K x)
  refine ⟨M, hM, hxm, fun μ hμ => ?_⟩
  have : IsGalois K M := hM.2
  have : FiniteDimensional K M := hM.1
  let τ := μ.restrictNormal M
  let v₀ := w.comap (algebraMap M Ω)
  have hτ : PkgI2.IsInertia v₀ τ := by
    apply (ActualTameInertia.mem_inertiaGroup_iff_inertiaSubgroup v₀ τ).mp
    apply ActualTameInertia.mem_inertiaGroup_iff.mpr
    intro y hy
    rw [← ValuationSubring.mem_nonunits_iff, GapSHPair.nonunits_comap]
    rw [map_sub, AlgEquiv.restrictNormal_commutes]
    exact hμ (y : Ω) y.2 hy
  obtain ⟨σ, hσ, hc⟩ := exists_inertia_at_prolongation w M τ hτ
  have h := hc ⟨x, hxm⟩
  change σ x = ((τ ⟨x, hxm⟩ : M) : Ω) at h
  have H := AlgEquiv.restrictNormal_commutes μ M (⟨x, hxm⟩ : M)
  exact H.symm.trans (h.symm.trans (hfix σ hσ))

#print axioms exists_inertia_at_prolongation
#print axioms mem_inertiaField_of_fixed_of_isSeparable

end SZRaynaud
