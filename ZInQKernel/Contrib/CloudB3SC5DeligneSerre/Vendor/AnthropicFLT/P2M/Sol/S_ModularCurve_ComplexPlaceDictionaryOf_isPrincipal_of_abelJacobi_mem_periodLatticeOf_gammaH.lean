/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH (git blob c03bfb2d4f789a812551491ae9d584f3ba0390ef, sha256 0af5b5f15d11785c801d5a59ed5750e426e014568ba3b1384062b811104dbd7d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve
end P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve
namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH
end P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve
export _root_.ModularCurve (realizeOf realizeOf_def ComplexPlaceDictionaryOf coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange ComplexPlaceDictionary translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC intFormRatiosC_subset periodAlongOf periodLatticeOf period jqModC map_jqModC ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH exists_realizeOf_eventuallyEq_of_meromorphic_gammaH ord_eq_zero_of_not_mem_of_realizeOf_tendsto ComplexPlaceDictionaryOf.exists_pt_eq_of_mem jqModC_mem_intFormRatiosC)
namespace AbelConverseGlueH
open _root_.ModularCurve

theorem realizeOf_zero {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    ModularCurve.realizeOf Γ 0 τ = 0 := by
  rw [ModularCurve.realizeOf_def]
  split_ifs with H
  · obtain ⟨-, hx⟩ := H.choose_spec
    rw [zero_mul] at hx
    have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
      exact AddSubgroup.mem_zmultiples _
    have hg : H.choose.2.1 = 0 := by
      rw [← ModularForm.qExpansion_eq_zero_iff one_pos h1]
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
      simpa using hx.symm
    simp [hg]
  · rfl

theorem isBigO_of_tendsto {F : ℍ → ℂ}
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im) := by
  intro σ
  obtain ⟨L, -, hL⟩ := hcusp σ
  refine ⟨0, ?_⟩
  simpa only [zero_mul, Real.exp_zero] using hL.isBigO_one ℝ

theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.jqModC ℂ ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  have h := ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
    (ModularCurve.intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
  have e : ModularCurve.coeffEmb ℂ (ModularCurve.jqModC ℚ) = ModularCurve.jqModC ℂ :=
    ModularCurve.map_jqModC (algebraMap ℚ ℂ)
  rwa [e] at h

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem isCongruenceSubgroup_gammaH :
    CongruenceSubgroup.IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
    (CongruenceSubgroup.Gamma1_is_congruence M)

end ModularCurve.AbelConverseGlueH
open scoped _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH
open scoped _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH

open UpperHalfPlane ModularCurve.AbelConverseGlueH in
open scoped MatrixGroups Topology in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H

  obtain ⟨F, hmer, hinv, hcusp, hord⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
      M H D c hdeg hΛ

  obtain ⟨x₀, hx₀, hFx⟩ := ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH M H F hmer hinv
    (isBigO_of_tendsto hcusp)
  set x : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H) := ⟨x₀, hx₀⟩
  have hFx' : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) (x : LaurentSeries ℂ) (ofComplex z) := hFx

  have hx0 : x ≠ 0 := by
    intro h0
    have hz : (x : LaurentSeries ℂ) = 0 := by simp [h0]
    have h2 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (UpperHalfPlane.I : ℂ) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [hFx' UpperHalfPlane.I] with z hz'
      rw [hz', hz, realizeOf_zero hT]
    have h1 := hord UpperHalfPlane.I
    rw [h2] at h1
    exact WithTop.top_ne_coe h1

  set y : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H) :=
    ⟨ModularCurve.jqModC ℂ, jqModC_mem_laurentBaseChange (CohCarrier.GammaH M H)⟩ with hy_def
  have hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := rfl
  refine ⟨x, hx0, fun v => ?_⟩
  by_cases hv : v ∈ Set.range D.pt
  ·
    obtain ⟨τ, rfl⟩ := hv
    have h1 := D.meromorphicOrderAt_realizeOf τ x hx0
    rw [← meromorphicOrderAt_congr (hFx' τ), hord τ] at h1
    have hr : (D.ramification τ : ℤ) ≠ 0 := by exact_mod_cast (D.ramification_pos τ).ne'
    exact mul_left_cancel₀ hr (WithTop.coe_injective h1)
  ·
    rw [Finsupp.mapDomain_notin_range _ _ hv]
    refine (ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto (CohCarrier.GammaH M H) hT
      (isCongruenceSubgroup_gammaH M H) (ModularCurve.xHFunctionField M H) rfl x F hFx' hcusp v y hy
      fun hj => hv ?_).symm
    obtain ⟨τ, hτ⟩ := ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem (CohCarrier.GammaH M H) hT
      (ModularCurve.xHFunctionField M H) rfl D v y hy hj
    exact ⟨τ, hτ⟩
