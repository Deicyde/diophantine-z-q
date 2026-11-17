/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt (git blob 00f44d33ca0852585b303fd3b29359026887b1c6, sha256 9fc71c9c5ee94435bae687cdd185de946a5474b1b58fd5de5c0d39a66c8bda1d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ₁ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁ : φ₁ ∈ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ)
    (hφN : φ ∈ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (hφt : φ ∈ archCutSubmodule F tys)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ y - ∑ h ∈ s, l h * φ₁ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε) :
    φ ∈ V := by

  have hcovP : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) :=
    hcov.mono (Set.iUnion₂_mono fun x _ => Set.image_mono (centreCutSiegelSetAmple_subset c u d₁ d₂ κ))

  obtain ⟨σ, hσ⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V hV
  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F

  set X : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys with hXdef
  haveI hfin : FiniteDimensional ℂ ↥X :=
    AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent F c u d₁ d₂ T hd hcovP ξ N hN tys V hV

  have hXle : X ≤ cuspMemberSubmodule F Φ₀ ξ :=
    le_trans (le_trans inf_le_left (le_trans inf_le_left hV.1.le))
      (AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcovP ξ hΦ₀)

  set L : ↥X →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hXle) with hLdef
  haveI : FiniteDimensional ℂ ↥(LinearMap.range L) := LinearMap.finiteDimensional_range L
  have hclosed : IsClosed ((LinearMap.range L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
      Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := (LinearMap.range L).closed_of_finiteDimensional

  obtain ⟨hφm, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
      F c u d₁ d₂ κ T hd hκ hc hd₁ hcov ξ σ hσ hΦ₀ N hN tys V hV.1 φ₁ hφ₁ φ hφ hφc hφN hφt happrox 1 one_pos
  have hmem : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ ∈ (LinearMap.range L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [← SetLike.mem_coe, ← hclosed.closure_eq, Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨hφm', x, hx, hxm, hlt⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
        F c u d₁ d₂ κ T hd hκ hc hd₁ hcov ξ σ hσ hΦ₀ N hN tys V hV.1 φ₁ hφ₁ φ hφ hφc hφN hφt happrox δ hδ
    refine ⟨L ⟨x, hx⟩, LinearMap.mem_range_self L _, ?_⟩
    rw [dist_eq_norm]
    exact hlt
  obtain ⟨⟨x, hx⟩, hLx⟩ := hmem

  have hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ := hXle hx
  have hsub : φ - x ∈ contMemberSubmodule F Φ₀ ξ :=
    ⟨(memberSubmodule F Φ₀ ξ).sub_mem hφm.1.1.1 hxm.1.1.1, hφc.sub hxm.2⟩
  have h0 : toCarrier F hΦ₀ σ ξ ⟨φ - x, hsub.1⟩ = 0 := by
    have e1 : (⟨φ - x, hsub.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨φ, hφm.1.1.1⟩ - ⟨x, hxm.1.1.1⟩ := rfl
    have e2 : (L ⟨x, hx⟩ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨x, hxm.1.1.1⟩ := rfl
    have e3 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨φ, hφm.1.1.1⟩ := rfl
    rw [e1, map_sub, ← e2, ← e3, hLx, sub_self]
  have hφx : φ - x = 0 := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (φ - x) hsub h0
  rw [sub_eq_zero] at hφx
  rw [hφx]
  exact hx.1.1
