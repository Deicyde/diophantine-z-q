/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite (git blob b837d3000a7ffe919dc0548a2a6fc94a266a1e82, sha256 84dca87e297efa0faaf83d72d74d8e8555a69a7bdb1dd3a1a21eb26174d3a00c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_SiegelVolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightConv F φ f ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  classical

  have hψ : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf φ hφ
  have hcont : Continuous (rightConv F φ f) := hψ.2

  have hcut : rightConv F φ f ∈ archCutSubmodule F tys :=
    AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys φ hφ.2 f hf hft
  refine Submodule.subset_span ⟨fun g => ?_, hcont, tys, hcut⟩

  have hy : rightTranslate F g (rightConv F φ f) ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g (rightConv F φ f) hψ
  have hlx := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1.1.1
  have hlxy := (mem_memberSubmodule_iff' F Φ₀ ξ (rightTranslate F g (rightConv F φ f))).mp hy.1.1.1

  have hMemD : MemLp (rightTranslate F g (rightConv F φ f)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
    haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
      NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
    have hDclosed : IsClosed (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet T) fun x _ => ?_
      exact (Homeomorph.mulRight x).isClosed_image.mpr (isClosed_centreCutSiegelSet c u d₁ d₂)
    have hDfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
      refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
      have himg : (· * x) '' centreCutSiegelSet F c u d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c u d₁ d₂ := by
        ext g'; constructor
        · rintro ⟨h, hh, rfl⟩; simpa [mul_inv_cancel_right] using hh
        · intro hg; exact ⟨g' * x⁻¹, hg, by simp only [inv_mul_cancel_right]⟩
      rw [himg, ← Measure.map_apply (measurable_mul_const x⁻¹) (isClosed_centreCutSiegelSet c u d₁ d₂).measurableSet,
        map_mul_right_eq_self]
      exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top (F := F) (adelicGLHaar (Fin 2) (𝓞 F) F) hc u hd₁ d₂
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :=
      isFiniteMeasure_restrict.mpr hDfin.ne

    obtain ⟨C, hC⟩ :=
      AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
        F ξ f hf c u d₁ d₂ (T.image (· * g)) hc hd₁ α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    have hb := hC φ hlx.1 hφ.1.1.2 hφ.2 hlx.2
    refine MemLp.of_bound hy.2.aestronglyMeasurable
      (C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal)
      ((ae_restrict_mem hDclosed.measurableSet).mono fun y hyW => ?_)
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hyW
    have hmemg : s * x * g ∈ ⋃ x' ∈ T.image (· * g), (· * x') '' centreCutSiegelSet F c u d₁ d₂ :=
      Set.mem_iUnion₂.mpr ⟨x * g, Finset.mem_image_of_mem _ hx, s, hs, (mul_assoc s x g).symm⟩
    calc ‖rightTranslate F g (rightConv F φ f) (s * x)‖ = ‖rightConv F φ f (s * x * g)‖ := by
          rw [rightTranslate_apply]
      _ ≤ C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal := hb _ hmemg
  refine ⟨⟨?_, hy.1.1.2⟩, hy.1.2⟩
  exact (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightTranslate F g (rightConv F φ f))).mpr ⟨hlxy.1, hMemD⟩

end
