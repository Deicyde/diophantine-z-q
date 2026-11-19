/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain (git blob 7822b060d8a88a9ab16c007ee9da0a236ddeadda, sha256 b20d98af380db296953cb58a0f799a1df619a2eb9e48dce3fe0afe5efd14fcf8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_SiegelVolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory NumberField.SiegelVolume

open scoped ENNReal NNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace SlabFDFinite

variable (K : Type) [Field K] [NumberField K]




scoped instance instCountableNumberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Function.Injective.countable (f := fun u : Mˣ => (u : M)) Units.val_injective

scoped instance instCountableMatrix : Countable (Matrix (Fin 2) (Fin 2) K) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → K))

scoped instance instCountableGL : Countable (GL (Fin 2) K) := instCountableUnits

scoped instance instCountableRange : Countable (globalPoints (𝓞 K) K).range :=
  (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem measure_image_mul_right_centreCutSiegelSet_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ}
    (hd₁ : 0 < d₁) (d₂ : ℝ) (x : (AdelicGL2 (𝓞 K) K)) :
    (adelicGLHaar (Fin 2) (𝓞 K) K) ((· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [Set.image_mul_right, ← Measure.map_apply (measurable_mul_const x⁻¹)
    (measurableSet_centreCutSiegelSet c u d₁ d₂)]
  exact measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

theorem measure_biUnion_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    (adelicGLHaar (Fin 2) (𝓞 K) K) (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  refine (measure_biUnion_finset_le T _).trans_lt ?_
  exact ENNReal.sum_lt_top.mpr fun x _ => measure_image_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x

end SlabFDFinite
open scoped _root_.P2MW.S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain.SlabFDFinite

open SlabFDFinite in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Φ₀ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) < ⊤ := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab_def
  have hslab : MeasurableSet slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  set Γ := (globalPoints (𝓞 K) K).range with hΓ
  set ν := μ.restrict slab with hν

  obtain ⟨T, c, hc, u, hcovall⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hcovall 1 2 two_pos (by norm_num)
  obtain ⟨T', hT'⟩ := exists_finset_slab_covering_of_coversModCentre K c u 1 2 T (by norm_num) hcov α β hα
  set D' : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T', (· * x) '' centreCutSiegelSet K c u 1 2 with hD'
  have hD'fin : μ D' < ⊤ := measure_biUnion_lt_top K hc u one_pos 2 T'

  have hslab_smul : ∀ (γ : Γ) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ slab ↔ x ∈ slab := by
    rintro ⟨_, γ, rfl⟩ x
    show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x))
        ∈ Set.Icc α β ↔ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

  haveI : MeasurableConstSMul Γ (AdelicGL2 (𝓞 K) K) :=
    ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩
  haveI : SMulInvariantMeasure Γ (AdelicGL2 (𝓞 K) K) ν := by
    refine ⟨fun γ s hs => ?_⟩
    have hpre : MeasurableSet ((fun x => γ • x) ⁻¹' s) := hs.preimage (measurable_const_smul γ)
    rw [hν, Measure.restrict_apply hpre, Measure.restrict_apply hs]
    have : (fun x => γ • x) ⁻¹' s ∩ slab = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right fun _ => (hslab_smul γ x).symm
    rw [this, measure_preimage_mul]

  have hcover : Φ₀ ∩ slab ⊆ ⋃ γ : Γ, γ • D' := by
    rintro g ⟨-, hg⟩
    obtain ⟨γ, hγ⟩ := hT' g hg
    refine Set.mem_iUnion.2 ⟨(⟨globalPoints (𝓞 K) K γ, γ, rfl⟩ : Γ)⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  calc μ (Φ₀ ∩ slab)
      ≤ μ ((⋃ γ : Γ, γ • D') ∩ Φ₀ ∩ slab) := measure_mono fun g hg =>
          ⟨⟨hcover hg, hg.1⟩, hg.2⟩
    _ = ν ((⋃ γ : Γ, γ • D') ∩ Φ₀) := (Measure.restrict_apply' hslab).symm
    _ = ν (⋃ γ : Γ, γ • D' ∩ Φ₀) := by rw [Set.iUnion_inter]
    _ ≤ ∑' γ : Γ, ν (γ • D' ∩ Φ₀) := measure_iUnion_le _
    _ = ν D' := (hΦ₀.measure_eq_tsum D').symm
    _ ≤ μ D' := Measure.restrict_le_self _
    _ < ⊤ := hD'fin
