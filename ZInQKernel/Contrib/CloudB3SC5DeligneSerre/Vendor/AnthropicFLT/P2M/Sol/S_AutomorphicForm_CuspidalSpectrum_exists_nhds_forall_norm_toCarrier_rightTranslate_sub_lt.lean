/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt (git blob bccc6f269ace8b4adaf1d27a9a44816e222927ed, sha256 a396bfcc6d9ba7b0b4f27150e8c3a6164e8ee21dbe7ff1102d2dee7fa236839b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Topology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter

noncomputable section

namespace Ws48RoadP

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_enorm_rpow_two_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ memberSubmodule F Φ₀ ξ) :
    ∫⁻ g, ‖φ g‖ₑ ^ (2:ℝ) ∂(weightedMeasure F Φ₀ σ) = ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ ^ (2:ℝ) := by
  have hm := memLp_weightedMeasure_of_mem F hΦ₀ σ hφ
  have h1 : toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ = hm.toLp φ := rfl
  rw [h1, Lp.norm_toLp, ENNReal.ofReal_toReal hm.eLpNorm_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm.aestronglyMeasurable, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_enorm_sub_rpow_two_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ memberSubmodule F Φ₀ ξ) (hψ : ψ ∈ memberSubmodule F Φ₀ ξ) :
    ∫⁻ g, ‖φ g - ψ g‖ₑ ^ (2:ℝ) ∂(weightedMeasure F Φ₀ σ) =
      ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ - toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩‖ ^ (2:ℝ) := by
  have hsub : φ - ψ ∈ memberSubmodule F Φ₀ ξ := sub_mem hφ hψ
  have hdiff : toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ - toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ = toCarrier F hΦ₀ σ ξ ⟨φ - ψ, hsub⟩ := by
    rw [← map_sub]; rfl
  rw [hdiff, ← lintegral_enorm_rpow_two_eq hΦ₀ σ ξ (φ - ψ) hsub]
  rfl

theorem enorm_sub_rpow_two_le (a b : ℂ) :
    ‖a - b‖ₑ ^ (2:ℝ) ≤ 2 * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) := by
  calc ‖a - b‖ₑ ^ (2:ℝ) ≤ (‖a‖ₑ + ‖b‖ₑ) ^ (2:ℝ) := by gcongr; exact enorm_sub_le
    _ ≤ (2:ℝ≥0∞) ^ ((2:ℝ) - 1) * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
    _ = 2 * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) := by norm_num

theorem continuous_enorm_rpow_two {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f) :
    Continuous fun g => ‖f g‖ₑ ^ (2:ℝ) :=
  ENNReal.continuous_rpow_const.comp hf.enorm

end Ws48RoadP

open Ws48RoadP

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ contMemberSubmodule F Φ₀ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ y ∈ V, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ < ε := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set κ : Measure (AdelicGL2 (𝓞 F) F) := weightedMeasure F Φ₀ σ with hκ

  let N : AdelicGL2 (𝓞 F) F → ℝ := fun y => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)
  have hN : Continuous N := NumberField.TateGlobal.continuous_ideleNorm_det F
  have hNpos : ∀ y, 0 < N y := fun y => NumberField.TateGlobal.ideleNorm_pos _
  have hN1 : N 1 = 1 := by simp [N, NumberField.TateGlobal.ideleNorm]

  have key : ∀ y : AdelicGL2 (𝓞 F) F, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩‖ ≤ N y ^ (σ / 2) * ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ := by
    intro y
    obtain ⟨T, T', hT, -, -, hTn⟩ := exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y
    refine ⟨hT.mapsTo x hx, ?_⟩
    rw [← hT.comm x hx]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))
  choose hy hbound using key

  set c : ℝ := ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ with hc
  let Fy : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun y g => ‖x (g * y) - x g‖ₑ ^ (2:ℝ)
  let Gy : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℝ≥0∞ :=
    fun y g => 2 * (‖x (g * y)‖ₑ ^ (2:ℝ) + ‖x g‖ₑ ^ (2:ℝ))
  let glim : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => 2 * (‖x g‖ₑ ^ (2:ℝ) + ‖x g‖ₑ ^ (2:ℝ))
  have hxc : Continuous x := hx.2
  have hxyc : ∀ y, Continuous fun g => x (g * y) := fun y => hxc.comp (continuous_id.mul continuous_const)
  have hIx : ∫⁻ g, ‖x g‖ₑ ^ (2:ℝ) ∂κ = ENNReal.ofReal c ^ (2:ℝ) := lintegral_enorm_rpow_two_eq hΦ₀ σ ξ x hx.1
  have hIxy : ∀ y, ∫⁻ g, ‖x (g * y)‖ₑ ^ (2:ℝ) ∂κ ≤ ENNReal.ofReal (N y ^ (σ / 2) * c) ^ (2:ℝ) := by
    intro y
    have h := lintegral_enorm_rpow_two_eq hΦ₀ σ ξ (rightTranslate F y x) (hy y).1
    simp only [rightTranslate_apply] at h
    rw [h]
    gcongr
    exact hbound y
  have hmeas2 : ∀ y, Measurable fun g => ‖x (g * y)‖ₑ ^ (2:ℝ) := fun y => (continuous_enorm_rpow_two (hxyc y)).measurable
  have hmeas1 : Measurable fun g => ‖x g‖ₑ ^ (2:ℝ) := (continuous_enorm_rpow_two hxc).measurable
  have hGint : ∀ y, ∫⁻ g, Gy y g ∂κ = 2 * (∫⁻ g, ‖x (g * y)‖ₑ ^ (2:ℝ) ∂κ + ∫⁻ g, ‖x g‖ₑ ^ (2:ℝ) ∂κ) := by
    intro y
    simp only [Gy]
    rw [lintegral_const_mul _ ((hmeas2 y).fun_add hmeas1), lintegral_add_left (hmeas2 y)]
  have hglim : ∫⁻ g, glim g ∂κ = 2 * (ENNReal.ofReal c ^ (2:ℝ) + ENNReal.ofReal c ^ (2:ℝ)) := by
    simp only [glim]
    rw [lintegral_const_mul _ (hmeas1.fun_add hmeas1), lintegral_add_left hmeas1, hIx]

  have hlim0 : Tendsto (fun y => ∫⁻ g, Fy y g ∂κ) (𝓝 1) (𝓝 0) := by
    refine tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le Fy Gy glim ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y
      exact (continuous_enorm_rpow_two ((hxyc y).sub hxc)).measurable.aemeasurable
    · intro y
      exact (((hmeas2 y).add hmeas1).const_mul _).aemeasurable
    · intro y
      exact ae_of_all _ fun g => enorm_sub_rpow_two_le _ _
    · refine ae_of_all _ fun g => ?_
      have hc' : Continuous fun y => Fy y g :=
        continuous_enorm_rpow_two (f := fun y => x (g * y) - x g) ((hxc.comp (continuous_const_mul g)).sub continuous_const)
      have h0 : Fy 1 g = 0 := by
        simp only [Fy, mul_one, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos two_pos]
      convert hc'.tendsto 1 using 2
      exact h0.symm
    · refine ae_of_all _ fun g => ?_
      have hc' : Continuous fun y => Gy y g :=
        (ENNReal.continuous_const_mul ENNReal.ofNat_ne_top).comp
          ((continuous_enorm_rpow_two (f := fun y => x (g * y)) (hxc.comp (continuous_const_mul g))).add
            continuous_const)
      convert hc'.tendsto 1 using 2
      simp only [Gy, glim, mul_one]
    · rw [hglim]
      have h : ENNReal.ofReal c ^ (2:ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg two_pos.le ENNReal.ofReal_ne_top
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨h, h⟩)
    ·
      let B : AdelicGL2 (𝓞 F) F → ℝ≥0∞ :=
        fun y => 2 * (ENNReal.ofReal (N y ^ (σ / 2) * c) ^ (2:ℝ) + ENNReal.ofReal c ^ (2:ℝ))
      have hGB : ∀ y, ∫⁻ g, Gy y g ∂κ ≤ B y := by
        intro y
        rw [hGint y, hIx]
        simp only [B]
        gcongr
        exact hIxy y
      have hBc : Continuous B := by
        refine (ENNReal.continuous_const_mul ENNReal.ofNat_ne_top).comp ?_
        refine (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp ?_)).add continuous_const
        exact (hN.rpow_const fun y => Or.inl (hNpos y).ne').mul continuous_const
      have hB1 : B 1 = ∫⁻ g, glim g ∂κ := by
        rw [hglim]
        simp only [B, hN1, Real.one_rpow, one_mul]
      calc limsup (fun y => ∫⁻ g, Gy y g ∂κ) (𝓝 1) ≤ limsup B (𝓝 1) :=
            limsup_le_limsup (Eventually.of_forall hGB)
        _ = B 1 := (hBc.tendsto 1).limsup_eq
        _ = ∫⁻ g, glim g ∂κ := hB1

  have hε2 : (0:ℝ≥0∞) < ENNReal.ofReal ε ^ (2:ℝ) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hε) ENNReal.ofReal_ne_top
  refine ⟨_, hlim0 (Iio_mem_nhds hε2), fun y hyV => ⟨hy y, ?_⟩⟩
  have hlt : ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, (hy y).1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ ^ (2:ℝ)
      < ENNReal.ofReal ε ^ (2:ℝ) := by
    rw [← lintegral_enorm_sub_rpow_two_eq hΦ₀ σ ξ (rightTranslate F y x) x (hy y).1 hx.1]
    simpa only [rightTranslate_apply, Set.mem_preimage, Set.mem_Iio] using hyV
  exact not_le.1 fun h => (not_lt.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) two_pos.le)) hlt
