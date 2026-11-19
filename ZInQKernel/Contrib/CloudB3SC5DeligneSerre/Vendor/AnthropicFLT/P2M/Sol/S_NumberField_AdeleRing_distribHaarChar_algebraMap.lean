/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdeleRing_distribHaarChar_algebraMap (git blob cb4eb0294cc53be2ff7dda4e9b4e8c6241b67914, sha256 27337288a0d6782654129b0870179f7efaa565e738c57e8d7927a7420655ec3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdeleRing_distribHaarChar_algebraMap

set_option autoImplicit false

open NumberField MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace FltWs24
namespace AdelicModulusOneChar

theorem addHaarScalarFactor_eq_one_of_integral_eq {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsAddLeftInvariant]
    (h : ∀ f : G → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ' = ∫ x, f x ∂μ) :
    addHaarScalarFactor μ' μ = 1 := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have hpos : 0 < ∫ x, f x ∂μ :=
    f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero
  have h1 := integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport μ' μ f_cont f_comp
  rw [h f f_cont f_comp, integral_smul_nnreal_measure] at h1
  have h2 : (addHaarScalarFactor μ' μ : ℝ) = 1 := by
    rw [NNReal.smul_def, smul_eq_mul] at h1
    field_simp at h1
    linarith [h1, hpos]
  exact_mod_cast h2

variable (F : Type) [Field F] [NumberField F]



theorem distribHaarChar_algebraMap_impl [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := by
  set u : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a with hu

  let μ : Measure (AdeleRing (𝓞 F) F) := Measure.addHaar
  haveI : μ.Regular := by
    show (Measure.addHaar : Measure (AdeleRing (𝓞 F) F)).Regular
    unfold Measure.addHaar; infer_instance

  have hmp : MeasurePreserving (fun x => (u : (AdeleRing (𝓞 F) F)) * x) μ μ :=
    NumberField.AdeleRing.measurePreserving_mul_algebraMap F μ (a : F) a.ne_zero

  have hsf : addHaarScalarFactor (DomMulAct.mk u⁻¹ • μ : Measure (AdeleRing (𝓞 F) F)) μ = 1 := by
    refine addHaarScalarFactor_eq_one_of_integral_eq _ μ fun f hf hfc => ?_
    rw [integral_domSMul]
    simp only [Equiv.symm_apply_apply, inv_inv]
    have hme : MeasurableEmbedding (fun x => (u : (AdeleRing (𝓞 F) F)) * x) :=
      (ContinuousAddEquiv.mulLeft u).toHomeomorph.measurableEmbedding
    exact hmp.integral_comp hme f
  have hinv : distribHaarChar (AdeleRing (𝓞 F) F) u⁻¹ = 1 := by
    rw [← addHaarScalarFactor_smul_eq_distribHaarChar μ u⁻¹]
    exact hsf
  rwa [map_inv (distribHaarChar (AdeleRing (𝓞 F) F)) u, inv_eq_one] at hinv

end FltWs24.AdelicModulusOneChar

open NumberField

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 :=
  FltWs24.AdelicModulusOneChar.distribHaarChar_algebraMap_impl F a
