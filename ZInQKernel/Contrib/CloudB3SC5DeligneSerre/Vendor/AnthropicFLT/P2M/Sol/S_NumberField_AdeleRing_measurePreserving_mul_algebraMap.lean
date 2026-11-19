/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdeleRing_measurePreserving_mul_algebraMap (git blob d6c0b3f0b75c9d387a70d7dafda159547346be92, sha256 6d6af3d2258100d84363d6a3dbb33db42725fa0cbf3b814f833c35750c7abf91).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdeleRing_measurePreserving_mul_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace FltWs24
namespace AdelicModulusOne

variable (F : Type) [Field F] [NumberField F]



noncomputable def principalUnit (a : F) (ha : a ≠ 0) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →+* (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 a ha)

theorem mul_eq_coe_mulLeft (a : F) (ha : a ≠ 0) :
    (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) = ⇑(ContinuousAddEquiv.mulLeft (principalUnit F a ha)) :=
  rfl

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  refine Function.Surjective.countable
    (f := fun k : F => (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) ?_
  rintro ⟨x, k, rfl⟩
  exact ⟨k, rfl⟩

theorem addHaarScalarFactor_map_mulLeft [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0)
    (hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ) :
    (μ.map (ContinuousAddEquiv.mulLeft (principalUnit F a ha))).addHaarScalarFactor μ = 1 := by
  have hm : ‹MeasurableSpace (AdeleRing (𝓞 F) F)› = AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := AdelicHaar.adeleBorel (𝓞 F) F
  set e : (AdeleRing (𝓞 F) F) ≃ₜ+ (AdeleRing (𝓞 F) F) := ContinuousAddEquiv.mulLeft (principalUnit F a ha) with he
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  have hcl : IsCompact (closure (AdelicBox.adelicBox F)) := hC.closure_of_subset hBC
  have key := measure_isAddInvariant_eq_smul_of_isCompact_closure (μ.map e) μ hcl
  have hme : Measurable (⇑e) := e.continuous.measurable
  rw [Measure.map_apply hme (AdelicBox.measurableSet_adelicBox F)] at key
  haveI := countable_principalSubgroup F
  haveI : MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) :=
    ⟨fun c => measurable_const_add (c : (AdeleRing (𝓞 F) F))⟩
  haveI : VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : (AdeleRing (𝓞 F) F)) s⟩
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      (⇑e ⁻¹' AdelicBox.adelicBox F) μ := by
    rw [← mul_eq_coe_mulLeft F a ha]; exact hFD
  have hμeq : μ (⇑e ⁻¹' AdelicBox.adelicBox F) = μ (AdelicBox.adelicBox F) :=
    hFD'.measure_eq (AdelicBox.isAddFundamentalDomain_adelicBox F μ)
  rw [hμeq, ENNReal.smul_def, smul_eq_mul] at key
  have h0 : μ (AdelicBox.adelicBox F) ≠ 0 := (AdelicBox.measure_adelicBox_pos F μ).ne'
  have htop : μ (AdelicBox.adelicBox F) ≠ ⊤ := (AdelicBox.measure_adelicBox_lt_top F μ).ne
  have h1 : ((μ.map e).addHaarScalarFactor μ : ℝ≥0∞) = 1 := by
    rw [← ENNReal.mul_left_inj h0 htop, one_mul]; exact key.symm
  exact_mod_cast h1

theorem measurePreserving_mul [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular] (a : F) (ha : a ≠ 0)
    (hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ) :
    MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ := by
  have h1 := addHaarScalarFactor_map_mulLeft F μ a ha hFD
  rw [mul_eq_coe_mulLeft F a ha]
  set e : (AdeleRing (𝓞 F) F) ≃ₜ+ (AdeleRing (𝓞 F) F) := ContinuousAddEquiv.mulLeft (principalUnit F a ha) with he
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (μ.map e).Regular := Regular.map e.toHomeomorph
  have huniq := isAddLeftInvariant_eq_smul_of_regular (μ.map e) μ
  rw [h1, one_smul] at huniq
  exact ⟨e.continuous.measurable, huniq⟩

end FltWs24.AdelicModulusOne

open NumberField

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ :=
  FltWs24.AdelicModulusOne.measurePreserving_mul F μ a ha
    (NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F μ a ha)
