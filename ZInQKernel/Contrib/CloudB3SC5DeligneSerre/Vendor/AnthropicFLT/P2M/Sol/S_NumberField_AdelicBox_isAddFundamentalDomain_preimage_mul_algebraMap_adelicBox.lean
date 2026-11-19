/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox (git blob 2f96cfbed478c4a8de320f4e8652afbc9c26f11d, sha256 99d02d47c147c73ba7b898fd1b291e495edb5ea4c0486a5ae23fd7e9bcf48bae).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace FltWs24
namespace AdelicModulusOne

variable (F : Type) [Field F] [NumberField F]



theorem isAddFundamentalDomain_preimage_mul [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ := by
  have hm : ‹MeasurableSpace (AdeleRing (𝓞 F) F)› = AdelicHaar.adeleBorel (𝓞 F) F := BorelSpace.measurable_eq
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := AdelicHaar.adeleBorel (𝓞 F) F
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · exact ((AdelicBox.measurableSet_adelicBox F).preimage
      (measurable_const_mul (algebraMap F (AdeleRing (𝓞 F) F) a))).nullMeasurableSet
  · obtain ⟨k, hk, huniq⟩ :=
      AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F (algebraMap F (AdeleRing (𝓞 F) F) a * x)
    refine ⟨⟨algebraMap F (AdeleRing (𝓞 F) F) (a⁻¹ * k), a⁻¹ * k, rfl⟩, ?_, ?_⟩
    · show algebraMap F (AdeleRing (𝓞 F) F) a * (algebraMap F (AdeleRing (𝓞 F) F) (a⁻¹ * k) + x) ∈ AdelicBox.adelicBox F
      rwa [mul_add, ← map_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · rintro ⟨_, k', rfl⟩ hk'
      have hk'B : algebraMap F (AdeleRing (𝓞 F) F) (a * k') + algebraMap F (AdeleRing (𝓞 F) F) a * x ∈ AdelicBox.adelicBox F := by
        have h : algebraMap F (AdeleRing (𝓞 F) F) a * (algebraMap F (AdeleRing (𝓞 F) F) k' + x) ∈ AdelicBox.adelicBox F := hk'
        rwa [mul_add, ← map_mul] at h
      have hak : a * k' = k := huniq (a * k') hk'B
      have hk'eq : k' = a⁻¹ * k := by
        rw [← hak, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      subst hk'eq
      rfl

end FltWs24.AdelicModulusOne

open NumberField

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ :=
  FltWs24.AdelicModulusOne.isAddFundamentalDomain_preimage_mul F μ a ha
