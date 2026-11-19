/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar (git blob 220ddd5bca4cda6c8776ca8ef124141ebf6eff7e, sha256 a4b082f451304ed19998eba11c2d006aef5c87360bc3ee43c02109d7d8bfe6c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar

set_option autoImplicit false

open NumberField MeasureTheory MeasureTheory.Measure

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem FltWs24.regular_adelicAddHaar (F : Type) [Field F] [NumberField F] :
    (AdelicHaar.adelicAddHaar (𝓞 F) F).Regular := by
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  first
    | exact (inferInstance : (Measure.addHaar : Measure (AdeleRing (𝓞 F) F)).Regular)
    | (unfold AdelicHaar.adelicAddHaar Measure.addHaar; infer_instance)
    | (delta NumberField.AdelicHaar.adelicAddHaar; unfold Measure.addHaar; infer_instance)

theorem solution
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicHaar.adelicAddHaar (𝓞 F) F) := by
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI := FltWs24.regular_adelicAddHaar F
  exact NumberField.AdeleRing.measurePreserving_mul_algebraMap F _ a ha
