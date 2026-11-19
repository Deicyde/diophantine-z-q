/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable (git blob b6c0080e2c9c97dca93549b4bef5e3e21897c43e, sha256 f8d798c93fa233c8ac4da3579deee38a1d1458ef769af24c8d8157e39d49ea9c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open MeasureTheory NumberField IsDedekindDomain
set_option autoImplicit false

open scoped Classical in

theorem EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (hf : Integrable f MeasureTheory.volume) (hg : Integrable g ν) :
    Integrable (fun x : AdeleRing (𝓞 F) F => f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) μ := by
  revert F μ ν f g hf hg
  exact @_root_.P2MW.S_EisensteinGeneral_Glue_integrable_mul_of_integrable_of_integrable.solution
