/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet (git blob 0a255f72bca74b2cf56d6df54a2edec5ea9f1047, sha256 bc356156d18a7e26150c4a17c5d4c57dacc3857a48050fa6585aef75f2cef045).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    Summable fun ξ : F => f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  revert F f hf
  exact @_root_.P2MW.S_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.solution
