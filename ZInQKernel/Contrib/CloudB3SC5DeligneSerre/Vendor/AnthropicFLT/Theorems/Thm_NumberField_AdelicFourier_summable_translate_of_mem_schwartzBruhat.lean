/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat (git blob ccc62e9eed4f3757841678bfec56442af1ee3ba2, sha256 6a7e2df7057bb84cfc194fea0b59aef7ebe659aa671c7ec30abe89cb71cd330d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat (F : Type) [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    Summable fun ξ : F => f (x + algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  revert F f hf x
  exact @_root_.P2MW.S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.solution
