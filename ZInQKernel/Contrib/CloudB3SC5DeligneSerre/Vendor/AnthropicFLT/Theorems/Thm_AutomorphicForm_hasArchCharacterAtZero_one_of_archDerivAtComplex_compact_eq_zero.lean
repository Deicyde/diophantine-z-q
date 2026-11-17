/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero (git blob f92084e61fb52cb8ce66f862485388980ae9333e, sha256 116e6a298624683b45ce3785966aeb83cf0f98786ecc8fc389677df6246cbd33).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y, (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ Y)
    (h0 : archDerivAtComplex hw .iH x = 0)
    (h1 : archDerivAtComplex hw .Fm x - archDerivAtComplex hw .E x = 0)
    (h2 : archDerivAtComplex hw .iE x + archDerivAtComplex hw .iFm x = 0) :
    HasArchCharacterAt₀ F w 1 x := by
  revert F w hw Y hYs hYK x hx h0 h1 h2
  exact @_root_.P2MW.S_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero.solution
