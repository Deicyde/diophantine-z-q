/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact (git blob fcd5b987dcb7cc8af9920d67e0268ce48f373d10, sha256 a604bf4ac85c7d44e0e35bea0e0b404a82c54134d6b96c9c3358e4b4dadc15bc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField FLT.SmoothVectors

theorem AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) := by
  revert F φ hφ K hK
  exact @_root_.P2MW.S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.solution
