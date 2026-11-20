/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_charInvolution_comp_opFamily (git blob d92f760840007f757ae38b0fbfef010cf6d89a7c, sha256 022357ce833d9f778ebb33d04d5971b4141f008a85db96e2f611a1f289142b10).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Inst
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_CharInvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_charInvolution_comp_opFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem CohCarrier.charInvolution_comp_opFamily
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen M S) :
    CohCarrier.charInvolution M H 𝒪 𝒪 ∘ₗ CohCarrier.opFamily M H S 𝒪 g =
      CohCarrier.opFamily M H S 𝒪 g ∘ₗ CohCarrier.charInvolution M H 𝒪 𝒪 := by
  revert M H S 𝒪 g
  exact @_root_.P2MW.S_CohCarrier_charInvolution_comp_opFamily.solution
