/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm (git blob fabb0189cd6c61288e2cf5504f3f97b83d66cf9f, sha256 35135379679ac1f821f5a5f59669e8f48d40dd7de850924c86fa4abbeb9f397f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_continuous_ideleNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem NumberField.TateGlobal.continuous_ideleNorm (F : Type) [Field F] [NumberField F] :
    Continuous (NumberField.TateGlobal.ideleNorm F) := by
  revert F
  exact @_root_.P2MW.S_NumberField_TateGlobal_continuous_ideleNorm.solution
