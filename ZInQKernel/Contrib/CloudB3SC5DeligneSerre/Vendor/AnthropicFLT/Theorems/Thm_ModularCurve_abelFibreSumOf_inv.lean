/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_abelFibreSumOf_inv (git blob 10a0cee4595130503c48587f50399966a598e9c5, sha256 d9f21b48e8c94330b0b11f80d248adb7c9a96c73cf8eeafbe45ff0a7f4efaca5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AbelFibreSumOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_abelFibreSumOf_inv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.abelFibreSumOf_inv
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) {t : ℂ} (ht : t ≠ 0) :
    ModularCurve.abelFibreSumOf Γ (fun τ : ℍ => (F τ)⁻¹) t⁻¹ =
      ModularCurve.abelFibreSumOf Γ F t := by
  revert Γ F t ht
  exact @_root_.P2MW.S_ModularCurve_abelFibreSumOf_inv.solution
