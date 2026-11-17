/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap (git blob 0b0273398394538a9dfe4a420a537d271ed45ba1, sha256 b1d2c273f54de7efa7ea4c4ac9d907a9b9284c5787866792ab9f89917bf6acb5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) =
      ModularCurve.xHFunctionField (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by
  revert M ℓ H
  exact @_root_.P2MW.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap.solution
