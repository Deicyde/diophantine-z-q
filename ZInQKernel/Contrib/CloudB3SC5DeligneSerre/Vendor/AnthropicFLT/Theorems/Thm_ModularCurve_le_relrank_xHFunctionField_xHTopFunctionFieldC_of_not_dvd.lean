/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd (git blob e854349a7f4196c94364ba1a1466e60fd8d81863, sha256 9745d180910ad346438dd33b8d0e118c48f7331469a8d43b59e67918088d33be).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ((ℓ + 1 : ℕ) : Cardinal) ≤
      IntermediateField.relrank (ModularCurve.xHFunctionField M H)
        (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := by
  revert M H ℓ hℓM
  exact @_root_.P2MW.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.solution
