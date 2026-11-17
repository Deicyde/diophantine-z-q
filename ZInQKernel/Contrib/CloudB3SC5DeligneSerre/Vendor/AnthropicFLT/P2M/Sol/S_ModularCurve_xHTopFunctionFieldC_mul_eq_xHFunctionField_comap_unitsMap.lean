/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap (git blob f71e37a3471d7186b4e449b8ad24d271b2a45572, sha256 cf2a3740c5ebb3535abc36cd94f06ba97c4aa838fb7855e57edee3af2ee46505).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_xHTopFunctionFieldC_mul_eq_xHFunctionField_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) =
      ModularCurve.xHFunctionField (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by
  show ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) =
    ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))))
  rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]
