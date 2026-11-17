/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq (git blob 7cac8a002d1fa5d25a3d40c06c397dbf4fd86ed4, sha256 aa272fb309a26b295b0600a4c8d8306ae05252021c1c6b6601ea2ef973de8899).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq (N : ℕ) (hN : 2 ≤ N) :
    6 * N * Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq.solution
