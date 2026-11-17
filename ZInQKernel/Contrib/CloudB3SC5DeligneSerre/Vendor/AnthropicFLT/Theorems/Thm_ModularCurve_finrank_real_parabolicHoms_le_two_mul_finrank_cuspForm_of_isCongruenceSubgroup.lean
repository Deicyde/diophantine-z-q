/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup (git blob 7f665ed621725ccb82c6e8cb2f25f03425e81cad, sha256 fc2b56fe8520a6db3d483d3789120a69e1790eb8f8b9591da8b63d9a5ce806da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  revert Γ hΓ
  exact @_root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.solution
