/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal (git blob 7b4dc5c727bde134ff274d4e7587422adb710350, sha256 8f054132f69cd0b39f55d44e0e5a6e16873b1f190b614e8199c5591ab467d4ad).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
    (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ' ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ' 2)) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  revert Γ' Γ hle hn h
  exact @_root_.P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.solution
