/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm (git blob 44a52ad7931981611fdad216ca02c04101ac47f4, sha256 0b28588b778a17ac20e5c684d63e5fed42acb0483196feedff66105d4b8125b9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm (N : ℕ) [NeZero N] :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) ≤
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.solution
