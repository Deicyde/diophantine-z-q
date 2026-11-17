/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma (git blob 492e4025834fe052a4cb9dbc0c9b53fb208042b0, sha256 bb7878b6306775c64216517800f3b5c6125bc15cadd046350198b61fa59fbf90).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  revert N hN
  exact @_root_.P2MW.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma.solution
