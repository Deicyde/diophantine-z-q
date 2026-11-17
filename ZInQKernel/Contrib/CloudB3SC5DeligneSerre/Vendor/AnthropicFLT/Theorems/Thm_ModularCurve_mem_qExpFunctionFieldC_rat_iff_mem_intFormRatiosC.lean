/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (git blob 52df610210461e393e7bb21f5b0b11d8484fea02, sha256 6dd282a7fb6f7f02787d3b5748eddb29b5cbfc2a5bd531106ebf01d7b6fa51d4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MatrixGroups

theorem ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
    (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (x : LaurentSeries ℚ) :
    x ∈ ModularCurve.qExpFunctionFieldC ℚ Γ ↔ x ∈ ModularCurve.intFormRatiosC ℚ Γ := by
  revert Γ hΓ x
  exact @_root_.P2MW.S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC.solution
