/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four (git blob 2132011524a816eb3e63c8627e6a9a43f06c2397, sha256 7c255be28aebbeb28834f687a3d5848c4ee9a3ff51852376ea7192e910193c27).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) := by
  revert γ hγ
  exact @_root_.P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.solution
