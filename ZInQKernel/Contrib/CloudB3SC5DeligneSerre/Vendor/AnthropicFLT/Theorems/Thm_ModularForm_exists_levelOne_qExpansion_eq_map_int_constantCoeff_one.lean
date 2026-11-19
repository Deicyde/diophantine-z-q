/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one (git blob 4b4d3c461c6d0a19acd91722a5b0274eb7658eb6, sha256 166d8b0934c5abbc45f723c01fc02e3506321d9ab026b5bf6dcb2966c704e8e1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups in

theorem ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one (a b : ℕ) (e : ℤ)
    (he : 4 * (a : ℤ) + 6 * (b : ℤ) = e) :
    ∃ (E : ModularForm 𝒮ℒ e) (P : PowerSeries ℤ),
      P.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) ∧
      PowerSeries.constantCoeff P = 1 := by
  revert a b e he
  exact @_root_.P2MW.S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one.solution
