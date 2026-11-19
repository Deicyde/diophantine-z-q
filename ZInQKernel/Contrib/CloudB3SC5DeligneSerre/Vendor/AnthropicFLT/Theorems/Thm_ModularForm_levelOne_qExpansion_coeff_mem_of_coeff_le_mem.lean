/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem (git blob 5fcd9ed07cb96e4a92bf239f97f55e61bead5aea, sha256 9b14c5b27f0b62fed1df33aeaeae5636fd7cf26e0ec9a83208e39a74188c8cac).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open scoped MatrixGroups in

theorem ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem (N : ℕ)
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R := by
  revert N F R hF n
  exact @_root_.P2MW.S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.solution
