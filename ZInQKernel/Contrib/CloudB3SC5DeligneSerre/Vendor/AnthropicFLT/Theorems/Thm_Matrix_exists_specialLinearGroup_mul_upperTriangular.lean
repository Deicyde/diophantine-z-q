/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular (git blob 6fa528791c5fa081848a3820644fe7dd6b1bb1c1, sha256 20a5f09564ef2381e5602c50a953619b3ebc746c660f95e6c1a58f20d8a4b8a1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_exists_specialLinearGroup_mul_upperTriangular

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Matrix.exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by
  revert M hM
  exact @_root_.P2MW.S_Matrix_exists_specialLinearGroup_mul_upperTriangular.solution
