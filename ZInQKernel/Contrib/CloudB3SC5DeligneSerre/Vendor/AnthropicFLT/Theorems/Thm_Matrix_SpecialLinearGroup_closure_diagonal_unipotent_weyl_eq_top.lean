/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top (git blob fe22cec57faee7ba5b61b72526ef7970f39bebca, sha256 1155515e1a1b6039f4dcf9e22cbf053db17a0a48afb4e63179f7f1cced797355).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Group.Subgroup.Lattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups
theorem Matrix.SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top
    {K : Type*} [Field K] :
    Subgroup.closure
      ({g : SL(2, K) | ∃ a : K, (g : Matrix (Fin 2) (Fin 2) K) = !![a, 0; 0, a⁻¹]} ∪
        {g : SL(2, K) | ∃ z : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1]} ∪
        {g : SL(2, K) | (g : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0]}) = ⊤ := by
  revert K
  exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top.solution
