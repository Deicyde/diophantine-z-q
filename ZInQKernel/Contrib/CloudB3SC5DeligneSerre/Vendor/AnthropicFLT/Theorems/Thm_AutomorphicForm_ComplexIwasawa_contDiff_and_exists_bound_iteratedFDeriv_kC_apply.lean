/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply (git blob 909ff0a2e27d40294ae73d2685eaec387427b750, sha256 c9b4c1e66b79ab6b7a109336fd622a24c65398acf8628e8d6e9ffabcf5194ebb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => kC g w i j)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
        ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by
  revert g hg
  exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.solution
