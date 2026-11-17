/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite (git blob f7cf817d5b721ad3a52a2478b1d38050f1b62974, sha256 d0fd8423ab5e19e7b816038a28242b0a29596e6315309098c47dd2f5299ffa16).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Matrix.Normed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) := by
  revert Φ hc hfin
  exact @_root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.solution
