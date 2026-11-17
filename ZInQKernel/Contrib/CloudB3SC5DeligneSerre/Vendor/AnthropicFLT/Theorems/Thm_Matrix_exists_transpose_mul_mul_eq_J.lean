/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_exists_transpose_mul_mul_eq_J (git blob 7fb0967e7d074e16f8045cc71e73f8cdc5f70e96, sha256 4e31359cf545bc6cccbb3c9456d4364b9dfbf9600df0ac75ceb9a365c3a438af).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_exists_transpose_mul_mul_eq_J

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Matrix.exists_transpose_mul_mul_eq_J {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hQ : Q.transpose = -Q) (hdet : IsUnit Q.det) :
    ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ, IsUnit P.det ∧
      P.transpose * Q * P = Matrix.J (Fin n) ℤ := by
  revert n Q hQ hdet
  exact @_root_.P2MW.S_Matrix_exists_transpose_mul_mul_eq_J.solution
