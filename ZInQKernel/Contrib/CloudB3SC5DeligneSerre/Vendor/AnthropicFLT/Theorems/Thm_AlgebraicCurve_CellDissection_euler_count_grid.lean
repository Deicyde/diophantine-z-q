/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_CellDissection_euler_count_grid (git blob d941cd48ac795619b49b0bcf4686641a33194c50, sha256 0bef49f0cbc36db3a489f0fa791691f7ad62b1a72be558e352fa7e88eafb8656).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CellDissection_euler_count_grid

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.CellDissection.euler_count_grid (n J K np nc : ℕ) (g : ℤ) (hJK : np + nc = J * K)
    (ιc : Type*) [Fintype ιc] (hnc : Fintype.card ιc = nc)
    (fib : ιc → Type*) [∀ b, Fintype (fib b)] (ec : ∀ b, fib b → ℕ)
    (hec : ∀ b, ∑ w, ec b w = n)
    (ιp : Type*) [Fintype ιp] (ep : ιp → ℕ) (hep : ∑ q, ep q = n)
    (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
    2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
        ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
        2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
      2 * (2 - 2 * g) := by
  revert n J K np nc g hJK ιc hnc fib ec hec ιp ep hep hRH
  exact @_root_.P2MW.S_AlgebraicCurve_CellDissection_euler_count_grid.solution
