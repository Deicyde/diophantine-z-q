/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qExpansion_coeff_nat_mul (git blob a084e3c8e2534ea94a8cec32c2c0db7c7610752e, sha256 c3f70ab13f8ab62006d67d70f79b84ea37bf83fb6a07d9219ba3d2e86da1c33b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_nat_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped Manifold
theorem UpperHalfPlane.qExpansion_coeff_nat_mul {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) : (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by
  revert h hh F hper hhol hbdd M hM n
  exact @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_nat_mul.solution
