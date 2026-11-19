/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_exists_trivialization_add_pow (git blob 17ddbdfcf9cc65b5ee2a84d88626222ff2199a86, sha256 ff8f1d16c0fd7cf6053fcd9390b41f5d5acd34ff8ddfdcde85ccae4493394869).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_exists_trivialization_add_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Complex.exists_trivialization_add_pow {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * Complex.I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e := by
  revert b θ e he U hray
  exact @_root_.P2MW.S_Complex_exists_trivialization_add_pow.solution
