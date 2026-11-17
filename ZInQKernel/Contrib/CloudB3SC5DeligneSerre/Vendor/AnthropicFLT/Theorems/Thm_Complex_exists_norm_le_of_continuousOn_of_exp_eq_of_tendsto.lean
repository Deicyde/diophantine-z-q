/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto (git blob 1426532ef0c411d2de4e81a37e8c035a3630dacc, sha256 b46c82d045a1bbb183217a8a16715b5e62696c371c2b4e1c97a9257b236f7bb7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by
  revert Λ ℓ a c hΛ hexp hlim hc
  exact @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution
