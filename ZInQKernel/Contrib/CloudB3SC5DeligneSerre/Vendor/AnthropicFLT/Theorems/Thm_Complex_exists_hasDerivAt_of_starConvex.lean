/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_exists_hasDerivAt_of_starConvex (git blob eae4bb03ff9c08b86c454f9075714b06baafbeea, sha256 3f87f844765def92deb065b4c21dc7498a64c152ccabeaa128e10750dab7373f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_exists_hasDerivAt_of_starConvex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Complex.exists_hasDerivAt_of_starConvex {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ U)
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z := by
  revert U hU q hq hstar f hf
  exact @_root_.P2MW.S_Complex_exists_hasDerivAt_of_starConvex.solution
