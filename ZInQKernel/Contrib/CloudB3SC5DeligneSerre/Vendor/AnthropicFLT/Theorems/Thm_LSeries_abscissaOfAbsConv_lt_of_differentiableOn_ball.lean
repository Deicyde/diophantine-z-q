/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball (git blob 6e19cddf7781fc2be0a5139763480b17dc1ec4aa, sha256 922d99b99f50d520ca5b7e29e6c8faf0c7bc23cdbaf6594984b77301b791c039).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.Complex.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped ComplexOrder
open Complex Set Metric LSeries
namespace LSeries
theorem abscissaOfAbsConv_lt_of_differentiableOn_ball {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := by
  revert a ha x hx f r hr hf hfa
  exact @_root_.P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.solution
end LSeries
