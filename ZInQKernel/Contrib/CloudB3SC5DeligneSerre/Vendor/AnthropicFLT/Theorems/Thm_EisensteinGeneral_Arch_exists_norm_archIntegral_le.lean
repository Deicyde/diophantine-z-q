/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Arch_exists_norm_archIntegral_le (git blob 6442953be1487374bc7dab9ba53b06a46a557d6e, sha256 393e7c6141de643b431ca6b7e9de36bfa510ce68ba7c91baf5c55459583b4f6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Arch_exists_norm_archIntegral_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_norm_archIntegral_le (c : ℂ) (hc : 0 < c.re) (M : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (z : ℂ) (r : ℝ), |z.re| ≤ M → r ≠ 0 →
      ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by
  revert c hc M
  exact @_root_.P2MW.S_EisensteinGeneral_Arch_exists_norm_archIntegral_le.solution
