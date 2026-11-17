/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Arch_exists_complexKType (git blob a63d9ee1e4edd56072be1768a7099bf8a7920424, sha256 646aa19e35f6b07ce47339b5217cd427bc6c059c6111962cf172d44ce89bbd1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Arch_exists_complexKType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Set MeasureTheory
set_option autoImplicit false

theorem EisensteinGeneral.Arch.exists_complexKType (a b : ℕ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  revert a b
  exact @_root_.P2MW.S_EisensteinGeneral_Arch_exists_complexKType.solution
