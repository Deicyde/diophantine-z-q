/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty (git blob 3973386c5bc0f56e2c471ee6e593e28f881be205, sha256 c02eeacb8c3c9b9ee11c39e1b30c41225b4c8bf18541fb2e92c1edab2b7fe7eb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane Complex Filter
open scoped Topology

theorem UpperHalfPlane.intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (y : ℝ) (hy : Y < y) :
    ∫ x in (0 : ℝ)..1, ω (ofComplex (x + y * Complex.I)) = 0 := by
  revert ω Y hY hper hcusp hhol y hy
  exact @_root_.P2MW.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty.solution
