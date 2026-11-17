/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty (git blob 64f5f20719eea9e47cb522168a1e5c30e04f65e7, sha256 6b765fd7a6a8fa0cd2f49cab43d1776e7e9fb9e31bdbee440cf68796b7fbd4b7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane Complex Filter MeasureTheory Set
open scoped Topology

theorem UpperHalfPlane.integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (p ρ : ℝ → ℝ) (hp : Function.support p ⊆ Ioo (-1) 1)
    (hp1 : ∀ x ∈ Icc (0 : ℝ) 1, p (x - 1) + p x = 1)
    (hρ : Function.support ρ ⊆ Ioi Y)
    (hint : Integrable fun z : ℂ => ω (ofComplex z) * (p z.re * ρ z.im : ℝ)) :
    ∫ z : ℂ, ω (ofComplex z) * (p z.re * ρ z.im : ℝ) = 0 := by
  revert ω Y hY hper hcusp hhol p ρ hp hp1 hρ hint
  exact @_root_.P2MW.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty.solution
