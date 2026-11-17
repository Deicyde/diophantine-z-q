/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff (git blob 00556f702457685e349d3eedd93262e3bb667aca, sha256 a75a6db48c1b1c34f5819e76e60969d7f3eb0e674d6d11771f729015ea528f15).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff (f : UpperHalfPlane → ℂ) (h₀ : ℕ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1
        (fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀, f (((j : ℕ) : ℝ) +ᵥ τ))) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (UpperHalfPlane.qExpansion (h₀ : ℝ) f) := by
  revert f h₀ hh₀ hper hhol hbdd m
  exact @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.solution
