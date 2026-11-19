/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg (git blob a0c4fe56499a6f0e51c0b0729bc710100849817f, sha256 00140b692f3c6fefd70844bdfeb0657f211809787daea8187835b741e2ba6290).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg (f : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 := by
  revert f hper hhol hbdd L hO n hn
  exact @_root_.P2MW.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.solution
