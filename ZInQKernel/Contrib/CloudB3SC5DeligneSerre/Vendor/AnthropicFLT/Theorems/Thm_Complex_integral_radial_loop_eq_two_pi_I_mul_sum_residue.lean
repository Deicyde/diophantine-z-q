/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue (git blob b2a05c53165324648a62ec7ba58bc59b664403e3, sha256 e87b02a7031888cd50c02fe30b9c3fa5a513a705002ba7ab6da64dc226e172ab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex in

theorem Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)
    (hint : ∀ p ∈ P, ‖p - c‖ < r (arg (p - c)))
    (han : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∉ P → AnalyticAt ℂ f z)
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = res p / (z - p) + g z) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) =
      2 * Real.pi * I * ∑ p ∈ P, res p := by
  revert c r hcont hper hpos N φs hφ0 hφN hmono hC2 f P res hint han hpole
  exact @_root_.P2MW.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue.solution
