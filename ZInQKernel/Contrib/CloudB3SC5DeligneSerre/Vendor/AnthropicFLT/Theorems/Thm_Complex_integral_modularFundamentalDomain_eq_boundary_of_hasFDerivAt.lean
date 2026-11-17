/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt (git blob 45abd7bcd575850af40e92fd9684c282d6974c8a, sha256 ab94f2a1697929b017d88b99e5660c4720af25329304bc30bf0203207e796b9f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory

theorem Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt
    (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
    (hDU : {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im} ⊆ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
    (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
    (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im)) :
    (∫ z in {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}, (Complex.I • Φ' z 1 - Φ' z Complex.I)) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * Complex.I))
        - Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * Complex.I))
        - ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) := by
  revert Φ Φ' U δ hδ hU hDU hd hc hΦ hΦ'
  exact @_root_.P2MW.S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt.solution
