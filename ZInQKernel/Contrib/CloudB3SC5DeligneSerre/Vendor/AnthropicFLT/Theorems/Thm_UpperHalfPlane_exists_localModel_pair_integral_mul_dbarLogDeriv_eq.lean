/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq (git blob e9ed97008f83e63641449deb5186248ca923c02f, sha256 4726558e0117bd18bf9b89e3dd7605f0647c48e70199100be056646043488136).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex MeasureTheory
open scoped Real Topology

theorem UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq
    (b s : ℂ) (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s) :
    ∃ d F : ℂ → ℂ, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ z ∉ K, d z = 1) ∧
      (∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
        d =ᶠ[𝓝 τ] fun z =>
          (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z) ∧
      Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ K ∧
      (∀ z : ℂ, 0 < z.im → z ≠ b →
        (fderiv ℝ d z 1 + I * fderiv ℝ d z I) / 2 / d z = F z) ∧
      ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
        Integrable (fun z : ℂ => E' z * F z) ∧ ∫ z : ℂ, E' z * F z = π * (E s - E b) := by
  revert b s hb hs hbs
  exact @_root_.P2MW.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.solution
