/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt (git blob e5fe9ec7c88c54e26d931ae9bd71a9190035f438, sha256 5a9795e46abebd37b070d56db00069fbee44f44a6579ca825c7adb933012a5f4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory

theorem ZSpan.norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Module.Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ℓ : E →L[ℝ] ℝ) (v : E) (hv : ℓ v ≠ 0)
    (Hs : ℕ → E → ℂ) (hcont : ∀ j, Continuous (Hs j))
    (hderiv : ∀ (j : ℕ) (x : E), HasDerivAt (fun t : ℝ => Hs j (x + t • v)) (Hs (j + 1) x) 0)
    (hper : ∀ (j : ℕ) (x : E) (i : ι),
      Complex.exp (2 * Real.pi * Complex.I * ℓ (x + b i)) * Hs j (x + b i) =
        Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs j x)
    (M : ℕ) :
    ‖∫ x in ZSpan.fundamentalDomain b, Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs 0 x ∂μ‖ ≤
      ((2 * Real.pi * |ℓ v|)⁻¹) ^ M * ∫ x in ZSpan.fundamentalDomain b, ‖Hs M x‖ ∂μ := by
  revert ι E b μ ℓ v hv Hs hcont hderiv hper M
  exact @_root_.P2MW.S_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt.solution
