/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top (git blob ba2ea19508260a37747cdf566a9353ea6731e798, sha256 27ad9bf2cf69761b980a225f03f0d9e610dc1243915dd8ae620ab2b2ce4f53c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
    (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) < ⊤ := by
  revert F t ht
  exact @_root_.P2MW.S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.solution
