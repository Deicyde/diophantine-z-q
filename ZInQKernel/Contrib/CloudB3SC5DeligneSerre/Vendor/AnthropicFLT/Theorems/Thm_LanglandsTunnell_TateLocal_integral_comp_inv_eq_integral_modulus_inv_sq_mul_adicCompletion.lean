/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion (git blob 8ada8f81621771af5a40e19bdfe1031cdf757250, sha256 845fd59e009282c9caee549465eeaadb9ccf5e3be1d01e40be98dbbad84619c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) :
    ∫ x, f x⁻¹ ∂μ
      = ∫ u, ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • f u ∂μ := by
  revert F v μ f
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion.solution
