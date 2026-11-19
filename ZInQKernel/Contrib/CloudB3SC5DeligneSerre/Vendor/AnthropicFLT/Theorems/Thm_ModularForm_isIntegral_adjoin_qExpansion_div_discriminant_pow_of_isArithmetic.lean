/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic (git blob be59c3db608e058ff939d66227eb2c53827c3b1b, sha256 43c5ba0adaa7f3c7ee92973548230febf6b3a81e51c519aa5af55684940f71ee).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ) {k : ℤ} (hk : k = 12 * m) (g : ModularForm 𝒢 k) : IsIntegral (Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))) (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m) := by
  revert 𝒢 h1 m k hk g
  exact @_root_.P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.solution
