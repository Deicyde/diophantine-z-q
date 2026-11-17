/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic (git blob d4707208eed93eea561adf840becf6b872b0f5e3, sha256 80efa9d4a2900edf595c4ceac2eb875b1bf060246579b3f935098498ee39f942).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) {k : ℤ} (g h : ModularForm 𝒢 k) (hh : h ≠ 0) : ∃ B : Polynomial (IntermediateField.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))), B ≠ 0 ∧ B.natDegree ≤ Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∧ Polynomial.aeval (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) B = 0 := by
  revert 𝒢 h1 k g h hh
  exact @_root_.P2MW.S_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic.solution
