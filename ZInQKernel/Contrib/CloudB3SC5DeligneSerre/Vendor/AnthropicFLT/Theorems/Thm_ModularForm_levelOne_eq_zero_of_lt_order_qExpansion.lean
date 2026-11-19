/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion (git blob 842af80816d6205516dca21e99bb24db044f4ad2, sha256 11bdfa5091890e63314c45d7d18897f3e99ca748c49ddcdc33f690f8c5fbd940).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Manifold
theorem ModularForm.levelOne_eq_zero_of_lt_order_qExpansion (M : ℕ) (hM : 0 < M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (h : ((M * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (M : ℝ) F).order) : F = 0 := by
  revert M hM k F h
  exact @_root_.P2MW.S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.solution
