/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic (git blob 74d24b5b994836a530daac80a9f27a2d567439c7, sha256 9fc0cb13a71a001a2b8a52b71439cc073c665cbccafc64b01f2ddd7c78702806).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Pointwise
theorem ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M) (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods) (h : ((M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ) : ℕ∞) < (qExpansion M f).order) : f = 0 := by
  revert 𝒢 k f M hM hconj h
  exact @_root_.P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.solution
