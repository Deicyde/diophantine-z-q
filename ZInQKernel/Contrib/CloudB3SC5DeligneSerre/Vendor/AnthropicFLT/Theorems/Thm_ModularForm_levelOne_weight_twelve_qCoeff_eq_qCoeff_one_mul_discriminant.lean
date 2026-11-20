/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (git blob 7985ac69696db7ed9555c11ac854e81132a09642, sha256 81d55e9c9da14882adde79e832c62c0cfe0ecb3e31ef9fd7e213bc44e406a691).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n := by
  revert Z h0
  exact @_root_.P2MW.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.solution
