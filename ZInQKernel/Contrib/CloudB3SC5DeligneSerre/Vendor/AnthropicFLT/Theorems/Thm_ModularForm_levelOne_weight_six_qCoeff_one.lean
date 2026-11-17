/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_levelOne_weight_six_qCoeff_one (git blob 2df88ef10438d24893df1ecf9859a3103a748ad6, sha256 663d0494868a889370fb4741956ec2aafe621b49b304db360d055a8956f3ba4e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_levelOne_weight_six_qCoeff_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) : ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 := by
  revert Y
  exact @_root_.P2MW.S_ModularForm_levelOne_weight_six_qCoeff_one.solution
