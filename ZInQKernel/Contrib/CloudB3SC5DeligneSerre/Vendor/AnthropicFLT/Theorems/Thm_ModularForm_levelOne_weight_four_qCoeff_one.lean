/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_levelOne_weight_four_qCoeff_one (git blob 137d749723d147acbab623d7b6b3e08fc8a6959f, sha256 b10c063e9cde99ea6061f53c5f9d97e816174d10e974bc4c2342b1596e883338).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_levelOne_weight_four_qCoeff_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by
  revert Y
  exact @_root_.P2MW.S_ModularForm_levelOne_weight_four_qCoeff_one.solution
