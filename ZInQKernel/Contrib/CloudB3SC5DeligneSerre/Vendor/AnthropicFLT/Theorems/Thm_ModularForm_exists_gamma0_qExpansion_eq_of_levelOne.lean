/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne (git blob bb60b1a2fb12a97a8742954a1974dca560b9ed18, sha256 c222e048223512e87e4bac607d2ce00819889805408e1b57275817d80f74e26b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  revert N k F
  exact @_root_.P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.solution
