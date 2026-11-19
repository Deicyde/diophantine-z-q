/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq (git blob ed95ebfbc9bdc1caa184564e92a6061169593584, sha256 c2f74e1fc6319b7d6f20f81cf628d32a763dc27ad8cf77bcbb6521b1f4ce74f3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
    {N : ℕ} [NeZero N] {k : ℤ} [DecidableEq (DirichletCharacter ℂ N)] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ N) (g : ι → CuspForm (Gamma1 N) k)
    (hg : ∀ i ∈ s, CuspForm.HasNebentypus (χ i) (g i))
    {ε : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) k} (hf : CuspForm.HasNebentypus ε f)
    (hsum : ∑ i ∈ s, g i = f) :
    ∑ i ∈ s.filter (fun i => χ i = ε), g i = f := by
  revert N k ι s χ g hg ε f hf hsum
  exact @_root_.P2MW.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq.solution
