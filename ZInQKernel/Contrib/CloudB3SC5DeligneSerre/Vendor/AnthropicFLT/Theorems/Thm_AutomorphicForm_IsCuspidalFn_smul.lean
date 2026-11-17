/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsCuspidalFn_smul (git blob ab77b60200c9e312b6953cb57299d9d885f6a1f1, sha256 5f5f0ca96c7698f09f61d6c09c4e46a3d9e27a7fc2c476dfbb17391e4fe7a71b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsCuspidalFn_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (c : ℂ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => c * f x) := by
  revert Q G μ u f hf c
  exact @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_smul.solution
