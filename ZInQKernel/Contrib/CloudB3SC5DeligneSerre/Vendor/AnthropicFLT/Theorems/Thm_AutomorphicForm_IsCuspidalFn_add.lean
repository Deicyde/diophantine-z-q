/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsCuspidalFn_add (git blob d52de9ecc2be7ae65a23b2858340e6dad617cfbc, sha256 7ba727dc45b0c6276c2d24c38c16a3b81e2725a4079f33180a371ef6c61e3882).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsCuspidalFn_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : AutomorphicForm.IsCuspidalFn μ u f₁) (hf₂ : AutomorphicForm.IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f₁ x + f₂ x) := by
  revert Q G μ u f₁ f₂ hf₁ hf₂ h₁ h₂
  exact @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_add.solution
