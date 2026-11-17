/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_constantTerm_add (git blob 1dc9bd17d713c09c90ff5b69bab5a0e858b1d03d, sha256 c32ca08535c9948951a588692b26b02e44a5ce11ac34096ec53aca2513fbe1ea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_constantTerm_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.constantTerm μ u (fun x => f₁ x + f₂ x) g
      = AutomorphicForm.constantTerm μ u f₁ g + AutomorphicForm.constantTerm μ u f₂ g := by
  revert Q G μ u f₁ f₂ g h₁ h₂
  exact @_root_.P2MW.S_AutomorphicForm_constantTerm_add.solution
