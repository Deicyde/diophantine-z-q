/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_IsCuspidalFn_add (git blob 56870e90d110bd12a6e918fd62e7cccdfb798673, sha256 2afced7c50504d2cd09b9ed9fa45b0a151899f2bb914cf779e7fd1cff73f76e5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_constantTerm_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_IsCuspidalFn_add
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : IsCuspidalFn μ u f₁) (hf₂ : IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, Integrable (constantTermIntegrand u f₂ g) μ) :
    IsCuspidalFn μ u (fun x => f₁ x + f₂ x) :=
  fun g => by rw [AutomorphicForm.constantTerm_add μ u g (h₁ g) (h₂ g), hf₁ g, hf₂ g, add_zero]
