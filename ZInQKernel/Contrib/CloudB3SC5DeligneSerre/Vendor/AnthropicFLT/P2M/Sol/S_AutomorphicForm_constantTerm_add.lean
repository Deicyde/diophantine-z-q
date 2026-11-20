/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_constantTerm_add (git blob cb52451371248780d1660357633ff6f90e28caaa, sha256 67225cc5884bca8eb0828702acb654174737d2c9f23390eb129a9d51805ecc95).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_constantTerm_add
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : Integrable (constantTermIntegrand u f₂ g) μ) :
    constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
  simpa [constantTerm, constantTermIntegrand] using integral_add h₁ h₂
