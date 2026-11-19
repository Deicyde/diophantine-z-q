/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_constantTerm_smul (git blob db08dca5c9a7364bd9893511b6eb4d48eb98fb5e, sha256 8be5746702f3c686672e2fdbab7318e5e86eaec6d2f98e1b451299b681010fb0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_constantTerm_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    AutomorphicForm.constantTerm μ u (fun x => c * f x) g
      = c * AutomorphicForm.constantTerm μ u f g := by
  revert Q G μ u c f g
  exact @_root_.P2MW.S_AutomorphicForm_constantTerm_smul.solution
