/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_constantTerm_rightTranslate (git blob f3a5669d98f9f851b70eefc1735b73c26f1cc5dc, sha256 178e9659e9b8c63f5ef6e12a1d2715747a51ddf5d3dc4b9a044fd0efb2bb805e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_constantTerm_rightTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    AutomorphicForm.constantTerm μ u (fun x => f (x * h)) g
      = AutomorphicForm.constantTerm μ u f (g * h) := by
  revert Q G μ u f g h
  exact @_root_.P2MW.S_AutomorphicForm_constantTerm_rightTranslate.solution
