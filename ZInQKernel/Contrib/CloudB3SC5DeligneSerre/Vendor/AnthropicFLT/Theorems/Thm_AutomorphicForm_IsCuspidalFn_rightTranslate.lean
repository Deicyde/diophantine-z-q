/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsCuspidalFn_rightTranslate (git blob 8d0b5854c9493697e154086129ad2a2c7547d7fd, sha256 0efc02fed62ccebceac61c30e1afdc3022739d022bc1799d6c06700ce06b6444).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsCuspidalFn_rightTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (h : G) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f (x * h)) := by
  revert Q G μ u f hf h
  exact @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_rightTranslate.solution
