/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup (git blob 6c530eeaf2482d524f5e14edd7a0c086fa9488d4, sha256 a6093f62662e9c5d68b718f49caacdc8d4905272ac434a706e78b9730c884bb1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.UnitaryGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm.ComplexIwasawa

theorem AutomorphicForm.ComplexIwasawa.kC_mem_specialUnitaryGroup
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  revert g hg z
  exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.solution
