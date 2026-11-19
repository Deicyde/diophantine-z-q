/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet (git blob 52f7b3aa3834a5638cf5cc9a84c71d44bfbf77e7, sha256 2076d8a18c5cc8c70ed78823553ca6762bd2bdcb9d1d3efcead49f8410fae4df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F]
    {f : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn F f)
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
    (fun s => f (g₁ * AutomorphicForm.unipotentGL2 s * g₂)) ∈ NumberField.AdelicFourier.pureTensorSet F := by
  revert F f hf g₁ g₂
  exact @_root_.P2MW.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet.solution
