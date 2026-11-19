/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup (git blob c1ae75d23030f457afc708811393fc9ced2303ff, sha256 c8903e0cd42fb6d283a53099ee670de34a62e9362acec64e2e9ee44dd11350f9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm NumberField.AdelicLevel

theorem AutomorphicForm.existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
    (K : Type*) [Field K] (b : GL (Fin 2) K) (hb : b ∈ borelSubgroup K) :
    ∃! a : Kˣ, (diagOne a)⁻¹ * b ∈
      (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom).range ⊔
        (unipotentGL2Hom (R := K)).range := by
  revert K b hb
  exact @_root_.P2MW.S_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup.solution
