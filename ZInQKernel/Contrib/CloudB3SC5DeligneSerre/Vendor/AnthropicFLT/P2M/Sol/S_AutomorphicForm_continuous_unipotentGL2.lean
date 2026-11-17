/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_continuous_unipotentGL2 (git blob 56c39d876a1f65e7d3a4f819fe5b578319dd9977, sha256 6f6fb79427e443897aa0c4e5a24b966b63b501396c17d4c338c71475026148e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_continuous_unipotentGL2

open AutomorphicForm

namespace M4aP3B
namespace CTU

variable {R : Type*} [CommRing R]

theorem unipotentGL2_inv (x : R) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

end M4aP3B.CTU

theorem solution {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by
  have hval : Continuous fun x : R =>
      ((AutomorphicForm.unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    refine continuous_matrix fun i j => ?_
    simp only [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [M4aP3B.CTU.unipotentGL2_inv]
  exact hval.comp continuous_neg

#print axioms solution
