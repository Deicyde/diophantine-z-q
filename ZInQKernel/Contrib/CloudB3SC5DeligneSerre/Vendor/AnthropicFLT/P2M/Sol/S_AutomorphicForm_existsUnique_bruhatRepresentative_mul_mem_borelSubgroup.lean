/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup (git blob 384d9475e66c9dd6b49977c0a503411a1e311dcc, sha256 686b3d73e3381bf3a6daf44548f6b71a48eb39140a98705d190450e704ba28e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup

set_option autoImplicit false

open AutomorphicForm

namespace BruhatC5

variable {K : Type*} [Field K]

theorem entry_weyl_unipotent_mul (ξ : K) (γ : GL (Fin 2) K) :
    ((((gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, gl2Weyl_val, unipotentGL2_coe]

theorem det_ne_zero (γ : GL (Fin 2) K) : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det γ).ne_zero

end BruhatC5

open BruhatC5 in
theorem solution
    (K : Type*) [Field K] (γ : GL (Fin 2) K) :
    ∃! o : Option K, (o.elim 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K := by
  have hdet := det_ne_zero γ
  rw [Matrix.det_fin_two] at hdet
  by_cases h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · refine ⟨none, ?_, ?_⟩
    · show (Option.elim none 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K
      simp only [Option.elim, one_mul, mem_borelSubgroup_iff]
      exact h10
    · intro o ho
      cases o with
      | none => rfl
      | some ξ =>
        exfalso
        have h := ho
        simp only [Option.elim, mem_borelSubgroup_iff] at h
        rw [entry_weyl_unipotent_mul, h10, mul_zero, add_zero] at h
        apply hdet
        rw [h, h10]; ring
  · refine ⟨some (-((γ : Matrix (Fin 2) (Fin 2) K) 0 0) / (γ : Matrix (Fin 2) (Fin 2) K) 1 0), ?_, ?_⟩
    · show (Option.elim (some _) 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K
      simp only [Option.elim, mem_borelSubgroup_iff]
      rw [entry_weyl_unipotent_mul]
      field_simp
      ring
    · intro o ho
      cases o with
      | none =>
        exfalso
        have h := ho
        simp only [Option.elim, one_mul, mem_borelSubgroup_iff] at h
        exact h10 h
      | some ξ =>
        have h := ho
        simp only [Option.elim, mem_borelSubgroup_iff] at h
        rw [entry_weyl_unipotent_mul] at h
        congr 1
        field_simp
        linear_combination h
