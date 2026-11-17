/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_closure_elemSet_eq_top (git blob bedcf52776baecd1d5512a65a814c578baa1d88f, sha256 c4fa97700bf4ae4d4673d20dfa3fe03752f67b267e817cb53b08207a47249d81).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean).
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SL2Elementary
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_closure_elemSet_eq_top

set_option autoImplicit false

open Matrix MatrixGroups Subgroup ModularCurve

theorem solution (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by
  set φ : SL(2, ℤ) →* SL(2, ZMod N) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) with hφ
  have hT : φ ModularGroup.T = upperElem (1 : ZMod N) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hφ, ModularGroup.coe_T]
  have hS : φ ModularGroup.S =
      upperElem (-1 : ZMod N) * lowerElem 1 * upperElem (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsurj : Function.Surjective φ :=
    ModularCurve.surjective_specialLinearGroup_map_zmod N
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ hsurj,
    ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure]
  refine (closure_le _).mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · rw [hS]
    exact mul_mem (mul_mem (upperElem_mem_closure_elemSet _)
      (lowerElem_mem_closure_elemSet _)) (upperElem_mem_closure_elemSet _)
  · rw [hT]
    exact upperElem_mem_closure_elemSet _
