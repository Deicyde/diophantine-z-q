/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1 (git blob 7617c67073fbfb08fd54b7af3fa4da411de1efe5, sha256 84ef2ead64cb9ecd9adf0f966f71acc8d98d0610b663149f3fcb49625c52a437).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1

set_option autoImplicit false

open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical
  obtain ⟨n, b, hb⟩ := ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k
  have hrat : ∀ (i : Fin n) (m : ℕ), ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (⇑(b i) : UpperHalfPlane → ℂ)).coeff m = (r : ℂ) := by
    intro i m
    obtain ⟨r, hr⟩ := hb i m
    exact ⟨r, hr.symm⟩
  choose D r hD hint using fun i => ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N (b i) (hrat i)
  refine ⟨n, fun i => b.repr F i / (D i : ℂ), fun i => ((D i : ℂ)) • b i, r, fun i => ?_, ?_⟩
  · rw [ModularForm.IsGLPos.coe_smul]; exact hint i
  · have hsum := b.sum_repr F
    have hcoe : (⇑F : UpperHalfPlane → ℂ) = ∑ i, b.repr F i • (⇑(b i) : UpperHalfPlane → ℂ) := by
      conv_lhs => rw [← hsum]
      rw [show (⇑(∑ i, b.repr F i • b i) : UpperHalfPlane → ℂ) = FunLike.coeAddMonoidHom (ModularForm _ k) UpperHalfPlane ℂ (∑ i, b.repr F i • b i) from rfl, map_sum]
      rfl
    rw [hcoe]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.IsGLPos.coe_smul, smul_smul, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr (hD i))]
