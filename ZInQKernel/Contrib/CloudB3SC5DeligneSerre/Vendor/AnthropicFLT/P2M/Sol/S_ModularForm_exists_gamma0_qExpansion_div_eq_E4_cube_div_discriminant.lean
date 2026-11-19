/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant (git blob 4668892ee25b6928cb9f8c3bb7789d840521a439, sha256 6363e775c4254635ee7d00c66d23beced99e73a7d3ad066cb4a465becb199e37).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.LaurentSeries
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_degeneracy_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant

open UpperHalfPlane
open scoped MatrixGroups

namespace SolJJ0Aux

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

private noncomputable def e4cube : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) gamma0_one_coe

private noncomputable def delta1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast rfl (CuspForm.toModularFormₗ CuspForm.discriminant) gamma0_one_coe

private theorem coe_e4cube : ⇑e4cube = ⇑(ModularForm.E₄.pow 3) := rfl

private theorem coe_delta1 : ⇑delta1 = ModularForm.discriminant := rfl

end SolJJ0Aux

theorem solution (ℓ : ℕ) [NeZero ℓ] : ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 ℓ) 12,
    H ≠ 0 ∧ ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
      ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
    (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 /
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 1 * 1 ∣ ℓ by simp) SolJJ0Aux.e4cube
  obtain ⟨H, hH⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 1 * 1 ∣ ℓ by simp) SolJJ0Aux.delta1
  have hGfun : ⇑G = ⇑(ModularForm.E₄.pow 3) := by
    rw [hG, SolJJ0Aux.heckeDiagMatrix_one]
    funext τ
    rw [one_smul]
    rfl
  have hHfun : ⇑H = ModularForm.discriminant := by
    rw [hH, SolJJ0Aux.heckeDiagMatrix_one]
    funext τ
    rw [one_smul]
    rfl
  refine ⟨G, H, ?_, ?_⟩
  · intro h0
    refine ModularForm.discriminant_ne_zero UpperHalfPlane.I ?_
    rw [← hHfun, h0]
    simp
  · have hqG : qExpansion 1 (G : ℍ → ℂ) = (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
      rw [hGfun]
      exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    have hqH : qExpansion 1 (H : ℍ → ℂ) = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
      rw [hHfun]
    rw [hqG, hqH, PowerSeries.coe_pow]
