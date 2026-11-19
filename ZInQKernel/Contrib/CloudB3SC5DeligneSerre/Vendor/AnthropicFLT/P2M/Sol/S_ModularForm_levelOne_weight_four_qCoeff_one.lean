/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_levelOne_weight_four_qCoeff_one (git blob 7bf61e372833846c098d82139fb6a8bd82a1ee7d, sha256 62ffb2c853833d5bc15e8bb16344bd1c2e3822fc4c76f7a2dd7fba7405530d06).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularForm
end ModularForm

namespace P2MW.S_ModularForm_levelOne_weight_four_qCoeff_one
open scoped MatrixGroups

namespace ModularForm export _root_.ModularForm (levelOne_weight_four_rank_one E₄_qExpansion_coeff_one E₄) end ModularForm
open scoped _root_.ModularForm in
private theorem ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₄ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₄,
      show (c • ⇑ModularForm.E₄) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₄_qExpansion_coeff_one]
  ring

theorem solution (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 :=
  ModularForm.levelOne_weight_four_qCoeff_one Y
