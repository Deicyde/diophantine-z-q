/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_E4_cube_div_discriminant_smul
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_E4_cube_div_discriminant_smul

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial
open scoped MatrixGroups ModularForm OnePoint

namespace ModularCurve

theorem E4_cube_div_discriminant_smul' (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE : ModularForm.E₄ (γ • τ) = denom (mapGL ℝ γ) τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) hγ τ
  have hΔ : ModularForm.discriminant (γ • τ)
      = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
    simp only [CuspForm.coe_discriminant] at this
    exact this
  have hd : denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [hE, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  norm_num
  first
  | rw [mul_div_mul_left _ _ (zpow_ne_zero 12 hd)]
  | rw [mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

end ModularCurve

end

theorem solution (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ) = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ :=
  ModularCurve.E4_cube_div_discriminant_smul' γ τ
