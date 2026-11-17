/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat (git blob 8a8c16aa201b81a69a38c83cfd65e67903e8b276, sha256 2a6ca20467a2f6bfac886aaf29c201fba1eff3eb90679689aa602b689365f643).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat

set_option autoImplicit false

noncomputable section

namespace M4aP1R
namespace LevelCoveringDecomp

open Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem exists_mem_productionPinsCompact_U_mul_eq_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      u ∈ (productionPinsCompact ℚ).U N ∧
        glFin (𝓞 ℚ) ℚ h = 1 ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  obtain ⟨γ, hmem, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := globalPoints (𝓞 ℚ) ℚ γ * g with hg'
  set u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g') with hu
  refine ⟨γ⁻¹, g' * u⁻¹, u, ?_, ?_, ?_, ?_⟩
  ·
    rw [productionPinsCompact_U, Subgroup.mem_inf, hu, AdelicDock.finEmbed_mem_levelOne_iff,
      mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
    exact ⟨(mem_levelOne_iff).mp hmem, rfl⟩
  ·
    rw [map_mul, map_inv, hu, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  ·
    intro w hw
    rw [map_mul, map_inv, hu, AdelicDock.glArch_finEmbed, inv_one, mul_one]
    exact hpos w hw
  ·
    rw [mul_assoc, inv_mul_cancel_right, map_inv, hg', inv_mul_cancel_left]

end M4aP1R.LevelCoveringDecomp

theorem solution
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
      (h u : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (AutomorphicForm.productionPinsCompact ℚ).U N ∧
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 ∧
        (∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * h * u := by
  first
    | exact M4aP1R.LevelCoveringDecomp.exists_mem_productionPinsCompact_U_mul_eq_rat_impl hN g
    | (apply M4aP1R.LevelCoveringDecomp.exists_mem_productionPinsCompact_U_mul_eq_rat_impl <;> assumption)
