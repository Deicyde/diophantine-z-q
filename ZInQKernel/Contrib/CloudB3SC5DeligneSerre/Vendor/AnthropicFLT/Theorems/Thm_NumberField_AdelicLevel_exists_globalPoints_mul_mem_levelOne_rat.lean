/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat (git blob 0992f0b1bca139bfd00d62426b078b68ea2a5c0c, sha256 8d6297e6b33d1e78f36dd502aa1166a51db71ca4c927fbe694b91806b182d819).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g
          ∈ NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ N ∧
        ∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ
                  (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * g)))
            ∈ Matrix.GLPos (Fin 2) ℝ := by
  revert N hN g
  exact @_root_.P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat.solution
