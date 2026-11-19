/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC (git blob 049a0dd5d666723b0bb1956138468f520d576202, sha256 21180d40cd8489ff54f29f9c666c66698555fc8692d5217b0b42b71e0da05d4b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ Γ, Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ Γ)))
        (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  revert Γ hT
  exact @_root_.P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.solution
