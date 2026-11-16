/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_functionFieldGeneration
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve IntermediateField

theorem solution (K : Type*) [Field K] [CharZero K] (N : ℕ) [NeZero N] :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  refine le_antisymm (modularFunctionFieldC_le_full K N) ?_

  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro x ⟨d, hned, hdvd, rfl⟩
  haveI := hned

  rw [show qExpand K d (jqModC K) = coeffMap (algebraMap ℚ K) (qExpand ℚ d jq) from by
    rw [← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]]

  have hmem : qExpand ℚ d jq ∈ modularFunctionField N :=
    functionFieldGeneration N d hdvd ‹NeZero d›

  have hle : (modularFunctionField N).toSubfield ≤
      Subfield.comap (coeffMap (algebraMap ℚ K)) (modularFunctionFieldC K N).toSubfield := by
    rw [modularFunctionField]
    refine adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨c, rfl⟩
      show coeffMap (algebraMap ℚ K) (algebraMap ℚ (LaurentSeries ℚ) c) ∈
        (modularFunctionFieldC K N).toSubfield
      rw [algebraMap_laurentSeries_eq_single, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact (modularFunctionFieldC K N).algebraMap_mem _
    · rintro y (rfl | rfl)
      · show coeffMap (algebraMap ℚ K) jq ∈ (modularFunctionFieldC K N).toSubfield
        rw [← jqModC_rat, coeffMap_jqModC]
        exact jqModC_mem K N
      · show coeffMap (algebraMap ℚ K) (qExpand ℚ N jq) ∈
          (modularFunctionFieldC K N).toSubfield
        rw [← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]
        exact jqNModC_mem K N
  exact hle hmem
