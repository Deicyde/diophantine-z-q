/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_functionFieldGeneration_iff_full_eq
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq

open ModularCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N :=by
  constructor
  · intro hgen
    refine le_antisymm ?_ (modularFunctionField_le_full N)
    rw [modularFunctionFieldFull, adjoin_le_iff]
    rintro x ⟨d, hne, hdvd, rfl⟩
    exact hgen d hdvd hne
  · intro heq d hdvd hne
    haveI := hne
    show qExpand ℚ d jq ∈ modularFunctionField N
    rw [← heq]
    exact jqd_mem_full N hdvd

end
