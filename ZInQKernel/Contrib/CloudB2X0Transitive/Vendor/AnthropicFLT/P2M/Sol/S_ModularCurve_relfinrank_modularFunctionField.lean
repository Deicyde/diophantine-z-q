/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_relfinrank_modularFunctionField
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
namespace P2MW.S_ModularCurve_relfinrank_modularFunctionField

namespace ModularCurve p2m_export "ModularCurve" "qExpand jq jqN modularFunctionField adjoin_jq_le" end ModularCurve
p2m_open_scoped "ModularCurve" in
open IntermediateField in
private theorem ModularCurve.relfinrank_modularFunctionField (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionField N) =
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) := by
  have key : extendScalars (ModularCurve.adjoin_jq_le N) =
      adjoin (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ)) := by
    have key0 := extendScalars_adjoin (ModularCurve.adjoin_jq_le N)
    refine key0.trans (le_antisymm ?_ ?_)
    · rw [adjoin_le_iff, Set.insert_subset_iff]
      refine ⟨?_, Set.singleton_subset_iff.mpr (subset_adjoin _ _ rfl)⟩
      exact (adjoin _ _).algebraMap_mem
        (⟨jq, subset_adjoin ℚ _ rfl⟩ : ↥(adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
    · exact adjoin.mono _ _ _ (Set.subset_insert _ _)
  rw [relfinrank_eq_finrank_of_le (ModularCurve.adjoin_jq_le N), key]

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_relfinrank_modularFunctionField.ModularCurve in

theorem solution (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionField N) = Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) :=
  ModularCurve.relfinrank_modularFunctionField N

#print axioms solution
