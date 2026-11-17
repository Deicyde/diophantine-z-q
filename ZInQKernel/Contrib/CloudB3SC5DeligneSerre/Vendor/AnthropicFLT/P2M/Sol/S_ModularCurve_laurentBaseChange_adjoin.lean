/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_laurentBaseChange_adjoin (git blob cdba92d7b4a904ebb5b0e6633e8baba0142fd52d, sha256 aec836a691c8fe36253c95f9e896bfa84cd11f2adf609afd9e76dd872a47c64f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_laurentBaseChange_adjoin

open ModularCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hle : (IntermediateField.adjoin ℚ S).toSubfield ≤
        (IntermediateField.adjoin L (coeffEmb L '' S)).toSubfield.comap (coeffEmb L) := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨c, rfl⟩ | hx)
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
            = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
          rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
            ← algebraMap_laurentSeries_eq_single]
        rw [this]
        exact (IntermediateField.adjoin L (coeffEmb L '' S)).algebraMap_mem _
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    exact hle hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ S hy)
