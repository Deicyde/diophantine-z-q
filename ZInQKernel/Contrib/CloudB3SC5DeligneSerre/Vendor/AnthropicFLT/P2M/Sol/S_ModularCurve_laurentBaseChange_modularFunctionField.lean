/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionField (git blob ce7cdcd3c91b65b78a056b14ccd029f6d45daeb8, sha256 3b19b56dee8bee128e828f5d85614d6cd5f3f1951db628c56c9be4f26c11671c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_coeffEmb_jq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_coeffEmb_jqN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_laurentBaseChange_modularFunctionField

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionField N) = ModularCurve.modularFunctionFieldC L N := by
  apply le_antisymm
  ·

    change IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
      ≤ modularFunctionFieldC L N
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq} at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        rcases hx with rfl | rfl
        · rw [coeffEmb_jq]; exact jqModC_mem L N
        · rw [show qExpand ℚ N jq = jqN N from rfl, coeffEmb_jqN]; exact jqNModC_mem L N
    | algebraMap c =>
        have h : (coeffEmb L).comp (algebraMap ℚ (LaurentSeries ℚ))
            = (algebraMap L (LaurentSeries L)).comp (algebraMap ℚ L) := RingHom.ext_rat _ _
        have hc := congrArg (fun f : ℚ →+* LaurentSeries L => f c) h
        simp only [RingHom.coe_comp, Function.comp_apply] at hc
        simp only [SetLike.mem_coe, hc]
        exact (modularFunctionFieldC L N).algebraMap_mem _
    | add x y _ _ hx hy => simpa only [SetLike.mem_coe, map_add] using add_mem hx hy
    | inv x _ hx => simpa only [SetLike.mem_coe, map_inv₀] using inv_mem hx
    | mul x y _ _ hx hy => simpa only [SetLike.mem_coe, map_mul] using mul_mem hx hy
  ·
    change IntermediateField.adjoin L {jqModC L, jqNModC L N}
      ≤ IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
    apply IntermediateField.adjoin.mono
    rintro _ (rfl | rfl)
    · exact ⟨jq, jq_mem N, coeffEmb_jq L⟩
    · exact ⟨qExpand ℚ N jq, jqN_mem N, coeffEmb_jqN L N⟩
