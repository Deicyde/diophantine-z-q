/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (git blob 0a9a271ceeb51ad5a786bbc796e00b71dfbcc499, sha256 33c929c9f6aab2c5fd25d5f51125d3b36f99b5e8d22f35341f9886ae1f7be433).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (y : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries L) = ModularCurve.jqModC L) :
    Module.finrank
        (IntermediateField.adjoin L
          ({y} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤ Γ'.index := by
  revert L Γ hT Γ' hΓ' hneg y hy
  exact @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.solution
