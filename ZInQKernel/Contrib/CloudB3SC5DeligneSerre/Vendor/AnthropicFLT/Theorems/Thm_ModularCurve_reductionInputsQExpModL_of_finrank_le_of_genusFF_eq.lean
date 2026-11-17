/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq (git blob f4c5a58d7cedb4994555290bbe50890e21134c80, sha256 fd588f9dd8d9f6fa9c6a87cfeef387e19a8fb7ba9ecac279a3d4e6eb85d2e2bf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hdeg : ∀ (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)
      (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) →
      (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ))
    (hgen : AlgebraicCurve.genusFF (IsLocalRing.ResidueField A)
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    ModularCurve.ReductionInputsQExpModL A Γ := by
  revert Γ hT A hdeg hgen
  exact @_root_.P2MW.S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq.solution
