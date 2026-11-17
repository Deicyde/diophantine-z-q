/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (git blob af881e4e3c507635663deec21a638a9e1390110b, sha256 f0039b2bf78d51afcafd888fabbb7c23a6c3b5ba87926d320eaa711ad5ffeae5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ,
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
      Transcendental (IsLocalRing.ResidueField A) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ∧
      ∀ (y : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        (y : LaurentSeries L) = ModularCurve.jqModC L →
        Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
            (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) ≤
          Module.finrank
            (IntermediateField.adjoin L
              ({y} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
            (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by
  revert L A Γ hT
  exact @_root_.P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.solution
