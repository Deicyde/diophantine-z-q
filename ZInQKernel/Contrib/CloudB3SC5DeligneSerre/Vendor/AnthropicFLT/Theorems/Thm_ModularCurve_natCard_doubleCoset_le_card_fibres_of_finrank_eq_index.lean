/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index (git blob 346e9cbdaec3baa0ff61461717590db62ec28f0a, sha256 fe3542ca3246ba344d3bb2bf4c4c754e3be3be270e999867e641db3ac513e876).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups

theorem ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) =
        (Γ ⊔ Subgroup.zpowers (-1)).index) :
    Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord y} ∧
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord (y - 1728)} ∧
      Nat.card (DoubleCoset.Quotient (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
              Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ≤
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            P.ord y < 0} := by
  revert M Γ hΓ y hy hfull
  exact @_root_.P2MW.S_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.solution
