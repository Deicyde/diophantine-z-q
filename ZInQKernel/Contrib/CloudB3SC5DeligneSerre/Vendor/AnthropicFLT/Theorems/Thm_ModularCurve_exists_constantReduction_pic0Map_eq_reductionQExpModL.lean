/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL (git blob 6bf750650b3b7c2c1a7b1d6e86adb00b84181301, sha256 ebf7e5692b66552023f936f35ebaae4b898b231c39c8251d507a1acc06f9e46d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ConstantReduction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsQExpModL A Γ) :
    ∃ R : ConstantReduction A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      R.placeMap = ModularCurve.placeReductionQExpModL h ∧
      R.pic0Map = ModularCurve.reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
              ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ := by
  revert Γ hT A h
  exact @_root_.P2MW.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.solution
