/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension (git blob 0333d8ded322585099af9ae7ec11feb6846d61ee, sha256 1efa3a7af2adc3962a9b69328507590e2081ac41e4b15ff1afe7b555b66d30f9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) (P Q : Place E FE)
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1)
    (hQ : ∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    P = Q := by
  revert K F hfg E FE hfgE hgen e P Q hP hQ
  exact @_root_.P2MW.S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.solution
