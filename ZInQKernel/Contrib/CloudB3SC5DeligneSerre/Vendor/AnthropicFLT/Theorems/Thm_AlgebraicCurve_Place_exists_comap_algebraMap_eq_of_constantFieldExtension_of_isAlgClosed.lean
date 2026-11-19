/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed (git blob 3b260290746ca8a6f28d2ffee45fb9c6b396b75d, sha256 55bacbc6a8a7aa08b156c4f5de486ec1f8bcfe1b7bc7033dbbda7edb70a5ff08).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : Place K F) :
    ∃ P' : Place K' F',
      P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, P'.ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q' = P' := by
  revert K F K' F' hfg hfg' hgen P
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed.solution
