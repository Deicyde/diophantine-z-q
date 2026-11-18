import ExtendedPresentationV002
import GenericFiberSpecV002
import Mathlib.FieldTheory.IntermediateField.Basic

/-! # Restricting the original valuation to an actual finite intermediate field -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The base-ring equality is inherited by literal restriction to an intermediate field. -/
theorem intermediate_restriction_comap (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (M : IntermediateField K Ω) :
    (w.comap (algebraMap M Ω)).comap (algebraMap K M) = O := by
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K M Ω]
  exact hw

/-- The original valuation, restricted to a finite intermediate field, has an
actual DVR class. No DVR class on the valuation ring of the whole closure is assumed. -/
theorem finite_intermediate_restriction_isDVR (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (M : IntermediateField K Ω)
    [FiniteDimensional K M] : IsDiscreteValuationRing (w.comap (algebraMap M Ω)) :=
  finite_extension_isDiscreteValuationRing O _ (intermediate_restriction_comap O w hw M)

/-- The original number-field valuation restricted to a finite point field has
an actual finitely presented local ring map over the base DVR. -/
theorem numberField_intermediate_restriction_finitePresentation [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (M : IntermediateField K Ω)
    [FiniteDimensional K M] :
    (baseHom O (w.comap (algebraMap M Ω)) (intermediate_restriction_comap O w hw M)).FinitePresentation :=
  numberField_extended_finitePresentation O _ (intermediate_restriction_comap O w hw M)

universe u

/-- The generic fiber of the actual restricted valuation ring is the native
spectrum of that same finite intermediate field. -/
theorem finite_intermediate_restriction_generic_fiber {K Ω : Type u}
    [Field K] [Field Ω] [Algebra K Ω] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (M : IntermediateField K Ω)
    [FiniteDimensional K M] :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (w.comap (algebraMap M Ω)).subtype))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K M)))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (baseHom O (w.comap (algebraMap M Ω)) (intermediate_restriction_comap O w hw M))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom O.subtype)) :=
  spec_generic_fiber_isPullback O _ (intermediate_restriction_comap O w hw M)

end FiniteExtensionValuation
