import ExtendedRingMapsV003
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Native spectra, fraction fields, and the generic open of extended valuation rings -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace FiniteExtensionValuation

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- The original field inclusions and the actual local ring map induce a commuting
square of native scheme morphisms. -/
theorem spec_fraction_field_square (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom (baseHom O w hw)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫ Spec.map (CommRingCat.ofHom O.subtype) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The selected closed point is sent to the original closed point. -/
theorem spec_closed_point (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    Spec.map (CommRingCat.ofHom (baseHom O w hw)) (IsLocalRing.closedPoint w) =
      IsLocalRing.closedPoint O := by
  letI : IsLocalHom (CommRingCat.ofHom (baseHom O w hw)).hom := baseHom_isLocalHom O w hw
  exact Spec_closedPoint

/-- The fraction-field inclusion of this DVR is a finitely presented ring map. -/
theorem generic_inclusion_finitePresentation (w : ValuationSubring M)
    [IsDiscreteValuationRing w] : w.subtype.FinitePresentation := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w
  letI := fraction_field_away w hπ
  change (algebraMap w M).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation π

/-- The fraction-field inclusion is the actual generic open immersion. -/
theorem spec_generic_open (w : ValuationSubring M) [IsDiscreteValuationRing w] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom w.subtype)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w
  letI := fraction_field_away w hπ
  exact IsOpenImmersion.of_isLocalization π

/-- The native generic open is locally of finite presentation. -/
theorem spec_generic_finitePresentation (w : ValuationSubring M)
    [IsDiscreteValuationRing w] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom w.subtype)) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).2 (generic_inclusion_finitePresentation w)

/-- The generic-open tests require no assumed structure on the extended ring. -/
theorem finite_extension_generic_tests [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom w.subtype)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom w.subtype)) := by
  letI := finite_extension_isDiscreteValuationRing O w hw
  exact ⟨spec_generic_open w, spec_generic_finitePresentation w⟩

end FiniteExtensionValuation
