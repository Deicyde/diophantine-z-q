import NormalizationCenterV002
import CenterLocalizationV002
import NormalizationSemilocalV002
import SemilocalSeparatorV001
import ExtendedSpecV002

/-!
# Finite presentation of the actual extended valuation ring

A finite separable normalization over a DVR is semilocal Dedekind. Its selected
localization is a principal localization, so the selected valuation ring is
finitely presented over the original DVR even when it is not module-finite.
-/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Finite presentation of the literal base-to-extended-ring map, with no
finite-type or finite-normalization premise supplied by the caller. -/
theorem finite_separable_extended_finitePresentation [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    (baseHom O w hw).FinitePresentation := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  let C := integralClosure O M
  haveI : Module.Finite O C := (finite_separable_normalization (M := M) O).1
  haveI : Algebra.FinitePresentation O C := (finite_separable_normalization (M := M) O).2.1
  haveI : IsDedekindDomain C := (finite_separable_normalization (M := M) O).2.2.1
  haveI : IsFractionRing C M := (finite_separable_normalization (M := M) O).2.2.2
  haveI : IsDedekindDomain C.toSubring := inferInstanceAs (IsDedekindDomain C)
  haveI : IsFractionRing C.toSubring M := inferInstanceAs (IsFractionRing C M)
  haveI : Module.IsTorsionFree O M := .trans_faithfulSMul O K M
  haveI : Module.IsTorsionFree O C := IsIntegralClosure.isTorsionFree O M
  obtain ⟨hC, hq0, _⟩ := finite_separable_center_description O w hw
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  letI : Algebra C w := (Subring.inclusion hC).toAlgebra
  letI := extensionRingAlgebra O w hw
  haveI : IsScalarTower O C w := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq0 inferInstance
  haveI : IsLocalization.AtPrime w q :=
    dedekind_center_isLocalization C.toSubring w hC (extended_ne_top O w hw) hq0
  haveI : Algebra.FinitePresentation C w := semilocal_prime_finitePresentation
    (finite_maximal_normalization (R := O) (C := C)) q w
  change Algebra.FinitePresentation O w
  exact Algebra.FinitePresentation.trans O C w

/-- The original number-field case is finitely presented without a Henselian,
complete, excellent, or assumed-finiteness input. -/
theorem numberField_extended_finitePresentation [NumberField K] [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    (baseHom O w hw).FinitePresentation := finite_separable_extended_finitePresentation O w hw

universe u

/-- Finite presentation is bound to the actual native scheme map. -/
theorem finite_separable_spec_finitePresentation {K M : Type u} [Field K] [Field M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    AlgebraicGeometry.LocallyOfFinitePresentation
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (baseHom O w hw))) :=
  (AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff _).2
    (finite_separable_extended_finitePresentation O w hw)

end FiniteExtensionValuation
