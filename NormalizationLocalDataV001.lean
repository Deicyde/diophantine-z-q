import NormalizationCenterV002
import CenterLocalizationV002

/-! # Typed localization data for the actual normalization and selected place -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The center is an actual nonzero maximal ideal, and the selected valuation
ring is its localization for the literal inclusion from the normalization. -/
theorem finite_separable_center_localization [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    ∃ hC : (integralClosure O M).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧ q.IsMaximal ∧
        letI := (Subring.inclusion hC).toAlgebra
        IsLocalization.AtPrime w q := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  let C := integralClosure O M
  haveI : IsDedekindDomain C := (finite_separable_normalization (M := M) O).2.2.1
  haveI : IsFractionRing C M := (finite_separable_normalization (M := M) O).2.2.2
  haveI : IsDedekindDomain C.toSubring := inferInstanceAs (IsDedekindDomain C)
  haveI : IsFractionRing C.toSubring M := inferInstanceAs (IsFractionRing C M)
  obtain ⟨hC, hq0, _⟩ := finite_separable_center_description O w hw
  have hqm : ((IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq0 inferInstance
  refine ⟨hC, hq0, hqm, ?_⟩
  exact dedekind_center_isLocalization C.toSubring w hC (extended_ne_top O w hw) hq0

end FiniteExtensionValuation
