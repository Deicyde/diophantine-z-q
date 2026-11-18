import NonzeroCenterV002
import NormalizationCenterV002
import CenterLocalizationV002

/-! # Global number rings and the selected local valuation ring -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {F : Type*} [Field F]

/-- A nontrivial valuation ring of a number field is the actual localization of
the global ring of integers at its nonzero maximal center. -/
theorem numberField_integer_place_description [NumberField F]
    (w : ValuationSubring F) (hw : w ≠ ⊤) :
    ∃ hC : (integralClosure ℤ F).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧ q.IsMaximal ∧
        letI := (Subring.inclusion hC).toAlgebra
        IsLocalization.AtPrime w q := by
  let C := integralClosure ℤ F
  haveI : IsDedekindDomain C := inferInstanceAs (IsDedekindDomain (NumberField.RingOfIntegers F))
  haveI : IsFractionRing C F := inferInstanceAs (IsFractionRing (NumberField.RingOfIntegers F) F)
  haveI : IsDedekindDomain C.toSubring := inferInstanceAs (IsDedekindDomain C)
  haveI : IsFractionRing C.toSubring F := inferInstanceAs (IsFractionRing C F)
  haveI : IsFractionRing w.toSubring F := inferInstanceAs (IsFractionRing w F)
  haveI : IsIntegrallyClosed w.toSubring := (ValuationRing.integers w F).isIntegrallyClosed
  haveI : IsIntegrallyClosedIn w.toSubring F :=
    (isIntegrallyClosed_iff_isIntegralClosure F).1 inferInstance
  have hC : C.toSubring ≤ w.toSubring := by
    apply Subring.integralClosure_le_iff.2
    intro n
    change (n : F) ∈ w
    exact intCast_mem w n
  have hq0 := center_ne_bot_of_ne_top C.toSubring w hC hw
  have hqm : ((IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq0 inferInstance
  exact ⟨hC, hq0, hqm, dedekind_center_isLocalization C.toSubring w hC hw hq0⟩

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- In the original number-field finite-extension case, the selected ring is a
localization of the extension's global number ring, not its whole number ring. -/
theorem numberField_extended_integer_place [NumberField K] [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    ∃ hC : (integralClosure ℤ M).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧ q.IsMaximal ∧
        letI := (Subring.inclusion hC).toAlgebra
        IsLocalization.AtPrime w q := by
  letI : NumberField M := NumberField.of_module_finite K M
  exact numberField_integer_place_description w (extended_ne_top O w hw)

end FiniteExtensionValuation
