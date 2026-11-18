import NormalizationLocalDataV001
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Residue extensions and infinitesimal quotients at the selected place -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The residue extension at the actual selected place is finite. This is
produced from the normalization and its actual localization, not assumed. -/
theorem finite_separable_residue_extension [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionRingAlgebra O w hw
    letI : IsLocalHom (algebraMap O w) := baseHom_isLocalHom O w hw
    FiniteDimensional (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := by
  letI := extensionRingAlgebra O w hw
  letI : IsLocalHom (algebraMap O w) := baseHom_isLocalHom O w hw
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  let C := integralClosure O M
  haveI : Module.Finite O C := (finite_separable_normalization (M := M) O).1
  obtain ⟨hC, hq0, hqm, hloc⟩ := finite_separable_center_localization O w hw
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  letI : q.IsMaximal := hqm
  letI : Algebra C w := (Subring.inclusion hC).toAlgebra
  letI : IsLocalization.AtPrime w q := hloc
  haveI : IsScalarTower O C w := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : (C ⧸ q) ≃ₐ[C] IsLocalRing.ResidueField w :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q w
  haveI : Module.Finite O (C ⧸ q) := inferInstance
  haveI : Module.Finite O (IsLocalRing.ResidueField w) :=
    Module.Finite.of_surjective (e.toLinearMap.restrictScalars O) e.surjective
  exact Module.Finite.of_restrictScalars_finite O (IsLocalRing.ResidueField O)
    (IsLocalRing.ResidueField w)

/-- Localization at the actual center preserves every infinitesimal quotient,
including the zero-th quotient. -/
theorem finite_separable_normalization_thickenings [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    ∃ hC : (integralClosure O M).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧
        letI := (Subring.inclusion hC).toAlgebra
        ∀ n : ℕ, Nonempty (((integralClosure O M) ⧸ q ^ n) ≃ₐ[integralClosure O M]
          (w ⧸ IsLocalRing.maximalIdeal w ^ n)) := by
  letI := extensionFieldAlgebra (M := M) O
  obtain ⟨hC, hq0, hqm, hloc⟩ := finite_separable_center_localization O w hw
  let C := integralClosure O M
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  letI : q.IsMaximal := hqm
  letI : Algebra C w := (Subring.inclusion hC).toAlgebra
  letI : IsLocalization.AtPrime w q := hloc
  exact ⟨hC, hq0, fun n => ⟨IsLocalization.AtPrime.equivQuotMaximalIdealPow q w n⟩⟩

end FiniteExtensionValuation
