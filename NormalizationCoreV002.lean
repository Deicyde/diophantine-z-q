import ExtendedRingMapsV003
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Valuation.Integral

/-!
# Finite separable normalization over the actual valuation ring

The normalization is finite by the trace-dual-lattice theorem. Separability is
used only for this finiteness argument, not for the extended DVR theorem.
-/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Integral elements over the actual base ring belong to every extended valuation ring. -/
theorem normalization_le (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    (integralClosure O M).toSubring ≤ w.toSubring := by
  letI := extensionFieldAlgebra (M := M) O
  haveI : IsFractionRing w.toSubring M := inferInstanceAs (IsFractionRing w M)
  haveI : IsIntegrallyClosed w.toSubring := (ValuationRing.integers w M).isIntegrallyClosed
  haveI : IsIntegrallyClosedIn w.toSubring M :=
    (isIntegrallyClosed_iff_isIntegralClosure M).1 inferInstance
  apply Subring.integralClosure_le_iff.2
  intro a
  change algebraMap K M (a : K) ∈ w
  have h : (a : K) ∈ w.comap (algebraMap K M) := by simpa only [hw] using a.2
  exact h

/-- Finiteness, finite presentation, normality, and the fraction field of the
entire normalization in a finite separable extension. -/
theorem finite_separable_normalization [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    letI := extensionFieldAlgebra (M := M) O
    Module.Finite O (integralClosure O M) ∧
      Algebra.FinitePresentation O (integralClosure O M) ∧
      IsDedekindDomain (integralClosure O M) ∧
      IsFractionRing (integralClosure O M) M := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  letI : Module.Finite O (integralClosure O M) :=
    IsIntegralClosure.finite O K M (integralClosure O M)
  have hfp : Algebra.FinitePresentation O (integralClosure O M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact ⟨inferInstance, hfp, integralClosure.isDedekindDomain O K M,
    integralClosure.isFractionRing_of_finite_extension K M⟩

/-- The number-field case needs no excellence or finite-normalization premise:
finite extensions are separable in characteristic zero. -/
theorem numberField_normalization [NumberField K] [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    letI := extensionFieldAlgebra (M := M) O
    Module.Finite O (integralClosure O M) ∧
      Algebra.FinitePresentation O (integralClosure O M) ∧
      IsDedekindDomain (integralClosure O M) ∧
      IsFractionRing (integralClosure O M) M :=
  finite_separable_normalization O

end FiniteExtensionValuation
