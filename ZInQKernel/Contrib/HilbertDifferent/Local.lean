import ZInQKernel.Contrib.HilbertDifferent.IntegralClosure
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.Contrib.Herbrand.Monogenic

/-!
# Hilbert's formula for the actual local-DVR leaf

This module proves `PkgI6.HilbertDifferentFormula`, not the distinct GLOBAL
`GlueConductor.HilbertDifferentFormula`. The original eight-module global partial
is unchanged. The monogenicity supplier is the separately authored contribution
`ZInQKernel.Contrib.Herbrand.Monogenic`, frozen SHA-256
`a2b761efd76e4ee50a00d277824f943ee34b4f617c273df0d17faf5a8b68e24d`.
Its exact exported wrapper is `ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top`.
The present proof uses that result; it does not copy or alter the supplier.

The finite-DVR structural inputs to the generic integral-closure Hilbert theorem
are derived here. Completeness is not needed by the stronger DVR helper, but the
closed local leaf retains every hypothesis of the actual baseline proposition.
The shared import must be integrated as tracked source/a stack dependency before
claiming a production-tree build. Private-overlay compilation is not that claim.
-/

open IsLocalRing Finset

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace ZInQ.Contrib.HilbertDifferent

/-- A module-finite extension with integrally closed upstairs domain realizes its integral
closure inside the upstairs fraction field. This is a proved structural input, not a leaf axiom. -/
theorem integralClosure_of_finite_integrallyClosed (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] :
    IsIntegralClosure B A (FractionRing B) :=
  IsIntegralClosure.of_isIntegrallyClosed B A (FractionRing B)

/-- Finite integral extensions induce finite extensions of the canonical fraction fields.
The explicit proof uses integral closure/localization and the existing module-finite theorem. -/
theorem finite_fractionRing_extension (A B : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B] :
    Module.Finite (FractionRing A) (FractionRing B) := by
  let : IsIntegralClosure B A (FractionRing B) := integralClosure_of_finite_integrallyClosed A B
  let : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B (FractionRing A) (FractionRing B)
  let : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization A (FractionRing A) (FractionRing B) B
  exact Module.Finite.of_isLocalization A B (nonZeroDivisors A)

/-- The baseline's lower groups are exactly the same power-ideal inertia groups used in the
generic Hilbert theorem. In particular there is no index shift or change of acting group. -/
theorem lowerRam_eq_powerInertia (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] (i : ℕ) :
    PkgI6.lowerRam A B i = (maximalIdeal B ^ (i + 1)).inertia (B ≃ₐ[A] B) := rfl

/-- Hilbert's ideal equality for finite torsion-free DVR extensions with perfect base residue
field and Galois fraction fields. This stronger helper has no completeness assumption. -/
theorem hilbertDifferentDVR (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGalois (FractionRing A) (FractionRing B)] :
    ∃ N : ℕ, (maximalIdeal B ^ (N + 1)).inertia (B ≃ₐ[A] B) = ⊥ ∧
      differentIdeal A B = maximalIdeal B ^
        (∑ i ∈ range N, (Nat.card ((maximalIdeal B ^ (i + 1)).inertia (B ≃ₐ[A] B)) - 1)) := by
  let : IsIntegralClosure B A (FractionRing B) := integralClosure_of_finite_integrallyClosed A B
  let : Module.Finite (FractionRing A) (FractionRing B) := finite_fractionRing_extension A B
  obtain ⟨β, hβ⟩ := ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top (A := A) (B := B)
  let P : Ideal B := maximalIdeal B
  have hP : P ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hPunit : ¬ IsUnit P := fun h ↦ hPtop (Ideal.isUnit_iff.mp h)
  obtain ⟨N, hN, hdiv, hnext⟩ :=
    hilbertDifferentAt_integralClosure_of_monogenic A (FractionRing A) (FractionRing B) B
      β hβ P hP
  have hD : differentIdeal A B ≠ ⊥ := by
    intro hz
    exact hnext (by rw [hz]; exact dvd_zero _)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hk
  change differentIdeal A B = P ^ k at hk
  rw [hk, pow_dvd_pow_iff hP hPunit] at hdiv hnext
  have hkN : k = ∑ i ∈ range N, (Nat.card ((P ^ (i + 1)).inertia (B ≃ₐ[A] B)) - 1) := by omega
  rw [hkN] at hk
  exact ⟨N, hN, hk⟩

/-- The exact closed LOCAL leaf, with no extra explicit, implicit, section or `Fact` hypothesis.
This is not a provider for the different GLOBAL T20 proposition. -/
theorem localHilbertDifferentFormula : PkgI6.HilbertDifferentFormula := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _
  simpa only [lowerRam_eq_powerInertia] using hilbertDifferentDVR A B

end ZInQ.Contrib.HilbertDifferent
