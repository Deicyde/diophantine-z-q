import ZInQKernel.Contrib.HilbertDifferent.Local

/-!
# Closed local Hilbert statement and endpoint checks

The expected local type is independently spelled from the actual baseline.
The global target is a separate proposition and is not claimed here.
-/

open IsLocalRing Finset

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace ZInQ.Contrib.HilbertDifferent.LocalChecks

/-- Independent spelling of the LOCAL baseline leaf, including all its original hypotheses. -/
def expectedLocalHilbert : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, PkgI6.lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ range N, (Nat.card (PkgI6.lowerRam A B i) - 1))

/-- This compares the actual elaborated baseline statement, not just its name or prose. -/
theorem statement_agrees : expectedLocalHilbert ↔ PkgI6.HilbertDifferentFormula := Iff.rfl

/-- Exact closed independently spelled type, with no extra monogenicity or Hilbert-Fact premise. -/
theorem exact_closed_local_shape : expectedLocalHilbert := localHilbertDifferentFormula

/-- Under the original Galois fraction-field hypotheses, a trivial automorphism group has
the unit different and the exact witness `N=0`. No generator is assumed as an extra input. -/
theorem zero_witness_of_trivial_autGroup (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGalois (FractionRing A) (FractionRing B)] [Subsingleton (B ≃ₐ[A] B)] :
    (maximalIdeal B ^ (0 + 1)).inertia (B ≃ₐ[A] B) = ⊥ ∧
      differentIdeal A B = maximalIdeal B ^
        (∑ i ∈ range 0, (Nat.card ((maximalIdeal B ^ (i + 1)).inertia (B ≃ₐ[A] B)) - 1)) := by
  obtain ⟨N, _, hD⟩ := hilbertDifferentDVR A B
  have htrivial (i : ℕ) : (maximalIdeal B ^ (i + 1)).inertia (B ≃ₐ[A] B) = ⊥ :=
    Subsingleton.elim _ _
  have hunit : differentIdeal A B = ⊤ := by simpa [htrivial] using hD
  exact ⟨htrivial 0, by simpa using hunit⟩

end ZInQ.Contrib.HilbertDifferent.LocalChecks

#check @ZInQ.Contrib.HilbertDifferent.localHilbertDifferentFormula
#check @ZInQ.Contrib.HilbertDifferent.hilbertDifferentDVR
#print axioms ZInQ.Contrib.HilbertDifferent.integralClosure_of_finite_integrallyClosed
#print axioms ZInQ.Contrib.HilbertDifferent.finite_fractionRing_extension
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentDVR
#print axioms ZInQ.Contrib.HilbertDifferent.localHilbertDifferentFormula
#print axioms ZInQ.Contrib.HilbertDifferent.LocalChecks.exact_closed_local_shape
#print axioms ZInQ.Contrib.HilbertDifferent.LocalChecks.zero_witness_of_trivial_autGroup
#print axioms ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top
