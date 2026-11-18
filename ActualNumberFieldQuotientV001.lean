import ActualNumberFieldDivisionV001

/-!
# The original number-field action has its actual continuous finite quotient

The quotient topology is the genuine quotient of the Krull topology.
Finiteness is supplied by native geometric torsion finiteness, not a
caller hypothesis. The quotient equivalence is actual field restriction.
-/

noncomputable section
set_option autoImplicit false

namespace ActualNumberFieldQuotient
open ActualFiniteLevel ActualDivisionField ActualPrimePowerDivision
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

def actualQuotient (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ((Ω ≃ₐ[K] Ω) ⧸ (action A (ℓ ^ n)).ker) ≃ₜ*
      (divisionFieldLevel (Ω := Ω) A ℓ n ≃ₐ[K] divisionFieldLevel (Ω := Ω) A ℓ n) :=
  continuousQuotientEquiv A (ℓ ^ n)

lemma actualQuotient_finite (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Finite ((Ω ≃ₐ[K] Ω) ⧸ (action A (ℓ ^ n)).ker) := quotient_finite A (ℓ ^ n)

lemma actualQuotient_is_restriction (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) :
    (actualQuotient A ℓ n).toMulEquiv (QuotientGroup.mk σ) = restriction A (ℓ ^ n) σ := rfl

end ActualNumberFieldQuotient

set_option pp.universes true
#check @ActualNumberFieldQuotient.actualQuotient
#check @ActualNumberFieldQuotient.actualQuotient_finite
#check @ActualNumberFieldQuotient.actualQuotient_is_restriction
#print axioms ActualNumberFieldQuotient.actualQuotient
#print axioms ActualNumberFieldQuotient.actualQuotient_finite
#print axioms ActualNumberFieldQuotient.actualQuotient_is_restriction
