import ZInQKernel.Contrib.FrobeniusDensity.FiniteDensity
import ZInQKernel.Contrib.FrobeniusDensity.ValuationRealization
import ZInQKernel.Contrib.FrobeniusDensity.Topology

/-!
# T18: absolute arithmetic Frobenius elements, with finite-set avoidance

The finite density theorem is proved by the scoped Tau Ceti port. The prime
is chosen above the maximum of the entire finite exclusion set. Finite
arithmetic Frobenius lifts to the same absolute automorphism at an actual
valuation, and its restriction is exactly the one prescribed by `sigma`.
Nonnormal open subgroups are covered by the finite normal fixing-subgroup lemma.
This file neither imports nor registers the unreviewed H-target extraction.
-/

namespace ZInQ.Contrib.FrobeniusDensity

/-- Frobenius density in the exact valuation/restriction orientation required
by the proposed T18 statement, including avoidance of any finite set of primes. -/
theorem frobenius_dense_avoiding_finite_set :
    ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
      ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
        LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U := by
  intro U hU σ S
  obtain ⟨E, hE, hG, hEU⟩ := exists_finiteGalois_fixingSubgroup_le U hU
  have : FiniteDimensional ℚ E := hE
  have : IsGalois ℚ E := hG
  have : NumberField E := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hFrob⟩ :=
    exists_finite_arithFrob_avoiding E S (AlgEquiv.restrictNormal σ E)
  have : Q.IsPrime := hQ
  obtain ⟨v, τ, hv, hτ, hres⟩ :=
    valuation_frobLift E (AlgEquiv.restrictNormal σ E) p Q hp hQp hQu hFrob
  exact ⟨p, hp, hpS, v, τ, hv, hτ,
    inv_mul_mem_of_restrictNormal_eq U E hEU τ σ hres⟩

/-- The faithful, locally defined closed T18 proposition is discharged.
This is not registration or acceptance of the draft H targets. -/
theorem t18_holds : T18 := frobenius_dense_avoiding_finite_set

end ZInQ.Contrib.FrobeniusDensity
