import ZInQKernel.Contrib.OneProof.SZThm33.ResidueSemistabilityDescent
import ZInQKernel.Contrib.OneProof.SZThm33.SemistableComparisonReverse

/-! The reverse implication of Silverberg–Zarhin Theorem 3.3. -/

noncomputable section

open CategoryTheory AlgebraicGeometry ReductSplit

namespace SZRaynaud

/-- The inertia condition in Theorem 3.3 implies semistable reduction over
the original valuation ring. -/
theorem silverbergZarhinThm33_reverse
    (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O))
    (hpot : HasSemistableReductionSZ A O ∨
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
        IsDiscreteValuationRing (w.comap (algebraMap E Ω)) ∧
        HasSemistableReductionSZ (A.baseChange E) (w.comap (algebraMap E Ω)))
    (hI : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x) :
    HasSemistableReductionSZ A O :=
  silverbergZarhinThm33_reverse_of_geometric_descent K O Ω w hw A ℓ hℓ
    isSemistableResT_of_geometric hpot hI

#print axioms silverbergZarhinThm33_reverse

end SZRaynaud
