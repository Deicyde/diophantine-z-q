import ZInQKernel.Contrib.OneProof.SZThm33.SemistableCriterionForward
import ZInQKernel.Contrib.OneProof.SZThm33.SilverbergZarhinReverse

noncomputable section

open scoped CategoryTheory.MonObj

namespace SZRaynaud

/-- Silverberg–Zarhin, Theorem 3.3 (p. 405), in the project's absolute-inertia
form. For the chosen valuation on an algebraic closure, semistable reduction is
equivalent to inertia acting trivially on the rational Tate module modulo its
invariants. The reverse implication uses the eventual semistable reduction
hypothesis in `SilverbergZarhinThm33`. -/
theorem silverbergZarhinThm33_proof : SilverbergZarhinThm33 := by
  intro K _ O _ Ω _ _ _ w hw A ℓ _ hℓ hpot
  exact ⟨levelTwo_of_semistableReductionSZ K O Ω w hw A ℓ hℓ,
    silverbergZarhinThm33_reverse K O Ω w hw A ℓ hℓ hpot⟩

end SZRaynaud
