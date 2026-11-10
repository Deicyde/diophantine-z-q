import ChallengeDeps
import Submission.Helpers

open LeanEval.NumberTheory

namespace Submission

theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  refine
    GreenTao.containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms
      ?_ GreenTao.hasStandardCyclicMajorantLinearForms
  intro k hk
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact
    GreenTao.hasUniformOrderedPatternRemoval_sourceFull
      k (k - 2) (by omega)

end Submission
