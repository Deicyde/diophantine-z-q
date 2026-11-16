import Mathlib.Tactic
import ZInQKernel.Contrib.OneProof.LegendreThreeSquares.Atlas

/-!
# `hL3s`: Legendre's three-square theorem, IF direction

This upstream module proves the full expanded statement of
`ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares` from the fork.
The H29 defining module is not yet accepted on upstream main; this file does not
copy or redefine that proposition or claim its integration into the headline.
It exports the same public theorem name with exactly the expanded quantifiers.

The genuine Ankeny proof is vendored from the public `facebookresearch/atlas-lean` repository at
`8860f7b55276b96e51df600021845dd5eb48f5ab`; its source, complete license and change notices are in
`ThirdParty/LegendreThreeSquares/`. It uses only the project's unchanged Mathlib 4.35 dependency.

The bridge below converts the excluded-form predicate to its logically equivalent negated
existential, then casts the natural witnesses to integers and reverses the equation. It has no
additional assumptions, including no positivity or squarefree restriction on `n`.
-/

namespace ZInQ.Contrib.OneProof.LegendreThreeSquares

/-- The exact, unconditional `hL3s` proposition, including `n = 0`. -/
theorem legendreThreeSquares_proof :
    ∀ n : ℕ, (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
      ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 := by
  intro n hn
  have hnot : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
    rintro ⟨a, b, hab⟩
    exact hn a b hab
  obtain ⟨x, y, z, hxyz⟩ :=
    Atlas.Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven n hnot
  refine ⟨(x : ℤ), (y : ℤ), (z : ℤ), ?_⟩
  exact_mod_cast hxyz.symm

end ZInQ.Contrib.OneProof.LegendreThreeSquares
