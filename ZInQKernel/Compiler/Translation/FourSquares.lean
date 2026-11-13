import Mathlib.NumberTheory.SumFourSquares

/-!
# Lagrange's four-square theorem

Every natural number is a sum of four squares of natural numbers (Mathlib's
`Nat.sum_four_squares`).

(Blueprint: `compiler/translation/lagrange-four-squares.md`.)
-/

namespace ZInQ.Translation

/-- **Lagrange's four-square theorem.** For every `n ∈ ℕ` there are `a₀, a₁, a₂, a₃ ∈ ℕ` with
`n = a₀² + a₁² + a₂² + a₃²`. -/
theorem four_squares (n : ℕ) : ∃ a₀ a₁ a₂ a₃ : ℕ, n = a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, h.symm⟩

end ZInQ.Translation
