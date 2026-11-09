import ZInQ.BinomialDigit

/-!
# Binomial coefficients as base-`B` digits

Blueprint: `compiler/natural/exponential/binomial-digit.md`.

With `β = 2^(N+1)`, the `K`-th base-`β` digit of `(β + 1)^N` is `C(N, K)`. The witnesses are
`β, τ, π, q, r` in the compiler's order, and the total is written `(β + 1)^N` as the compiler
emits it; upstream's `ZInQ.BinomialDigit.macro_holds_iff_choose` writes `(1 + β)^N`.
-/

namespace ZInQ

/-- `C = C(N, K)` iff `C` is the `K`-th base-`2^(N+1)` digit of `(2^(N+1) + 1)^N`, witnessed by
`β = 2^(N+1)`, `τ = (β+1)^N`, `π = β^K` and a division `τ = π(βq + C) + r` with `C < β`,
`r < π`. -/
theorem binomial_digit_iff_choose (C N K : ℕ) :
    (∃ β τ π q r : ℕ, β = 2 ^ (N + 1) ∧ τ = (β + 1) ^ N ∧ π = β ^ K ∧ C < β ∧ r < π ∧
      τ = π * (β * q + C) + r) ↔ C = Nat.choose N K := by
  rw [← BinomialDigit.macro_holds_iff_choose, BinomialDigit.macroHolds]
  simp only [Nat.add_comm _ 1]

end ZInQ
