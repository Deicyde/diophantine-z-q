import Mathlib

/-!
# Hypothesis PC: pole completeness

Theorem 5.2 (`hyp:PC`) of the 11/5 manuscript. The manuscript derives it from the
restricted converse theorem (Theorem 5.3, `hyp:RC`), whose proof occupies Sections 7–9
and Appendices E–G and uses Kato's Euler system, Waldspurger's formula,
Bump–Friedberg–Hoffstein, Nekovář's Selmer complexes and Gross–Zagier–Kolyvagin.
The statement itself concerns the rational solubility of one explicit polynomial, so it
enters the main theorem as an explicit hypothesis.
-/

namespace ZInQ

open scoped BigOperators

/-- The exceptional primes `S₀ = {2, 3, 5, 7, 13}` of the pole predicate. -/
def poleS0 : Finset ℕ := {2, 3, 5, 7, 13}

/-- The pole polynomial `Q_pole` of Section 5, evaluated at the input `B` and its eleven
witnesses `b₀, …, b₅, e, z, r₁, r₂, w`. -/
def polePoly (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) : ℚ :=
  let m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5)
  let A := m * B
  let H := A * (A - B ^ 2)
  let T₁ := A * (A - e) * (A + 3 * e)
  let T₂ := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H)
  B * ((∑ i, (b i ^ 2 - b i) ^ 2) + (e * H * z * w - 1) ^ 2 + (r₁ ^ 2 - T₁) ^ 2 +
    (r₂ ^ 2 - T₂) ^ 2)

/-- `Φ(B)`: the pole polynomial has a rational zero with input `B`. -/
def PoleSoluble (B : ℚ) : Prop :=
  ∃ (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ), polePoly B b e z r₁ r₂ w = 0

/-- **Hypothesis PC** (Theorem 5.2, pole completeness). Every rational `B` with square
reduced denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` for every `p ∈ S₀` satisfies `Φ(B)`. -/
def PoleCompleteness : Prop :=
  ∀ B : ℚ, IsSquare B.den → 0 < B → B < 1 / 2 → (∀ p ∈ poleS0, 4 ≤ padicValRat p B) →
    PoleSoluble B

end ZInQ
