import Mathlib

/-!
# Hypotheses 22P and CAT: prime patterns and the catalogue

Proposition 6.2 (`prop:fixed-prime-pattern`) of the 11/5 manuscript is proved with the
Green–Tao asymptotic for linear equations in primes, the Möbius–nilsequences theorem and
the inverse theorem for the Gowers norms (Green–Tao–Ziegler). Proposition 12.1
(`prop:cutoff`) bounds the catalogue with the explicit progression estimate of Bennett,
Martin, O'Bryant and Rechnitzer. Neither input is in Mathlib; both conclusions are
elementary statements about integers, so they enter the main theorem as explicit
hypotheses.
-/

namespace ZInQ

open scoped BigOperators

/-- `W = 4 P_s`, where `P_s = 324#` is the product of the primes at most `324`. -/
def catalogueModulus : ℕ := 4 * primorial 324

/-- The `i`-th prime greater than `324` in the residue class `r` modulo `W`, counting from `0`. -/
noncomputable def cataloguePrime (r i : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ 324 < p ∧ p % catalogueModulus = r) i

/-- `𝓗`: the first twenty-two primes greater than `324` in each unit residue class modulo `W`. -/
def catalogueSet : Set ℕ :=
  {h | ∃ r i, r < catalogueModulus ∧ Nat.Coprime r catalogueModulus ∧ i < 22 ∧
    h = cataloguePrime r i}

/-- `𝓚 = {d h : d ∣ P_s⁴, d > 0, h ∈ 𝓗}`. -/
def catalogueMultipliers : Set ℕ :=
  {k | ∃ d h, d ∣ primorial 324 ^ 4 ∧ 0 < d ∧ h ∈ catalogueSet ∧ k = d * h}

/-- The number of points of `y² = x³ + a x` over `ZMod p`, counting the point at infinity. -/
noncomputable def pointCount (p : ℕ) (a : ZMod p) : ℕ :=
  Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1} + 1

/-- The conditions of Proposition 6.2 on a prime `p`: it splits in `ℚ(√2)`, both reductions
of `E : y² = x³ - (75 - 53√2)² x` at the places above `p` are good, and their orders
`d₁, d₂` satisfy `gcd(d₁, d₂) = 4` and `p ∤ d₁ d₂`. -/
def GoodPatternPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∃ r : ZMod p, r ^ 2 = 2 ∧
    (75 - 53 * r : ZMod p) ≠ 0 ∧ (75 + 53 * r : ZMod p) ≠ 0 ∧
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2)) = 4 ∧
    ¬ p ∣ pointCount p (-(75 - 53 * r) ^ 2) * pointCount p (-(75 + 53 * r) ^ 2)

/-- The seven shifts `𝓑 = {0, -15, -20, -24, -30, -60, 1}`. -/
def patternShifts : List ℤ := [0, -15, -20, -24, -30, -60, 1]

/-- The twenty-two pattern values `v` and `u_j - b v` (`1 ≤ j ≤ 3`, `b ∈ 𝓑`), where
`u₃ = A v - u₁ - u₂`. -/
def patternValues (A u₁ u₂ v : ℤ) : List ℤ :=
  v :: ([u₁, u₂, A * v - u₁ - u₂].flatMap fun u => patternShifts.map fun b => u - b * v)

/-- **Hypothesis 22P** (Proposition 6.2, the fixed twenty-two-prime pattern). For every
integer `A` and every real `B₀` there are integers `u₁, u₂, v` with `v ≠ 0` such that each
pattern value equals `ε k p` with `ε = ±1`, `k ∈ 𝓚` and `p > B₀` a good pattern prime. -/
def FixedPrimePattern : Prop :=
  ∀ (A : ℤ) (B₀ : ℝ), ∃ u₁ u₂ v : ℤ, v ≠ 0 ∧
    ∀ x ∈ patternValues A u₁ u₂ v, ∃ (ε : ℤ) (k p : ℕ),
      (ε = 1 ∨ ε = -1) ∧ k ∈ catalogueMultipliers ∧ B₀ < p ∧ GoodPatternPrime p ∧
        x = ε * k * p

open Classical in
/-- **Hypothesis CAT** (the progression estimate as used in Proposition 12.1): every unit
residue class modulo `W` contains at least twenty-two primes in the interval `(324, 2^(W³))`. -/
def CatalogueBound : Prop :=
  ∀ r : ℕ, r < catalogueModulus → Nat.Coprime r catalogueModulus →
    22 ≤ ({p ∈ Finset.Ioo 324 (2 ^ catalogueModulus ^ 3) |
      p.Prime ∧ p % catalogueModulus = r}).card

end ZInQ
