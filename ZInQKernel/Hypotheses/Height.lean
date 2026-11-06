import Mathlib

/-!
# Hypothesis H: the six-contact height estimate

Theorem 4.1 (`thm:height`) of the 11/5 manuscript. Its proof uses Shimura curves,
Buzzard's integral models, modularity at the coefficient prime five and an effective
CM argument, none of which is available in Mathlib. The statement itself concerns
only rational numbers, so it enters the main theorem as an explicit hypothesis.
-/

namespace ZInQ

open scoped BigOperators

/-- The logarithmic height `h(a/b) = log max(|a|, b)` of a rational number in lowest terms. -/
noncomputable def ratHeight (u : ℚ) : ℝ :=
  Real.log (max |(u.num : ℝ)| (u.den : ℝ))

/-- The six contact values `𝒞 = {0, -15, -20, -24, -30, -60}`. -/
def contactSet : Finset ℚ := {0, -15, -20, -24, -30, -60}

open Classical in
/-- `M_S(u)`: the product of the primes `p ∉ S` at which `v_p(u - c)` is positive and odd for
some contact value `c`. Negative valuations of `u` do not contribute. -/
noncomputable def contactSupport (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contactSet, (u - c).num.natAbs).primeFactors with
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)),
    p

/-- `F₀ = 324!`. -/
noncomputable def heightF0 : ℕ := Nat.factorial 324

/-- `D = F₀ · 3^(256 F₀⁴)`. -/
noncomputable def heightD : ℕ := heightF0 * 3 ^ (256 * heightF0 ^ 4)

/-- `G₀ = 116064000000`. -/
def heightG0 : ℕ := 116064000000

/-- `E₀ = 10 (D G₀)²`. -/
noncomputable def heightE0 : ℕ := 10 * (heightD * heightG0) ^ 2

/-- `B_cm = D² 3^(21000 D²) + 1`. -/
noncomputable def heightBcm : ℕ := heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1

/-- `C_cm = 2 B_cm + 4096 (1028 + 5 D + 84000 D²)`. -/
noncomputable def heightCcm : ℕ := 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2)

/-- `Q_R = R^(R E₀)`. -/
noncomputable def heightQ (R : ℝ) : ℝ := R ^ (R * heightE0)

/-- `H₆(S; R) = 2·10¹³ · max(1, C_cm, Q_R¹⁷)`. It depends on `S` only through the
admissible range of `R`. -/
noncomputable def heightH6 (R : ℝ) : ℝ :=
  2 * 10 ^ 13 * max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- **Hypothesis H** (Theorem 4.1, the six-contact estimate). For every finite set `S` of
primes containing all primes at most `324`, every `R ≥ max(D, max S, 10¹²)` and every
`u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(S; R) M_S(u)²⁴`. -/
def SixContactEstimate : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S) →
    ∀ R : ℝ, (heightD : ℝ) ≤ R → (∀ p ∈ S, (p : ℝ) ≤ R) → (10 : ℝ) ^ 12 ≤ R →
      ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 R * (contactSupport S u : ℝ) ^ 24

end ZInQ
