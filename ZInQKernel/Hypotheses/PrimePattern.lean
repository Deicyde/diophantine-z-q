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

/-- Every unit residue class modulo `W` contains infinitely many primes above `324`
(Dirichlet's theorem, available in Mathlib). -/
theorem infinite_catalogue_class {r : ℕ} (hr : r < catalogueModulus)
    (hcop : Nat.Coprime r catalogueModulus) :
    (Set.ofPred fun p => p.Prime ∧ 324 < p ∧ p % catalogueModulus = r).Infinite := by
  have hW : catalogueModulus ≠ 0 := by
    unfold catalogueModulus
    exact mul_ne_zero (by norm_num) (primorial_pos 324).ne'
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hpa, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max a 324) hW hcop
  refine ⟨p, ⟨hp, lt_of_le_of_lt (le_max_right _ _) hpa, ?_⟩, lt_of_le_of_lt (le_max_left _ _) hpa⟩
  rw [hmod, Nat.mod_eq_of_lt hr]

/-- `Nat.nth` takes no junk value here: every catalogue index names a genuine prime above `324`
in its residue class. -/
theorem cataloguePrime_spec {r : ℕ} (hr : r < catalogueModulus)
    (hcop : Nat.Coprime r catalogueModulus) (i : ℕ) :
    (cataloguePrime r i).Prime ∧ 324 < cataloguePrime r i ∧
      cataloguePrime r i % catalogueModulus = r :=
  Nat.nth_mem_of_infinite (infinite_catalogue_class hr hcop) i

/-- `𝓚 = {d h : d ∣ P_s⁴, d > 0, h ∈ 𝓗}`. -/
def catalogueMultipliers : Set ℕ :=
  {k | ∃ d h, d ∣ primorial 324 ^ 4 ∧ 0 < d ∧ h ∈ catalogueSet ∧ k = d * h}

/-- The multipliers are positive, so no pattern value `ε k p` is zero. -/
theorem pos_of_mem_catalogueMultipliers {k : ℕ} (hk : k ∈ catalogueMultipliers) : 0 < k := by
  obtain ⟨d, h, -, hd, ⟨r, i, hr, hcop, -, rfl⟩, rfl⟩ := hk
  exact Nat.mul_pos hd (cataloguePrime_spec hr hcop i).1.pos

/-- The number of points of `y² = x³ + a x` over `ZMod p`, counting the point at infinity. -/
noncomputable def pointCount (p : ℕ) (a : ZMod p) : ℕ :=
  Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1} + 1

theorem pointCount_eq_card (p : ℕ) [NeZero p] (a : ZMod p) :
    pointCount p a = ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      fun xy => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1).card + 1 := by
  unfold pointCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The reduction of `E` at `(17, s - 6)` has `20` points, as stated in Proposition 3.1. -/
theorem pointCount_seventeen : pointCount 17 (-(75 - 53 * 6) ^ 2) = 20 := by
  rw [pointCount_eq_card]; decide

/-- The reduction of `E` at `(23, s - 5)` has `24` points, as stated in Proposition 3.1. -/
theorem pointCount_twentythree : pointCount 23 (-(75 - 53 * 5) ^ 2) = 24 := by
  rw [pointCount_eq_card]; decide

/-- The conditions of Proposition 6.2 on a prime `p`: it splits in `ℚ(√2)`, both reductions
of `E : y² = x³ - (75 - 53√2)² x` at the places above `p` are good, and their orders
`d₁, d₂` satisfy `gcd(d₁, d₂) = 4` and `p ∤ d₁ d₂`. -/
def GoodPatternPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∃ r : ZMod p, r ^ 2 = 2 ∧
    (75 - 53 * r : ZMod p) ≠ 0 ∧ (75 + 53 * r : ZMod p) ≠ 0 ∧
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2)) = 4 ∧
    ¬ p ∣ pointCount p (-(75 - 53 * r) ^ 2) * pointCount p (-(75 + 53 * r) ^ 2)

/-- A sanity check of the definition: `17` is a good pattern prime (`17 ≡ 1 mod 8`,
`17 ≡ 3 mod 7`; the two reductions have `20` and `16` points). -/
theorem goodPatternPrime_seventeen : GoodPatternPrime 17 := by
  refine ⟨by norm_num, by norm_num, 6, by decide, by decide, by decide, ?_, ?_⟩
  · rw [pointCount_eq_card, pointCount_eq_card]; decide
  · rw [pointCount_eq_card, pointCount_eq_card]; decide

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

/-- Hypothesis CAT bounds every catalogue prime by `X = 2^(W³)`: this is the bound
`H_max < X` drawn from it in Proposition 12.1. -/
theorem cataloguePrime_lt_of_catalogueBound (hCAT : CatalogueBound) {r : ℕ}
    (hr : r < catalogueModulus) (hcop : Nat.Coprime r catalogueModulus) {i : ℕ} (hi : i < 22) :
    cataloguePrime r i < 2 ^ catalogueModulus ^ 3 := by
  classical
  unfold cataloguePrime
  apply Nat.nth_lt_of_lt_count
  refine lt_of_lt_of_le hi (le_trans (hCAT r hr hcop) ?_)
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_range] at hp ⊢
  exact ⟨hp.1.2, hp.2.1, hp.1.1, hp.2.2⟩

end ZInQ
