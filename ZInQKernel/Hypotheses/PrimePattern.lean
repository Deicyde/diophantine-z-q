import Mathlib

/-!
# Hypotheses 22P and CAT: prime patterns and the catalogue

Proposition 6.2 (`prop:fixed-prime-pattern`) of the 11/5 manuscript is proved with the
Green–Tao asymptotic for linear equations in primes, the Möbius–nilsequences theorem and
the inverse theorem for the Gowers norms (Green–Tao–Ziegler). Its conclusion is an
elementary statement about integers, so the three-hypothesis main theorem takes it as an
explicit hypothesis, `FixedPrimePattern` (22P). The two-hypothesis theorem
(`ZInQKernel/MainGreenTao.lean`) does not need it: route AP uses `GoodPrimeAP` instead, which
is proved (`Hypotheses/PrimeAP.lean`, `Hypotheses/GreenTao.lean`). The definitions
`pointCount` and `GoodSlopePrime` below are used by both routes.

The proof of Proposition 12.1 (`prop:cutoff`, the literal cutoff) bounds the catalogue with
the explicit progression estimate of Bennett, Martin, O'Bryant and Rechnitzer (CAT below). The
weaker form CAT₈, with the cutoff `2^(W⁸)`, is proved in Lean by an effective Dirichlet theorem
(`ZInQ.catalogueBound8`, `ZInQKernel/Progressions/`), and it is the form the size chain uses.

`TwoSlopePattern` (22P₂) is an alternative to 22P: a homothetic copy of a twelve-point set
inside the good primes, which the proof uses through the constant slope `-10`. It gives the
same conclusion of the completeness proof (`Mult.slopeRepresentation_of_twoSlopePattern`), with
the same polynomial. It is a different linear pattern in primes, not a consequence of 22P; its
expected proof is the Green–Tao–Ziegler argument of Proposition 6.2 with two variables and twelve
forms.
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

/-- The conditions on a prime that the completeness proof of the multiplication template uses:
`p` splits in `ℚ(√2)`, both reductions of `E` at the places above `p` are good, and their orders
`d₁, d₂` satisfy `gcd(d₁, d₂) = 4`. This is `GoodPatternPrime` without `p ≠ 2` and `p ∤ d₁ d₂`. -/
def GoodSlopePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ r : ZMod p, r ^ 2 = 2 ∧
    (75 - 53 * r : ZMod p) ≠ 0 ∧ (75 + 53 * r : ZMod p) ≠ 0 ∧
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2)) = 4

theorem GoodPatternPrime.goodSlopePrime {p : ℕ} (hp : GoodPatternPrime p) : GoodSlopePrime p := by
  obtain ⟨hp, -, r, hr, h1, h2, hgcd, -⟩ := hp
  exact ⟨hp, r, hr, h1, h2, hgcd⟩

/-- The twelve values `u - c v` and `u - (A + 10 - c) v` (`c ∈ 𝒞 = {0, -15, -20, -24, -30, -60}`)
of the two-slope pattern: the contact numerators of the slopes `u / v` and `A + 10 - u / v`. -/
def twoSlopeValues (A u v : ℤ) : List ℤ :=
  ([0, -15, -20, -24, -30, -60] : List ℤ).flatMap fun c => [u - c * v, u - (A + 10 - c) * v]

/-- **Hypothesis 22P₂** (the two-slope prime pattern). For every integer `A` there are integers
`u, v` with `v ≠ 0` such that the absolute value of each of the twelve numbers `u - c' v`,
`c' ∈ 𝒞 ∪ (A + 10 - 𝒞)`, is a good slope prime greater than `324` and outside the catalogue, and
such that `v`, `u - v` and `u - (A + 9) v` have valuation at most `4` at the primes `q ≤ 324` and
at most `1` at the catalogue primes.

It is used through the three slopes `u / v`, `A + 10 - u / v` and the constant slope `-10`, which
sum to `A`. In other words: a homothetic copy `u - v · (𝒞 ∪ (A + 10 - 𝒞))` of a twelve-point set
inside the good primes, with the common difference `v` and the numerators of `t - 1` controlled
at the old primes. For instance, `v = 8 P_s w` with `w` odd and `v_q(w) ≤ 3` for `q ≤ 324`,
twelve good primes above the catalogue, and no square of a catalogue prime dividing `w`, `u - v`
or `u - (A + 9) v` satisfy these conditions. -/
def TwoSlopePattern : Prop :=
  ∀ A : ℤ, ∃ u v : ℤ, v ≠ 0 ∧
    (∀ x ∈ twoSlopeValues A u v,
      GoodSlopePrime x.natAbs ∧ 324 < x.natAbs ∧ x.natAbs ∉ catalogueSet) ∧
    ∀ x ∈ [v, u - v, u - (A + 9) * v], ∀ q : ℕ, q.Prime →
      (q ≤ 324 → padicValInt q x ≤ 4) ∧ (q ∈ catalogueSet → padicValInt q x ≤ 1)

open Classical in
/-- **Hypothesis CAT** (the progression estimate as used in the proof of Proposition 12.1):
every unit residue class modulo `W` contains at least twenty-two primes in the interval
`(324, 2^(W³))`. -/
def CatalogueBound : Prop :=
  ∀ r : ℕ, r < catalogueModulus → Nat.Coprime r catalogueModulus →
    22 ≤ ({p ∈ Finset.Ioo 324 (2 ^ catalogueModulus ^ 3) |
      p.Prime ∧ p % catalogueModulus = r}).card

/-- Hypothesis CAT bounds every catalogue prime by `X = 2^(W³)`: this is the bound
`H_max < X` drawn from it in the proof of Proposition 12.1. -/
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


open Classical in
/-- **Hypothesis CAT₈**, the weaker form of CAT used by the size chain: every unit residue class
modulo `W` contains at least twenty-two primes in the interval `(324, 2^(W⁸))`. It follows from
CAT (`catalogueBound8_of_catalogueBound`) and from an effective Dirichlet theorem. -/
def CatalogueBound8 : Prop :=
  ∀ r : ℕ, r < catalogueModulus → Nat.Coprime r catalogueModulus →
    22 ≤ ({p ∈ Finset.Ioo 324 (2 ^ catalogueModulus ^ 8) |
      p.Prime ∧ p % catalogueModulus = r}).card

/-- CAT implies CAT₈: the interval `(324, 2^(W³))` lies in `(324, 2^(W⁸))`. -/
theorem catalogueBound8_of_catalogueBound (hCAT : CatalogueBound) : CatalogueBound8 := by
  classical
  -- The comparison `2^(w³) ≤ 2^(w⁸)` is proved for a variable `w`, so that the kernel never
  -- evaluates the closed powers of `W`.
  have hX : ∀ w : ℕ, 1 ≤ w → 2 ^ w ^ 3 ≤ 2 ^ w ^ 8 := fun w hw =>
    pow_le_pow_right₀ (by norm_num) (pow_le_pow_right₀ hw (by norm_num))
  have hW : 1 ≤ catalogueModulus := by
    unfold catalogueModulus
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by norm_num) (primorial_pos 324).ne')
  intro r hr hcop
  refine le_trans (hCAT r hr hcop) (Finset.card_le_card ?_)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans_le (hX _ hW)⟩, hp.2⟩

/-- Hypothesis CAT₈ bounds every catalogue prime by `X = 2^(W⁸)`: this is the bound `H_max < X`
of the proof of Proposition 12.1, with the cutoff `2^(W⁸)` in place of `2^(W³)`. -/
theorem cataloguePrime_lt_of_catalogueBound8 (hCAT : CatalogueBound8) {r : ℕ}
    (hr : r < catalogueModulus) (hcop : Nat.Coprime r catalogueModulus) {i : ℕ} (hi : i < 22) :
    cataloguePrime r i < 2 ^ catalogueModulus ^ 8 := by
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
