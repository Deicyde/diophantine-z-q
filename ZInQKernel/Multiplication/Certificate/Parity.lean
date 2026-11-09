import ZInQKernel.Hypotheses.Pole
import ZInQ.PoleValuation

/-!
# The parity of the abscissa and the one-sided pole obstruction

Blueprint: `multiplication/abscissa-parity.md`, `multiplication/pole-obstruction.md`.

On the congruent number curve `y² = x(x - ℓ)(x + ℓ)` with `v_p(ℓ)` even, the valuation `v_p(x)`
of a nonzero abscissa is even, at every prime `p` (`abscissa_val_even`). From this, a rational
zero of the pole polynomial with input `B ≠ 0` forbids a negative odd valuation `v_p(B)` at every
prime `p ∉ S₀ = {2, 3, 5, 7, 13}` (`pole_obstruction`, Lemma 5.1). Neither statement uses a
hypothesis.

The pole polynomial is the Route K one (`ZInQ.polePoly`, curves `x + ℓ`). Upstream's
`ZInQ.ValuationObstruction` treats the manuscript's curves `x + 3ℓ`, so its system `poleSystem`
and the lemmas `curve_rhs_nonzero_and_valuation`, `poleSystem_no_negative_odd_valuation` are
copied here with `3ℓ` replaced by `ℓ`; the hypothesis `p ≠ 3` and the step `v_p(3ℓ) = v_p(ℓ)`
disappear. The multiplier and `H` lemmas of upstream do not involve the curve and are reused.

Mathlib's `padicValRat p 0 = 0`; nonvanishing is part of the hypotheses.
-/

namespace ZInQ.Mult

open ZInQ.ValuationObstruction (PoleWitness poleMultiplier poleA poleH
  poleMultiplier_nonzero_and_valuation_zero negative_input_pole_h_valuation)

/-- The witness system of the Route K pole polynomial: six Boolean coordinates, the inverse
equation `eHzw = 1`, and the curve equations `r₁² = A(A - e)(A + e)` and
`r₂² = A(Az² - eH)(Az² + eH)`, with `A = mB` and `H = A(A - B²)`. Upstream's
`ValuationObstruction.poleSystem` is the same system with `A + 3e` and `Az² + 3eH`. -/
def poleSystem (B : ℚ) (v : PoleWitness) : Prop :=
  (∀ i : Fin 6, (v.bit i) ^ 2 - v.bit i = 0) ∧
  v.e * poleH B v * v.z * v.w = 1 ∧
  v.r1 ^ 2 = poleA B v * (poleA B v - v.e) * (poleA B v + v.e) ∧
  v.r2 ^ 2 = poleA B v *
    (poleA B v * v.z ^ 2 - v.e * poleH B v) *
    (poleA B v * v.z ^ 2 + v.e * poleH B v)

/-- The square-scaling fact on the congruent number curve: if `x, l ≠ 0` have different
`p`-adic valuations, then `x(x - l)(x + l) ≠ 0` and its valuation is
`v(x) + 2 min (v(x), v(l))`. This is upstream's `curve_rhs_nonzero_and_valuation` with `3l`
replaced by `l`; no hypothesis on `p` is needed. -/
theorem congruentCurve_rhs_nonzero_and_valuation (p : ℕ) [Fact p.Prime] (x l : ℚ) (hx : x ≠ 0)
    (hl : l ≠ 0) (hne : padicValRat p x ≠ padicValRat p l) :
    x * (x - l) * (x + l) ≠ 0 ∧
      padicValRat p (x * (x - l) * (x + l)) =
        padicValRat p x + 2 * min (padicValRat p x) (padicValRat p l) := by
  -- the factor `x - l`
  have hnl : -l ≠ 0 := neg_ne_zero.mpr hl
  have hvnl : padicValRat p (-l) = padicValRat p l := padicValRat.neg l
  have hsub0 : x - l ≠ 0 := fun h => hne (by rw [sub_eq_zero.mp h])
  have hsum0 : x + -l ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact hsub0
  have hne' : padicValRat p x ≠ padicValRat p (-l) := by
    rw [hvnl]
    exact hne
  have hsub : padicValRat p (x - l) = min (padicValRat p x) (padicValRat p l) := by
    rw [sub_eq_add_neg, padicValRat.add_eq_min (p := p) hsum0 hx hnl hne', hvnl]
  -- the factor `x + l`
  have hadd0 : x + l ≠ 0 := by
    intro h
    apply hne
    rw [eq_neg_iff_add_eq_zero.mpr h, padicValRat.neg]
  have hadd : padicValRat p (x + l) = min (padicValRat p x) (padicValRat p l) :=
    padicValRat.add_eq_min (p := p) hadd0 hx hl hne
  have hxs0 : x * (x - l) ≠ 0 := mul_ne_zero hx hsub0
  refine ⟨mul_ne_zero hxs0 hadd0, ?_⟩
  rw [padicValRat.mul hxs0 hadd0, padicValRat.mul hx hsub0, hsub, hadd]
  ring

/-- **Parity of the abscissa on `y² = x(x - ℓ)(x + ℓ)`.** For a prime `p`, `ℓ ≠ 0` with
`v_p(ℓ)` even and `x ≠ 0` on the curve, `v_p(x)` is even. -/
theorem abscissa_val_even (p : ℕ) (hp : p.Prime) (x l y : ℚ) (hx : x ≠ 0)
    (hl : l ≠ 0) (hl_even : Even (padicValRat p l)) (h : y ^ 2 = x * (x - l) * (x + l)) :
    Even (padicValRat p x) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases heq : padicValRat p x = padicValRat p l
  · rw [heq]
    exact hl_even
  · obtain ⟨hne0, hval⟩ := congruentCurve_rhs_nonzero_and_valuation p x l hx hl heq
    have hy2 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      have h := padicValRat.pow (p := p) y (k := 2)
      exact_mod_cast h
    rw [← h, hy2] at hval
    generalize min (padicValRat p x) (padicValRat p l) = c at hval
    exact ⟨padicValRat p y - c, by omega⟩

/-- **The valuation obstruction for the pole system** (Lemma 5.1, Route K). For a solution of
`poleSystem B v` with `B ≠ 0` and a prime `p ∤ 2730`, `v_p(B)` is not negative and odd. -/
theorem poleSystem_no_negative_odd_valuation (B : ℚ) (v : PoleWitness) (hB : B ≠ 0)
    (hsystem : poleSystem B v) (p : ℕ) (hp : p.Prime) (hpout : ¬ p ∣ 2730) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  rintro ⟨hneg, hodd⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hbits, hinv, hc1, hc2⟩ := hsystem
  -- the multiplier is a nonzero unit
  obtain ⟨hm0, hmv⟩ := poleMultiplier_nonzero_and_valuation_zero p hp hpout v.bit hbits
  -- `A ≠ 0`, `H ≠ 0` and `v(H) = 3 v(B)`
  obtain ⟨hA0, hH0, hHv⟩ :=
    negative_input_pole_h_valuation p hp (poleMultiplier v.bit) B hm0 hB hmv hneg
  have hA0' : poleA B v ≠ 0 := hA0
  have hH0' : poleH B v ≠ 0 := hH0
  have hHv' : padicValRat p (poleH B v) = 3 * padicValRat p B := hHv
  have hAv : padicValRat p (poleA B v) = padicValRat p B := by
    show padicValRat p (poleMultiplier v.bit * B) = padicValRat p B
    rw [padicValRat.mul hm0 hB, hmv, zero_add]
  -- nonvanishing of `e` and `z` from the inverse equation `e H z w = 1`
  have he0 : v.e ≠ 0 := by
    intro h
    rw [h] at hinv
    simp at hinv
  have hz0 : v.z ≠ 0 := by
    intro h
    rw [h] at hinv
    simp at hinv
  obtain ⟨kb, hkb⟩ := hodd
  rcases Int.even_or_odd (padicValRat p v.e) with he | he
  · -- `v(e)` even: the first point `(A, r₁)` forces `v(A) = v(B)` even
    have hAeven := abscissa_val_even p hp (poleA B v) v.e v.r1 hA0' he0 he hc1
    rw [hAv] at hAeven
    obtain ⟨r, hr⟩ := hAeven
    omega
  · -- `v(e)` odd: then `v(eH) = v(e) + 3 v(B)` is even, and the second point
    -- `(Az², zr₂)` forces `v(Az²) = v(B) + 2 v(z)` even
    have hl0 : v.e * poleH B v ≠ 0 := mul_ne_zero he0 hH0'
    have hleven : Even (padicValRat p (v.e * poleH B v)) := by
      rw [padicValRat.mul he0 hH0', hHv']
      obtain ⟨ke, hke⟩ := he
      exact ⟨ke + 3 * kb + 2, by omega⟩
    have hz2ne : v.z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hx0 : poleA B v * v.z ^ 2 ≠ 0 := mul_ne_zero hA0' hz2ne
    have hcurve2 : (v.z * v.r2) ^ 2 = (poleA B v * v.z ^ 2) *
        ((poleA B v * v.z ^ 2) - v.e * poleH B v) *
        ((poleA B v * v.z ^ 2) + v.e * poleH B v) := by
      rw [mul_pow, hc2]
      ring
    have hxeven := abscissa_val_even p hp (poleA B v * v.z ^ 2) (v.e * poleH B v) (v.z * v.r2)
      hx0 hl0 hleven hcurve2
    have hz2 : padicValRat p (v.z ^ 2) = 2 * padicValRat p v.z := by
      have h := padicValRat.pow (p := p) v.z (k := 2)
      exact_mod_cast h
    rw [padicValRat.mul hA0' hz2ne, hAv, hz2] at hxeven
    obtain ⟨r, hr⟩ := hxeven
    omega

/-- A prime outside `S₀ = {2, 3, 5, 7, 13}` does not divide `2730 = 2·3·5·7·13`. -/
theorem not_dvd_2730_of_not_mem_poleS0 {p : ℕ} (hp : p.Prime) (hpS0 : p ∉ poleS0) :
    ¬ p ∣ 2730 := by
  intro hd
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 h
  rw [show (2730 : ℕ) = 2 * (3 * (5 * (7 * 13))) by norm_num] at hd
  simp only [poleS0, Finset.mem_insert, Finset.mem_singleton, not_or] at hpS0
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
  · exact hpS0.1 (hq 2 Nat.prime_two h)
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
  · exact hpS0.2.1 (hq 3 Nat.prime_three h)
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
  · exact hpS0.2.2.1 (hq 5 Nat.prime_five h)
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · exact hpS0.2.2.2.1 (hq 7 (by norm_num) h)
  · exact hpS0.2.2.2.2 (hq 13 (by norm_num) h)

/-- A rational zero of `Q_pole` with input `B ≠ 0` is a solution of the pole system: the sum of
squares vanishes, so every summand does. -/
theorem poleSystem_of_polePoly_eq_zero {B : ℚ} (hB : B ≠ 0) {b : Fin 6 → ℚ} {e z r₁ r₂ w : ℚ}
    (h : polePoly B b e z r₁ r₂ w = 0) : poleSystem B ⟨b, e, z, r₁, r₂, w⟩ := by
  unfold polePoly at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hB
  have hs : 0 ≤ ∑ i, (b i ^ 2 - b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [add_eq_zero_iff_of_nonneg (by positivity) (sq_nonneg _),
    add_eq_zero_iff_of_nonneg (by positivity) (sq_nonneg _),
    add_eq_zero_iff_of_nonneg hs (sq_nonneg _),
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at h
  obtain ⟨⟨⟨hb, hw⟩, h1⟩, h2⟩ := h
  refine ⟨fun i => pow_eq_zero_iff two_ne_zero |>.1 (hb i (Finset.mem_univ i)), ?_, ?_, ?_⟩
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hw)
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

/-- **The one-sided pole obstruction** (Lemma 5.1). If `B ≠ 0` and `Φ(B)`, then for every prime
`p ∉ S₀ = {2, 3, 5, 7, 13}`, `v_p(B)` is not negative and odd. -/
theorem pole_obstruction (B : ℚ) (hB : B ≠ 0) (hΦ : PoleSoluble B) (p : ℕ) (hp : p.Prime)
    (hpS0 : p ∉ poleS0) : ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  obtain ⟨b, e, z, r₁, r₂, w, h⟩ := hΦ
  exact poleSystem_no_negative_odd_valuation B _ hB (poleSystem_of_polePoly_eq_zero hB h) p hp
    (not_dvd_2730_of_not_mem_poleS0 hp hpS0)

end ZInQ.Mult
