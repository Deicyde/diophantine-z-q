import ZInQKernel.Hypotheses.Pole
import ZInQ.PoleValuation

/-!
# The parity of the abscissa and the one-sided pole obstruction

Blueprint: `multiplication/abscissa-parity.md`, `multiplication/pole-obstruction.md`.

On `y² = x(x - ℓ)(x + 3ℓ)` with `v_p(ℓ)` even and `p ≠ 3`, the valuation `v_p(x)` of a nonzero
abscissa is even (`abscissa_val_even`; the upstream lemma
`ValuationObstruction.elliptic_x_valuation_even_of_parameter_even` carries an unused hypothesis
`p ≠ 2`, dropped here). From this, a rational zero of the pole polynomial with input `B ≠ 0`
forbids a negative odd valuation `v_p(B)` at every prime `p ∉ S₀ = {2, 3, 5, 7, 13}`
(`pole_obstruction`, Lemma 5.1). Neither statement uses a hypothesis.

Mathlib's `padicValRat p 0 = 0`; nonvanishing is part of the hypotheses.
-/

namespace ZInQ.Mult

open ZInQ.ValuationObstruction

/-- **Parity of the abscissa on `y² = x(x - ℓ)(x + 3ℓ)`.** For a prime `p ≠ 3`, `ℓ ≠ 0` with
`v_p(ℓ)` even and `x ≠ 0` on the curve, `v_p(x)` is even. -/
theorem abscissa_val_even (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (x l y : ℚ) (hx : x ≠ 0)
    (hl : l ≠ 0) (hl_even : Even (padicValRat p l)) (h : y ^ 2 = x * (x - l) * (x + 3 * l)) :
    Even (padicValRat p x) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases heq : padicValRat p x = padicValRat p l
  · rw [heq]
    exact hl_even
  · obtain ⟨hne0, hval⟩ := curve_rhs_nonzero_and_valuation p hp3 x l hx hl heq
    have hy2 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      have h := padicValRat.pow (p := p) y (k := 2)
      exact_mod_cast h
    rw [← h, hy2] at hval
    generalize min (padicValRat p x) (padicValRat p l) = c at hval
    exact ⟨padicValRat p y - c, by omega⟩

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
