import ZInQKernel.Hypotheses.Pole

/-!
# The one-sided pole obstruction

Blueprint: `multiplication/abscissa-parity.md` and `multiplication/pole-obstruction.md`
(Lemma 5.1). These two articles belong to the multiplication chapter's root section; soundness
uses the obstruction at odd contact primes, so it is proved here.

If `B ≠ 0` and `Φ(B)`, then at no prime `p ∉ S₀ = {2, 3, 5, 7, 13}` is `v_p(B)` negative and odd.
-/

namespace ZInQ

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Parity of the abscissa on `y² = x (x - ℓ)(x + 3ℓ)`.** For `p ≠ 3`, `ℓ ≠ 0` with
`v_p(ℓ)` even and `x ≠ 0`, `v_p(x)` is even. -/
theorem abscissa_parity (hp3 : p ≠ 3) {ℓ x y : ℚ} (hℓ : ℓ ≠ 0)
    (hℓe : Even (padicValRat p ℓ)) (hx : x ≠ 0) (h : y ^ 2 = x * (x - ℓ) * (x + 3 * ℓ)) :
    Even (padicValRat p x) := by
  by_cases he : padicValRat p x = padicValRat p ℓ
  · rwa [he]
  have h3 : padicValRat p (3 : ℚ) = 0 := by
    have : padicValRat p ((3 : ℕ) : ℚ) = padicValNat p 3 := padicValRat.of_nat
    rw [show ((3 : ℕ) : ℚ) = 3 by norm_num] at this
    rw [this, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hd)
  have h3ℓ : padicValRat p (3 * ℓ) = padicValRat p ℓ := by
    rw [padicValRat.mul (by norm_num) hℓ, h3, zero_add]
  have hnegℓ : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
  have h1 : x - ℓ ≠ 0 := by
    intro h0; apply he; rw [show x = ℓ by linarith]
  have h2 : x + 3 * ℓ ≠ 0 := by
    intro h0; apply he; rw [show x = -(3 * ℓ) by linarith, padicValRat.neg, h3ℓ]
  have v1 : padicValRat p (x - ℓ) = min (padicValRat p x) (padicValRat p ℓ) := by
    rw [sub_eq_add_neg, padicValRat.add_eq_min (by rwa [← sub_eq_add_neg]) hx hnegℓ
      (by rwa [padicValRat.neg]), padicValRat.neg]
  have v2 : padicValRat p (x + 3 * ℓ) = min (padicValRat p x) (padicValRat p ℓ) := by
    rw [padicValRat.add_eq_min h2 hx (mul_ne_zero (by norm_num) hℓ) (by rwa [h3ℓ]), h3ℓ]
  have hrhs : x * (x - ℓ) * (x + 3 * ℓ) ≠ 0 := mul_ne_zero (mul_ne_zero hx h1) h2
  have hy : y ≠ 0 := by rintro rfl; rw [← h] at hrhs; simp at hrhs
  have hv := congrArg (padicValRat p) h
  rw [padicValRat.pow, padicValRat.mul (mul_ne_zero hx h1) h2, padicValRat.mul hx h1, v1, v2]
    at hv
  push_cast at hv
  exact ⟨padicValRat p y - min (padicValRat p x) (padicValRat p ℓ), by linarith⟩

omit hp in
theorem sq_sub_eq_zero_of_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∑ i ∈ s, f i ^ 2 = 0) : ∀ i ∈ s, f i = 0 := by
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).mp h i hi
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

omit hp in
theorem bool_of_sq_sub {b : ℚ} (h : b ^ 2 - b = 0) : b = 0 ∨ b = 1 := by
  have : b * (b - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- `v_p(1 + n b) = 0` for `b ∈ {0, 1}` when `1 + n` is a prime different from `p`. -/
theorem padicValRat_one_add_mul_bool {b : ℚ} (hb : b = 0 ∨ b = 1) {n : ℕ} (hn : (n + 1).Prime)
    (hpn : p ≠ n + 1) : 1 + n * b ≠ 0 ∧ padicValRat p (1 + n * b) = 0 := by
  rcases hb with rfl | rfl
  · simp
  · have e : (1 + (n : ℚ) * 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [e, padicValRat.of_nat]
    refine ⟨by exact_mod_cast (n + 1).succ_ne_zero, ?_⟩
    rw [padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro hd; exact hpn ((Nat.prime_dvd_prime_iff_eq hp.out hn).mp hd)

omit hp in
theorem four_sq {S X Y Z : ℚ} (hS : 0 ≤ S) (h : S + X ^ 2 + Y ^ 2 + Z ^ 2 = 0) :
    S = 0 ∧ X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have q1 := sq_nonneg X
  have q2 := sq_nonneg Y
  have q3 := sq_nonneg Z
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)

/-- **The one-sided pole obstruction** (Lemma 5.1). If `B ≠ 0` and `Φ(B)`, then for every prime
`p ∉ S₀`, `v_p(B)` is not negative and odd. -/
theorem pole_obstruction {B : ℚ} (hB : B ≠ 0) (hΦ : PoleSoluble B) (hpS : p ∉ poleS0) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  rintro ⟨hneg, hodd⟩
  obtain ⟨b, e, z, r₁, r₂, w, h⟩ := hΦ
  simp only [polePoly, mul_eq_zero, hB, false_or] at h
  obtain ⟨hS, hw, hr₁, hr₂⟩ := four_sq (Finset.sum_nonneg fun i _ => sq_nonneg _) h
  set m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5) with hm
  set A := m * B with hA
  set H := A * (A - B ^ 2) with hH
  clear_value H A m
  have hb : ∀ i : Fin 6, b i = 0 ∨ b i = 1 := fun i =>
    bool_of_sq_sub (sq_sub_eq_zero_of_sum Finset.univ (fun i => b i ^ 2 - b i) hS i
      (Finset.mem_univ i))
  have hp2 : p ≠ 2 := fun h => hpS (by simp [poleS0, h])
  have hp3 : p ≠ 3 := fun h => hpS (by simp [poleS0, h])
  have hp5 : p ≠ 5 := fun h => hpS (by simp [poleS0, h])
  have hp7 : p ≠ 7 := fun h => hpS (by simp [poleS0, h])
  have hp13 : p ≠ 13 := fun h => hpS (by simp [poleS0, h])
  -- `m` is a signed divisor of `2730`, a `p`-adic unit
  have f0 : 1 - 2 * b 0 ≠ 0 ∧ padicValRat p (1 - 2 * b 0) = 0 := by
    rcases hb 0 with h0 | h0 <;> rw [h0] <;> norm_num
  have f1 := padicValRat_one_add_mul_bool (p := p) (n := 1) (by simpa using hb 1)
    Nat.prime_two hp2
  have f2 := padicValRat_one_add_mul_bool (p := p) (n := 2) (hb 2) Nat.prime_three hp3
  have f3 := padicValRat_one_add_mul_bool (p := p) (n := 4) (hb 3) (by norm_num) hp5
  have f4 := padicValRat_one_add_mul_bool (p := p) (n := 6) (hb 4) (by norm_num) hp7
  have f5 := padicValRat_one_add_mul_bool (p := p) (n := 12) (hb 5) (by norm_num) hp13
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at f1 f2 f3 f4 f5
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero f0.1 f1.1) f2.1) f3.1)
      f4.1) f5.1
  have hmv : padicValRat p m = 0 := by
    rw [hm, padicValRat.mul _ f5.1, padicValRat.mul _ f4.1, padicValRat.mul _ f3.1,
      padicValRat.mul _ f2.1, padicValRat.mul f0.1 f1.1, f0.2, f1.2, f2.2, f3.2, f4.2, f5.2]
    all_goals
      first
      | rfl
      | exact mul_ne_zero (mul_ne_zero (mul_ne_zero f0.1 f1.1) f2.1) f3.1
      | exact mul_ne_zero (mul_ne_zero f0.1 f1.1) f2.1
      | exact mul_ne_zero f0.1 f1.1
      | exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero f0.1 f1.1) f2.1) f3.1) f4.1
  set k := padicValRat p B with hk
  have hA0 : A ≠ 0 := by rw [hA]; exact mul_ne_zero hm0 hB
  have hAv : padicValRat p A = k := by rw [hA, padicValRat.mul hm0 hB, hmv, zero_add]
  have hH0 : H ≠ 0 := by
    intro h0; rw [h0] at hw; simp at hw
  have hAB : A - B ^ 2 ≠ 0 := by intro h0; apply hH0; rw [hH, h0, mul_zero]
  have hABv : padicValRat p (A - B ^ 2) = 2 * k := by
    rw [sub_eq_add_neg, add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm, ← sub_eq_add_neg])
      (neg_ne_zero.mpr (pow_ne_zero _ hB)) hA0 (by rw [padicValRat.neg, padicValRat.pow, hAv]; omega),
      padicValRat.neg, padicValRat.pow]
    push_cast; ring
  have hHv : padicValRat p H = 3 * k := by
    rw [hH, padicValRat.mul hA0 hAB, hAv, hABv]; ring
  have he0 : e ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  have heH0 : e * H ≠ 0 := mul_ne_zero he0 hH0
  have heHv : padicValRat p (e * H) = padicValRat p e + 3 * k := by
    rw [padicValRat.mul he0 hH0, hHv]
  obtain ⟨j, hj⟩ := hodd
  rcases Int.even_or_odd (padicValRat p e) with hev | hev
  · -- `v_p(e)` even: the abscissa `A` of `E_e` has even valuation
    have := abscissa_parity hp3 he0 hev hA0 (y := r₁) (by linear_combination hr₁)
    rw [hAv] at this
    obtain ⟨i, hi⟩ := this
    omega
  · -- `v_p(eH)` even: the abscissa `A z²` of `E_{eH}` has even valuation
    have hev' : Even (padicValRat p (e * H)) := by
      rw [heHv]; obtain ⟨i, hi⟩ := hev; exact ⟨i + 3 * j + 2, by omega⟩
    have hx0 : A * z ^ 2 ≠ 0 := mul_ne_zero hA0 (pow_ne_zero _ hz0)
    have := abscissa_parity hp3 heH0 hev' hx0 (y := z * r₂)
      (by linear_combination z ^ 2 * hr₂)
    rw [padicValRat.mul hA0 (pow_ne_zero _ hz0), padicValRat.pow, hAv] at this
    obtain ⟨i, hi⟩ := this
    omega

end ZInQ
