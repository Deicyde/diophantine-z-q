import Mathlib

/-!
# The sum `Σ_{n ≤ w} r(n)/n` and the sum `Σ_{m ≤ w, m ∈ 𝒮} τ(m)/m`

Part of the sieve bound of `docs/research/pd-paper.md` §4.5 (Claims A and B), in a simplified form.

* `rDiv n = r(n)/n`, where `r(n) = Σ_{d ∣ n} χ₄(d)`.
* `rSum_ge_log`: `(2/3)·log w ≤ Σ_{n ≤ w} r(n)/n` (Claim A). The proof pairs the terms
  `d ≡ 1, 3 (mod 4)` of `Σ_d (χ₄(d)/d)·H(⌊w/d⌋)`; no Euler–Mascheroni constant is needed.
* `rDiv = hDiv * vDiv` with `hDiv n = τ(n)/n·[n ∈ 𝒮]` (`𝒮`: all prime factors `≡ 1 (mod 4)`) and
  `vDiv n = r(n)/n·[n ∈ 𝒯]` (`𝒯`: no prime factor `≡ 1 (mod 4)`), and `Σ_{m ≤ x} vDiv m ≤ 4`.
* `log_le_hSum`: `log w ≤ 6·Σ_{n ≤ w} hDiv n` (Claim B, with `V = 4`).
* `hSum_coprime_ge`: removing the multiples of a prime `ℓ ≥ 5` keeps at least `3/5` of the sum.
-/

open ArithmeticFunction Finset ZMod

namespace ZInQ.Density.GaussSieve

noncomputable section

open scoped Classical

/-- `χ₄(n)/n`. -/
def chiDiv : ArithmeticFunction ℝ := ⟨fun n => (χ₄ (n : ZMod 4) : ℝ) / n, by simp⟩

/-- `1/n`. -/
def invId : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

/-- `r(n)/n = Σ_{d ∣ n} χ₄(d)/n`. -/
def rDiv : ArithmeticFunction ℝ := chiDiv * invId

@[simp] theorem chiDiv_apply (n : ℕ) : chiDiv n = (χ₄ (n : ZMod 4) : ℝ) / n := rfl

@[simp] theorem invId_apply (n : ℕ) : invId n = (n : ℝ)⁻¹ := rfl

theorem chiDiv_mult : chiDiv.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  simp only [chiDiv_apply, Nat.cast_mul, map_mul, Int.cast_mul]
  ring

theorem invId_mult : invId.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  simp only [invId_apply, Nat.cast_mul, mul_inv]

theorem rDiv_mult : rDiv.IsMultiplicative := chiDiv_mult.mul invId_mult

/-- Dirichlet convolution at a prime power. -/
theorem mul_apply_prime_pow' (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.divisors_prime_pow hp,
    sum_map]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

theorem rDiv_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    rDiv (p ^ k) = (∑ i ∈ range (k + 1), (χ₄ (p : ZMod 4) : ℝ) ^ i) / (p : ℝ) ^ k := by
  rw [rDiv, mul_apply_prime_pow' _ _ hp, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [chiDiv_apply, invId_apply, Nat.cast_pow, map_pow, Int.cast_pow]
  rw [show (p : ℝ) ^ k = (p : ℝ) ^ i * (p : ℝ) ^ (k - i) by
    rw [← pow_add, Nat.add_sub_cancel' hik]]
  field_simp

/-! ### Claim A: `(2/3) log w ≤ Σ_{n ≤ w} r(n)/n` -/

theorem chi4_nat_cases (n : ℕ) :
    (χ₄ (n : ZMod 4) : ℝ) = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four n]
  split_ifs <;> simp

/-- Alternating sums with antitone nonnegative coefficients: blocks of four. -/
theorem alt_sum_four_block (a : ℕ → ℝ) (ha : ∀ i j, 1 ≤ i → i ≤ j → a j ≤ a i) (k : ℕ) :
    a 1 - a 3 ≤ ∑ d ∈ range (4 * k + 4), (χ₄ (d : ZMod 4) : ℝ) * a d := by
  induction k with
  | zero =>
    simp [sum_range_succ]
  | succ k ih =>
    have h4 : 4 * (k + 1) + 4 = 4 * k + 4 + 1 + 1 + 1 + 1 := by ring
    rw [h4, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    have e0 : (χ₄ ((4 * k + 4 : ℕ) : ZMod 4) : ℝ) = 0 := by
      rw [chi4_nat_cases]; simp [show (4 * k + 4) % 2 = 0 by omega]
    have e1 : (χ₄ ((4 * k + 4 + 1 : ℕ) : ZMod 4) : ℝ) = 1 := by
      rw [chi4_nat_cases, ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_left_of_eq_true _ _ (by simp; omega)]
    have e2 : (χ₄ ((4 * k + 4 + 1 + 1 : ℕ) : ZMod 4) : ℝ) = 0 := by
      rw [chi4_nat_cases, ite_eq_left_of_eq_true _ _ (by simp; omega)]
    have e3 : (χ₄ ((4 * k + 4 + 1 + 1 + 1 : ℕ) : ZMod 4) : ℝ) = -1 := by
      rw [chi4_nat_cases, ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_right_of_eq_false _ _ (by simp; omega)]
    rw [e0, e1, e2, e3]
    have := ha (4 * k + 4 + 1) (4 * k + 4 + 1 + 1 + 1) (by omega) (by omega)
    linarith

theorem alt_sum_ge (a : ℕ → ℝ) (ha : ∀ i j, 1 ≤ i → i ≤ j → a j ≤ a i) (h0 : ∀ i, 0 ≤ a i)
    (n : ℕ) (hn : 2 ≤ n) :
    a 1 - a 3 ≤ ∑ d ∈ range n, (χ₄ (d : ZMod 4) : ℝ) * a d := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 4).symm⟩
  rcases q with _ | q
  · interval_cases r
    · omega
    · omega
    · simp [sum_range_succ]; linarith [h0 3]
    · simp [sum_range_succ]; linarith [h0 3]
  · have hb := alt_sum_four_block a ha q
    have h4 : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [h4]
    have e0 : (χ₄ ((4 * q + 4 : ℕ) : ZMod 4) : ℝ) = 0 := by
      rw [chi4_nat_cases]; simp [show (4 * q + 4) % 2 = 0 by omega]
    have e1 : (χ₄ ((4 * q + 4 + 1 : ℕ) : ZMod 4) : ℝ) = 1 := by
      rw [chi4_nat_cases, ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_left_of_eq_true _ _ (by simp; omega)]
    have e2 : (χ₄ ((4 * q + 4 + 1 + 1 : ℕ) : ZMod 4) : ℝ) = 0 := by
      rw [chi4_nat_cases, ite_eq_left_of_eq_true _ _ (by simp; omega)]
    interval_cases r
    · simpa using hb
    · rw [sum_range_succ, e0]; simpa using hb
    · rw [show 4 * q + 4 + 2 = 4 * q + 4 + 1 + 1 by ring, sum_range_succ, sum_range_succ, e0, e1]
      linarith [h0 (4 * q + 4 + 1)]
    · rw [show 4 * q + 4 + 3 = 4 * q + 4 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        sum_range_succ, e0, e1, e2]
      linarith [h0 (4 * q + 4 + 1)]

/-- `Σ_{n ∈ (0, w]} r(n)/n`. -/
def rSum (w : ℕ) : ℝ := ∑ n ∈ Ioc 0 w, rDiv n

theorem sum_Ioc_invId (k : ℕ) : ∑ m ∈ Ioc 0 k, invId m = (harmonic k : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

theorem sum_Ioc_eq_sum_range {f : ℕ → ℝ} (hf : f 0 = 0) (w : ℕ) :
    ∑ n ∈ Ioc 0 w, f n = ∑ n ∈ range (w + 1), f n := by
  induction w with
  | zero => simp [hf]
  | succ w ih => rw [sum_Ioc_succ_top (Nat.zero_le _), ih, sum_range_succ _ (w + 1)]

theorem harmonic_mono' {m n : ℕ} (h : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  rw [← sum_Ioc_invId, ← sum_Ioc_invId]
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h)
    (fun i _ _ => by simp only [invId_apply]; positivity)

theorem harmonic_nonneg' (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  rw [← sum_Ioc_invId]
  exact sum_nonneg fun i _ => by simp only [invId_apply]; positivity

theorem rSum_ge_harmonic (w : ℕ) (hw : 1 ≤ w) : (2 / 3) * (harmonic w : ℝ) ≤ rSum w := by
  rw [rSum, rDiv, sum_Ioc_mul_eq_sum_sum]
  simp_rw [sum_Ioc_invId]
  set a : ℕ → ℝ := fun d => (harmonic (w / d) : ℝ) / d with ha_def
  have key : ∀ d, chiDiv d * (harmonic (w / d) : ℝ) = (χ₄ (d : ZMod 4) : ℝ) * a d := by
    intro d; simp only [chiDiv_apply, ha_def]; ring
  simp_rw [key]
  rw [sum_Ioc_eq_sum_range (by simp [ha_def])]
  have hanti : ∀ i j, 1 ≤ i → i ≤ j → a j ≤ a i := by
    intro i j hi hij
    simp only [ha_def]
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have hj' : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le hi hij)
    rw [div_le_div_iff₀ hj' hi']
    exact mul_le_mul (harmonic_mono' (Nat.div_le_div_left hij hi)) (by exact_mod_cast hij)
      hi'.le (harmonic_nonneg' _)
  have hnn : ∀ i, 0 ≤ a i := fun i => div_nonneg (harmonic_nonneg' _) (Nat.cast_nonneg _)
  refine le_trans ?_ (alt_sum_ge a hanti hnn (w + 1) (by omega))
  simp only [ha_def, Nat.div_one, Nat.cast_one, div_one]
  have : (harmonic (w / 3) : ℝ) ≤ harmonic w := harmonic_mono' (Nat.div_le_self w 3)
  norm_num
  linarith

/-- **Claim A** (simplified): `(2/3)·log w ≤ Σ_{n ≤ w} r(n)/n`. -/
theorem rSum_ge_log (w : ℕ) : (2 / 3) * Real.log w ≤ rSum w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [rSum]
  refine le_trans ?_ (rSum_ge_harmonic w hw)
  have h1 : Real.log w ≤ Real.log ((w + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hw) (by push_cast; linarith)
  have h2 := log_add_one_le_harmonic w
  linarith

/-! ### The decomposition `r = h ∗ v` -/

/-- Every prime factor of `n` is `≡ 1 (mod 4)` (false for `n = 0`). -/
def AllOneMod4 (n : ℕ) : Prop := ∀ q, q.Prime → q ∣ n → q % 4 = 1

/-- `n ≠ 0` and no prime factor of `n` is `≡ 1 (mod 4)`. -/
def NoOneMod4 (n : ℕ) : Prop := n ≠ 0 ∧ ∀ q, q.Prime → q ∣ n → q % 4 ≠ 1

theorem not_allOneMod4_zero : ¬ AllOneMod4 0 := fun h => by
  have := h 2 Nat.prime_two (dvd_zero 2); norm_num at this

theorem allOneMod4_mul {m n : ℕ} : AllOneMod4 (m * n) ↔ AllOneMod4 m ∧ AllOneMod4 n := by
  constructor
  · intro h
    exact ⟨fun q hq hd => h q hq (hd.mul_right n), fun q hq hd => h q hq (hd.mul_left m)⟩
  · rintro ⟨h1, h2⟩ q hq hd
    rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
    exacts [h1 q hq hd, h2 q hq hd]

theorem noOneMod4_mul {m n : ℕ} : NoOneMod4 (m * n) ↔ NoOneMod4 m ∧ NoOneMod4 n := by
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨left_ne_zero_of_mul h0, fun q hq hd => h q hq (hd.mul_right n)⟩,
      ⟨right_ne_zero_of_mul h0, fun q hq hd => h q hq (hd.mul_left m)⟩⟩
  · rintro ⟨⟨h01, h1⟩, ⟨h02, h2⟩⟩
    refine ⟨mul_ne_zero h01 h02, fun q hq hd => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
    exacts [h1 q hq hd, h2 q hq hd]

theorem dvd_prime_pow_eq {p q j : ℕ} (hp : p.Prime) (hq : q.Prime) (h : q ∣ p ^ j) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)

theorem allOneMod4_prime_pow {p j : ℕ} (hp : p.Prime) :
    AllOneMod4 (p ^ j) ↔ j = 0 ∨ p % 4 = 1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact Or.inl hj
    · exact Or.inr (h p hp (dvd_pow_self p hj.ne'))
  · rintro (rfl | h) q hq hd
    · simp at hd; exact absurd hd hq.ne_one
    · rw [dvd_prime_pow_eq hp hq hd]; exact h

theorem noOneMod4_prime_pow {p j : ℕ} (hp : p.Prime) :
    NoOneMod4 (p ^ j) ↔ j = 0 ∨ p % 4 ≠ 1 := by
  constructor
  · rintro ⟨_, h⟩
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact Or.inl hj
    · exact Or.inr (h p hp (dvd_pow_self p hj.ne'))
  · rintro (rfl | h)
    · refine ⟨by simp, fun q hq hd => ?_⟩
      simp at hd; exact absurd hd hq.ne_one
    · exact ⟨pow_ne_zero _ hp.ne_zero, fun q hq hd => by rw [dvd_prime_pow_eq hp hq hd]; exact h⟩

/-- Indicator of `AllOneMod4`. -/
def indS : ArithmeticFunction ℝ := ⟨fun n => if AllOneMod4 n then 1 else 0, by
  simp [not_allOneMod4_zero]⟩

/-- Indicator of `NoOneMod4`. -/
def indT : ArithmeticFunction ℝ := ⟨fun n => if NoOneMod4 n then 1 else 0, by
  simp [NoOneMod4]⟩

@[simp] theorem indS_apply (n : ℕ) : indS n = if AllOneMod4 n then 1 else 0 := rfl

@[simp] theorem indT_apply (n : ℕ) : indT n = if NoOneMod4 n then 1 else 0 := rfl

theorem indS_mult : indS.IsMultiplicative := by
  refine ⟨?_, fun {m n} _ => ?_⟩
  · simp only [indS_apply, if_pos (show AllOneMod4 1 from fun q hq hd => absurd
      (Nat.dvd_one.1 hd) hq.ne_one)]
  · simp only [indS_apply, allOneMod4_mul]
    split_ifs <;> simp_all

theorem indT_mult : indT.IsMultiplicative := by
  refine ⟨?_, fun {m n} _ => ?_⟩
  · simp only [indT_apply, if_pos (show NoOneMod4 1 from ⟨one_ne_zero, fun q hq hd => absurd
      (Nat.dvd_one.1 hd) hq.ne_one⟩)]
  · simp only [indT_apply, noOneMod4_mul]
    split_ifs <;> simp_all

/-- `τ(n)/n`. -/
def tauDiv : ArithmeticFunction ℝ := ⟨fun n => (n.divisors.card : ℝ) / n, by simp⟩

@[simp] theorem tauDiv_apply (n : ℕ) : tauDiv n = (n.divisors.card : ℝ) / n := rfl

theorem tauDiv_mult : tauDiv.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [tauDiv_apply, Nat.Coprime.card_divisors_mul h, Nat.cast_mul]
  rw [mul_div_mul_comm]

/-- `h(n)/n = τ(n)/n · [n ∈ 𝒮]`. -/
def hDiv : ArithmeticFunction ℝ := tauDiv.pmul indS

/-- `v(n)/n = r(n)/n · [n ∈ 𝒯]`. -/
def vDiv : ArithmeticFunction ℝ := rDiv.pmul indT

theorem hDiv_mult : hDiv.IsMultiplicative := tauDiv_mult.pmul indS_mult

theorem vDiv_mult : vDiv.IsMultiplicative := rDiv_mult.pmul indT_mult

theorem hDiv_nonneg (n : ℕ) : 0 ≤ hDiv n := by
  simp only [hDiv, pmul_apply, tauDiv_apply, indS_apply]
  split_ifs <;> positivity

theorem card_divisors_prime_pow' {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((p ^ k).divisors.card : ℝ) = k + 1 := by
  rw [Nat.divisors_prime_pow hp, card_map, card_range]; push_cast; ring

theorem rDiv_eq_hDiv_mul_vDiv : rDiv = hDiv * vDiv := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ rDiv_mult _ (hDiv_mult.mul vDiv_mult)).2 fun p i hp => ?_
  rw [mul_apply_prime_pow' _ _ hp]
  by_cases h4 : p % 4 = 1
  · rw [sum_eq_single i]
    · have hv1 : vDiv 1 = 1 := vDiv_mult.map_one
      simp only [Nat.sub_self, pow_zero, hv1, mul_one, hDiv, pmul_apply, tauDiv_apply,
        indS_apply, if_pos ((allOneMod4_prime_pow hp).2 (Or.inr h4)), card_divisors_prime_pow' hp,
        rDiv_prime_pow hp, ZMod.χ₄_nat_one_mod_four h4]
      simp
    · intro j hj hji
      have : 1 ≤ i - j := by simp [Nat.lt_succ_iff] at hj; omega
      simp only [vDiv, pmul_apply, indT_apply, if_neg (show ¬ NoOneMod4 (p ^ (i - j)) by
        rw [noOneMod4_prime_pow hp]; omega), mul_zero]
    · intro h; simp at h
  · rw [sum_eq_single 0]
    · have hh1 : hDiv 1 = 1 := hDiv_mult.map_one
      simp only [pow_zero, hh1, one_mul, Nat.sub_zero, vDiv, pmul_apply, indT_apply,
        if_pos ((noOneMod4_prime_pow hp).2 (Or.inr h4)), mul_one]
    · intro j _ hj0
      simp only [hDiv, pmul_apply, indS_apply, if_neg (show ¬ AllOneMod4 (p ^ j) by
        rw [allOneMod4_prime_pow hp]; omega), mul_zero, zero_mul]
    · intro h; simp at h

/-! ### `Σ_{m ≤ x} v(m)/m ≤ 4` -/

theorem sum_range_neg_one_pow (n : ℕ) :
    ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i = if Even n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd n with h | h
    · have : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg this, pow_succ, h.neg_one_pow]; ring
    · have : Even (n + 1) := h.add_one
      rw [if_neg (Nat.not_even_iff_odd.2 h), if_pos this, this.neg_one_pow]; ring

theorem vDiv_props (m : ℕ) :
    0 ≤ vDiv m ∧ vDiv m ≤ (m : ℝ)⁻¹ ∧ (vDiv m ≠ 0 → ∃ a s : ℕ, m = 2 ^ a * s ^ 2) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one =>
    rw [vDiv_mult.map_one]; exact ⟨zero_le_one, by simp, fun _ => ⟨0, 1, by simp⟩⟩
  | prime_pow p n hp hn =>
    have hp' : p.Prime := hp
    have hpos : (0 : ℝ) < (p : ℝ) ^ n := by have := hp'.pos; positivity
    by_cases h4 : p % 4 = 1
    · have : vDiv (p ^ n) = 0 := by
        simp only [vDiv, pmul_apply, indT_apply, if_neg (show ¬ NoOneMod4 (p ^ n) by
          rw [noOneMod4_prime_pow hp']; omega), mul_zero]
      rw [this]; exact ⟨le_rfl, by positivity, fun h => absurd rfl h⟩
    · have hv : vDiv (p ^ n) = rDiv (p ^ n) := by
        simp only [vDiv, pmul_apply, indT_apply,
          if_pos ((noOneMod4_prime_pow hp').2 (Or.inr h4)), mul_one]
      rw [hv, rDiv_prime_pow hp', Nat.cast_pow]
      rcases hp'.eq_two_or_odd with rfl | hodd
      · have : (χ₄ ((2 : ℕ) : ZMod 4) : ℝ) = 0 := by rw [chi4_nat_cases]; simp
        rw [this, sum_range_succ']
        simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
          pow_zero, zero_add, one_div]
        exact ⟨by positivity, le_rfl, fun _ => ⟨n, 1, by simp⟩⟩
      · have h3 : p % 4 = 3 := by omega
        rw [ZMod.χ₄_nat_three_mod_four h3, Int.cast_neg, Int.cast_one, sum_range_neg_one_pow]
        split_ifs with he
        · refine ⟨by positivity, by rw [one_div], fun _ => ?_⟩
          obtain ⟨t, rfl⟩ := he
          exact ⟨0, p ^ t, by ring⟩
        · simp
  | coprime a b _ _ hab iha ihb =>
    rw [vDiv_mult.map_mul_of_coprime hab]
    obtain ⟨ha0, ha1, ha2⟩ := iha
    obtain ⟨hb0, hb1, hb2⟩ := ihb
    refine ⟨mul_nonneg ha0 hb0, ?_, fun h => ?_⟩
    · rw [Nat.cast_mul, mul_inv]
      exact mul_le_mul ha1 hb1 hb0 (by positivity)
    · obtain ⟨α, s, rfl⟩ := ha2 (left_ne_zero_of_mul h)
      obtain ⟨β, t, rfl⟩ := hb2 (right_ne_zero_of_mul h)
      exact ⟨α + β, s * t, by ring⟩

theorem vSum_le_four (x : ℕ) : ∑ m ∈ Ioc 0 x, vDiv m ≤ 4 := by
  classical
  set D := (range (x + 1)) ×ˢ (Icc 1 x)
  have h1 : ∑ m ∈ Ioc 0 x, vDiv m ≤ ∑ m ∈ (Ioc 0 x).filter (fun m => vDiv m ≠ 0), (m : ℝ)⁻¹ := by
    rw [sum_filter]
    refine sum_le_sum fun m _ => ?_
    split_ifs with h
    · exact (vDiv_props m).2.1
    · rw [not_not.1 h]
  have h2 : (Ioc 0 x).filter (fun m => vDiv m ≠ 0) ⊆ D.image (fun as => 2 ^ as.1 * as.2 ^ 2) := by
    intro m hm
    simp only [mem_filter, mem_Ioc] at hm
    obtain ⟨a, s, rfl⟩ := (vDiv_props _).2.2 hm.2
    have hs : s ≠ 0 := by rintro rfl; simp at hm
    have h2a : a < 2 ^ a := Nat.lt_two_pow_self
    have hsa : s ≤ s ^ 2 := by nlinarith [Nat.one_le_iff_ne_zero.2 hs]
    have hle1 : 2 ^ a ≤ 2 ^ a * s ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have hle2 : s ^ 2 ≤ 2 ^ a * s ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    refine mem_image.2 ⟨(a, s), ?_, rfl⟩
    simp only [D, mem_product, mem_range, mem_Icc]
    omega
  have h3 := sum_le_sum_of_subset_of_nonneg (f := fun m : ℕ => (m : ℝ)⁻¹) h2
    (fun m _ _ => inv_nonneg.2 (Nat.cast_nonneg m))
  have h4 := sum_image_le_of_nonneg (s := D) (g := fun as => 2 ^ as.1 * as.2 ^ 2)
    (f := fun m : ℕ => (m : ℝ)⁻¹) (fun u _ => inv_nonneg.2 (Nat.cast_nonneg u))
  have h5 : ∑ as ∈ D, (((2 ^ as.1 * as.2 ^ 2 : ℕ) : ℝ))⁻¹ =
      (∑ a ∈ range (x + 1), (1 / (2 : ℝ)) ^ a) * ∑ s ∈ Icc 1 x, ((s : ℝ) ^ 2)⁻¹ := by
    rw [sum_product, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    push_cast
    rw [mul_inv, one_div, inv_pow]
  have h6 : ∑ s ∈ Icc 1 x, ((s : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have : Icc 1 x = Ioo 0 (x + 1) := by ext; simp; omega
    rw [this]
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (x + 1)
    norm_num at this ⊢
    exact this
  have h7 := sum_geometric_two_le (x + 1)
  have h8 : 0 ≤ ∑ s ∈ Icc 1 x, ((s : ℝ) ^ 2)⁻¹ := sum_nonneg fun _ _ => by positivity
  calc ∑ m ∈ Ioc 0 x, vDiv m ≤ _ := h1
    _ ≤ _ := h3
    _ ≤ _ := h4
    _ = _ := h5
    _ ≤ 2 * 2 := mul_le_mul h7 h6 h8 (by norm_num)
    _ = 4 := by norm_num

/-- `Σ_{n ≤ w} h(n)/n = Σ_{n ≤ w, n ∈ 𝒮} τ(n)/n`. -/
def hSum (w : ℕ) : ℝ := ∑ n ∈ Ioc 0 w, hDiv n

/-- **Claim B** (with `V = 4`): `Σ_{n ≤ w} r(n)/n ≤ 4·Σ_{n ≤ w, n ∈ 𝒮} τ(n)/n`. -/
theorem rSum_le_hSum (w : ℕ) : rSum w ≤ 4 * hSum w := by
  rw [rSum, hSum, rDiv_eq_hDiv_mul_vDiv, sum_Ioc_mul_eq_sum_sum, mul_sum]
  refine sum_le_sum fun n _ => ?_
  rw [mul_comm 4]
  exact mul_le_mul_of_nonneg_left (vSum_le_four _) (hDiv_nonneg n)

theorem log_le_hSum (w : ℕ) : Real.log w ≤ 6 * hSum w := by
  have h1 := rSum_ge_log w
  have h2 := rSum_le_hSum w
  linarith

/-! ### Removing the multiples of `ℓ` -/

theorem card_divisors_mul_le' (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]; exact card_mul_le

theorem hDiv_prime_mul_le {ℓ : ℕ} (hℓ : ℓ.Prime) (m : ℕ) :
    hDiv (ℓ * m) ≤ (2 / ℓ) * hDiv m := by
  simp only [hDiv, pmul_apply, tauDiv_apply, indS_apply, allOneMod4_mul]
  by_cases hm : AllOneMod4 m
  · by_cases hl : AllOneMod4 ℓ
    · rw [if_pos ⟨hl, hm⟩, if_pos hm, mul_one, mul_one]
      have hc : ((ℓ * m).divisors.card : ℝ) ≤ 2 * m.divisors.card := by
        have := card_divisors_mul_le' ℓ m
        rw [Nat.Prime.divisors hℓ, card_pair hℓ.ne_one.symm] at this
        exact_mod_cast this
      rw [Nat.cast_mul, div_mul_div_comm]
      exact div_le_div_of_nonneg_right hc (by positivity)
    · rw [if_neg (fun h => hl h.1), mul_zero]
      split_ifs <;> positivity
  · rw [if_neg (fun h => hm h.2), mul_zero, if_neg hm, mul_zero, mul_zero]

/-- Removing the multiples of a prime `ℓ` costs at most a factor `1 - 2/ℓ`. -/
theorem hSum_coprime_ge {ℓ : ℕ} (hℓ : ℓ.Prime) (w : ℕ) :
    (1 - 2 / (ℓ : ℝ)) * hSum w ≤ ∑ n ∈ (Ioc 0 w).filter (fun n => ¬ ℓ ∣ n), hDiv n := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 w) (fun n => ℓ ∣ n) hDiv
  have hsub : (Ioc 0 w).filter (fun n => ℓ ∣ n) ⊆ (Ioc 0 w).image (fun m => ℓ * m) := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨h0, hw⟩, m, rfl⟩ := hn
    refine mem_image.2 ⟨m, ?_, rfl⟩
    simp only [mem_Ioc]
    constructor
    · rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at h0
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left m hℓ.pos) hw
  have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hDiv_nonneg n)
  have h2 := sum_image_le_of_nonneg (s := Ioc 0 w) (g := fun m => ℓ * m) (f := hDiv)
    (fun _ _ => hDiv_nonneg _)
  have h3 : ∑ m ∈ Ioc 0 w, hDiv (ℓ * m) ≤ (2 / ℓ) * hSum w := by
    rw [hSum, mul_sum]; exact sum_le_sum fun m _ => hDiv_prime_mul_le hℓ m
  have : hSum w = ∑ n ∈ Ioc 0 w, hDiv n := rfl
  rw [sub_mul, one_mul]
  linarith

end

end ZInQ.Density.GaussSieve
