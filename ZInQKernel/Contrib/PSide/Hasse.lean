import ZInQKernel.Contrib.PSide.APZero
import ZInQKernel.Contrib.PSide.Coeff
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# P4 (first half): Hasse's bound for `C_d`, by a character-sum argument

For `C_d : y² = x³ − d² x` and a prime `p ∤ 2d`, `a_p(C_d) = −φ(−d²)` with the Jacobsthal sum
`φ(a) = Σ_{x ∈ 𝔽_p} χ(x (x² + a))` (`χ` the quadratic character). Over any finite field `F` of
odd characteristic with `q` elements:

1. `jac_mul_sq`: `φ(a t²) = χ(t) φ(a)` for `t ≠ 0` (substitute `x = t y`);
2. `sum_char_mul_add`: `Σ_a χ((a + u)(a + v)) = q − 1` if `u = v` and `−1` otherwise (the Jacobi
   sum `J(χ, χ) = −χ(−1)`, `jacobiSum_nontrivial_inv`);
3. `sum_jac_sq`: `Σ_a φ(a)² = q (q − 1)(1 + χ(−1)) ≤ 2 q (q − 1)`;
4. `jac_sq_le`: for `a ≠ 0`, `(q − 1) φ(a)² = Σ_{t ≠ 0} φ(a t²)² ≤ 2 Σ_c φ(c)²`, since each `c`
   has at most two square roots; hence `φ(a)² ≤ 4q`.

This is the classical elementary proof of Hasse's bound for `y² = x³ + a x` via Jacobsthal sums
(STANDARD; e.g. Berndt–Evans–Williams, *Gauss and Jacobi Sums*, Ch. 6 (UNVERIFIED chapter number),
or Ireland–Rosen, Ch. 18 §3 for the evaluation `a_p = ±2a`, `p = a² + b²`). Results:

* `jac_sq_le_four_mul`: `φ(a)² ≤ 4q` for `a ≠ 0`;
* `cdCoeff_prime_eq_neg_jac`, `cdCoeff_prime_sq_le` (**Hasse's bound for `C_d`**:
  `c_p² ≤ 4p` for every prime `p` and every `d`), and `LFunction_cd_prime_sq_le` (on Mathlib's
  coefficients, odd squarefree `d`).
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve

section Jacobsthal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Jacobsthal sum `φ(a) = Σ_x χ(x (x² + a))`. -/
def jac (a : F) : ℤ := ∑ x : F, quadraticChar F (x * (x ^ 2 + a))

theorem jac_mul_sq (a : F) {t : F} (ht : t ≠ 0) :
    jac (a * t ^ 2) = quadraticChar F t * jac a := by
  unfold jac
  rw [Finset.mul_sum]
  refine (Fintype.sum_bijective (t * ·) (mulLeft_bijective₀ t ht) _ _ fun y => ?_).symm
  have e : t * y * ((t * y) ^ 2 + a * t ^ 2) = t * t ^ 2 * (y * (y ^ 2 + a)) := by ring
  simp only [e, map_mul, map_pow, quadraticChar_sq_one ht, mul_one]

theorem jac_sq_mul_sq (a : F) {t : F} (ht : t ≠ 0) : jac (a * t ^ 2) ^ 2 = jac a ^ 2 := by
  rw [jac_mul_sq a ht, mul_pow, quadraticChar_sq_one ht, one_mul]

theorem quadraticChar_sq_eq (z : F) : quadraticChar F (z ^ 2) = if z = 0 then 0 else 1 := by
  split_ifs with h
  · subst h; simp
  · exact quadraticChar_sq_one' h

/-- `Σ_a χ((a + u)(a + v))`. -/
theorem sum_char_mul_add (hF : ringChar F ≠ 2) (u v : F) :
    ∑ a : F, quadraticChar F ((a + u) * (a + v)) =
      if u = v then (Fintype.card F : ℤ) - 1 else -1 := by
  split_ifs with huv
  · subst huv
    have h1 : ∑ a : F, quadraticChar F ((a + u) * (a + u)) =
        ∑ b : F, quadraticChar F (b ^ 2) :=
      Fintype.sum_equiv (Equiv.addRight u) _ _ fun a => by simp [sq]
    rw [h1]
    simp_rw [quadraticChar_sq_eq]
    have : ∀ b : F, (if b = 0 then (0 : ℤ) else 1) = 1 - if b = 0 then 1 else 0 := fun b => by
      split_ifs <;> simp
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · set w := u - v with hw
    have hw0 : w ≠ 0 := sub_ne_zero.mpr huv
    have hχ := quadraticChar_ne_one hF
    have hJ : jacobiSum (quadraticChar F) (quadraticChar F) = -quadraticChar F (-1) := by
      have := jacobiSum_nontrivial_inv hχ
      rwa [(quadraticChar_isQuadratic F).inv] at this
    -- substitute `a = w x − u`
    have h1 : ∑ a : F, quadraticChar F ((a + u) * (a + v)) =
        ∑ x : F, quadraticChar F (-1) * (quadraticChar F x * quadraticChar F (1 - x)) := by
      refine (Fintype.sum_equiv ((Equiv.mulLeft₀ w hw0).trans (Equiv.subRight u)) _ _
        fun x => ?_).symm
      show _ = quadraticChar F ((w * x - u + u) * (w * x - u + v))
      have e : (w * x - u + u) * (w * x - u + v) = (-1) * w ^ 2 * (x * (1 - x)) := by
        rw [hw]; ring
      rw [e, map_mul, map_mul, map_mul, quadraticChar_sq_one' hw0, mul_one]
    rw [h1, ← Finset.mul_sum, ← jacobiSum, hJ, mul_neg, ← sq,
      quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)]

/-- `Σ_a φ(a)² = q (q − 1)(1 + χ(−1))`. -/
theorem sum_jac_sq (hF : ringChar F ≠ 2) :
    ∑ a : F, jac a ^ 2 =
      (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (-1)) := by
  set q : ℤ := ((Fintype.card F : ℕ) : ℤ) with hqdef
  have h1 : ∑ a : F, jac a ^ 2 = ∑ x : F, ∑ y : F, quadraticChar F (x * y) *
      ∑ a : F, quadraticChar F ((a + x ^ 2) * (a + y ^ 2)) := by
    simp_rw [jac, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1; ring
  simp_rw [sum_char_mul_add hF] at h1
  simp only [← hqdef] at h1
  have h2 : ∀ x y : F, quadraticChar F (x * y) * (if x ^ 2 = y ^ 2 then q - 1 else -1) =
      q * (if y = x ∨ y = -x then quadraticChar F (x * y) else 0) -
        quadraticChar F x * quadraticChar F y := by
    intro x y
    have : x ^ 2 = y ^ 2 ↔ y = x ∨ y = -x := by
      rw [eq_comm]; exact sq_eq_sq_iff_eq_or_eq_neg
    rw [map_mul]
    by_cases h : y = x ∨ y = -x
    · rw [ite_eq_left (this.mpr h), ite_eq_left h]; ring
    · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h]; ring
  simp_rw [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    quadraticChar_sum_zero hF, zero_mul, sub_zero] at h1
  rw [h1]
  have h3 : ∀ x : F, ∑ y : F, (if y = x ∨ y = -x then quadraticChar F (x * y) else 0) =
      if x = 0 then 0 else 1 + quadraticChar F (-1) := by
    intro x
    split_ifs with hx
    · subst hx; simp
    · have hne : x ≠ -x := fun h => hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
      have : ∀ y : F, (if y = x ∨ y = -x then quadraticChar F (x * y) else 0) =
          (if y = x then quadraticChar F (x * y) else 0) +
            (if y = -x then quadraticChar F (x * y) else 0) := by
        intro y
        by_cases h1 : y = x
        · subst h1; rw [ite_eq_left (Or.inl rfl), ite_eq_left rfl, ite_eq_right hne]; ring
        · by_cases h2 : y = -x
          · subst h2; rw [ite_eq_left (Or.inr rfl), ite_eq_right h1, ite_eq_left rfl]; ring
          · rw [ite_eq_right (by tauto), ite_eq_right h1, ite_eq_right h2]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← sq, quadraticChar_sq_one' hx, mul_neg, ← sq, neg_eq_neg_one_mul (x ^ 2), map_mul,
        quadraticChar_sq_one' hx, mul_one]
  simp_rw [h3]
  have : ∀ x : F, (if x = 0 then (0 : ℤ) else 1 + quadraticChar F (-1)) =
      (1 + quadraticChar F (-1)) - if x = 0 then 1 + quadraticChar F (-1) else 0 := fun x => by
    split_ifs <;> simp
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem quadraticChar_le_one (a : F) : quadraticChar F a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rcases quadraticChar_dichotomy ha with h | h <;> rw [h]; norm_num

/-- `Σ_t G(t²) ≤ 2 Σ_c G(c)` for nonnegative `G` (each `c` has at most two square roots). -/
theorem sum_sq_le_two_mul (hF : ringChar F ≠ 2) (G : F → ℤ) (hG : ∀ c, 0 ≤ G c) :
    ∑ t : F, G (t ^ 2) ≤ 2 * ∑ c : F, G c := by
  classical
  have h1 : ∑ t : F, G (t ^ 2) = ∑ c : F, ((Finset.univ.filter fun t : F => t ^ 2 = c).card : ℤ) *
      G c := by
    have : ∀ t : F, G (t ^ 2) = ∑ c : F, if t ^ 2 = c then G c else 0 := fun t => by
      rw [Finset.sum_ite_eq]; simp
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hc : ((Finset.univ.filter fun t : F => t ^ 2 = c).card : ℤ) = quadraticChar F c + 1 := by
    rw [← quadraticChar_card_sqrts hF c]
    congr 2
    ext y; simp
  rw [hc]
  have := quadraticChar_le_one c
  nlinarith [hG c]

/-- **`φ(a)² ≤ 4q`** for `a ≠ 0`. -/
theorem jac_sq_le_four_mul (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    jac a ^ 2 ≤ 4 * Fintype.card F := by
  set q : ℤ := ((Fintype.card F : ℕ) : ℤ) with hqdef
  have hq : 1 < q := by
    have := Fintype.one_lt_card (α := F); simp only [q]; exact_mod_cast this
  -- `(q − 1) φ(a)² ≤ Σ_t φ(a t²)²`
  have h1 : (q - 1) * jac a ^ 2 ≤ ∑ t : F, jac (a * t ^ 2) ^ 2 := by
    have : ∀ t : F, (jac a ^ 2 - if t = 0 then jac a ^ 2 else 0) ≤ jac (a * t ^ 2) ^ 2 := by
      intro t
      split_ifs with ht
      · simp only [sub_self]; positivity
      · rw [sub_zero, jac_sq_mul_sq a ht]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun t _ => this t)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  -- `Σ_t φ(a t²)² ≤ 2 Σ_c φ(a c)² = 2 Σ_c φ(c)²`
  have h2 := sum_sq_le_two_mul hF (fun c => jac (a * c) ^ 2) (fun c => sq_nonneg _)
  have h3 : ∑ c : F, jac (a * c) ^ 2 = ∑ c : F, jac c ^ 2 :=
    Fintype.sum_bijective (a * ·) (mulLeft_bijective₀ a ha) _ _ fun c => rfl
  rw [h3, sum_jac_sq hF] at h2
  have h4 : quadraticChar F (-1) ≤ 1 := quadraticChar_le_one _
  rw [← hqdef] at h2
  have h5 : (q - 1) * jac a ^ 2 ≤ (q - 1) * (4 * q) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hq.le) (by linarith : (0 : ℤ) ≤ q))
      (sub_nonneg.2 h4)]
  exact le_of_mul_le_mul_left h5 (by linarith)

end Jacobsthal

section Cd

/-- `c_p = −φ(−d²)` at a prime `p ∤ 2d` (any `d`). -/
theorem cdCoeff_prime_eq_neg_jac (d : ℕ) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    cdCoeff d p = -jac (-(d : ZMod p) ^ 2) := by
  rw [cdCoeff_prime d (Fact.out), ite_eq_right hp, cdModel_eq_shortCurve,
    natCard_point_shortCurve_zmod p hp]
  have h := card_solutions_eq (ringChar_zmod_ne_two (ne_two_of_not_dvd hp))
    (fun x : ZMod p => x ^ 3 - (d : ZMod p) ^ 2 * x)
  rw [ZMod.card] at h
  push_cast
  rw [h, jac]
  have : ∀ x : ZMod p, x ^ 3 - (d : ZMod p) ^ 2 * x = x * (x ^ 2 + -(d : ZMod p) ^ 2) :=
    fun x => by ring
  simp_rw [this]
  ring

/-- **Hasse's bound for `C_d`**: `c_p² ≤ 4p` for every prime `p` and every `d` (for `p ∣ 2d`,
`c_p = 0`). -/
theorem cdCoeff_prime_sq_le (d : ℕ) {p : ℕ} (hp : p.Prime) : cdCoeff d p ^ 2 ≤ 4 * p := by
  have := Fact.mk hp
  by_cases h : p ∣ 2 * d
  · rw [cdCoeff_prime d hp, ite_eq_left h]; positivity
  · rw [cdCoeff_prime_eq_neg_jac d h, neg_sq]
    have hd : (d : ZMod p) ≠ 0 := fun h0 =>
      h (((ZMod.natCast_eq_zero_iff d p).mp h0).trans (dvd_mul_left d 2))
    have := jac_sq_le_four_mul (ringChar_zmod_ne_two (ne_two_of_not_dvd h))
      (neg_ne_zero.mpr (pow_ne_zero 2 hd))
    rwa [ZMod.card] at this

/-- **Hasse's bound on Mathlib's coefficients of `L(C_d, s)`** (odd squarefree `d`):
`a_p² ≤ 4p`, i.e. `|a_p| ≤ 2√p`, for every prime `p`. -/
theorem LFunction_cd_prime_sq_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {p : ℕ}
    (hp : p.Prime) : (shortCurve (-(d : ℚ) ^ 2)).LFunction p ^ 2 ≤ 4 * p := by
  rw [LFunction_cd_eq_cdCoeff hd hsq]
  exact cdCoeff_prime_sq_le d hp

end Cd

end ZInQ.Contrib.PSide
