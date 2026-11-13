import ZInQKernel.Model.Descent.Kummer

/-!
# The Kummer image over `ℚ` is finite

For `E_c : y² = x³ + c x` with `c ∈ ℤ ∖ {0}`, the Kummer map `α_c : E_c(ℚ) → ℚˣ/ℚˣ²` takes
values in the square classes of the signed divisors of `c`:

* for an affine point `(x, y)` with `x ≠ 0` and a prime `p ∤ c`, `v_p(x)` is even
  (`mwEven_padicValRat_x`: if `v_p(x) < 0` then `v_p(y²) = 3 v_p(x)`, if `v_p(x) > 0` then
  `v_p(y²) = v_p(x)`);
* a nonzero rational whose valuations at primes not dividing `B` are even is, modulo
  squares, a signed divisor of `B` (`mwSqc_eq_divisor`: write `num · den = ± s² a` with `a`
  squarefree; every prime factor of `a` divides `B`).
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

theorem mwEven_padicValRat_x {c : ℤ} {x y : ℚ} (he : y ^ 2 = x ^ 3 + c * x) (hx : x ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp : ¬(p : ℤ) ∣ c) : Even (padicValRat p x) := by
  have hc : c ≠ 0 := by rintro rfl; exact hp (dvd_zero _)
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hvc : padicValRat p (c : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hp]; rfl
  have hcx : padicValRat p ((c : ℚ) * x) = padicValRat p x := by
    rw [padicValRat.mul hcq hx, hvc, zero_add]
  have hx3 : padicValRat p (x ^ 3) = 3 * padicValRat p x := by
    rw [padicValRat.pow]; norm_num
  by_cases hy : y = 0
  · have h2 : x ^ 2 = -c := by
      have : x * (x ^ 2 + c) = 0 := by rw [hy] at he; linear_combination -he
      linear_combination (mul_eq_zero.mp this).resolve_left hx
    have : padicValRat p (x ^ 2) = 2 * padicValRat p x := by rw [padicValRat.pow]; norm_num
    rw [h2, padicValRat.neg, hvc] at this
    exact ⟨0, by omega⟩
  have hs : x ^ 3 + c * x ≠ 0 := by rw [← he]; exact pow_ne_zero 2 hy
  have hy2 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by rw [padicValRat.pow]; norm_num
  rw [he] at hy2
  rcases lt_trichotomy (padicValRat p x) 0 with h | h | h
  · rw [padicValRat.add_eq_of_lt hs (pow_ne_zero 3 hx) (mul_ne_zero hcq hx)
      (by rw [hx3, hcx]; omega), hx3] at hy2
    exact ⟨padicValRat p y - padicValRat p x, by omega⟩
  · exact ⟨0, by omega⟩
  · rw [add_comm] at hs hy2
    rw [padicValRat.add_eq_of_lt hs (mul_ne_zero hcq hx) (pow_ne_zero 3 hx)
      (by rw [hx3, hcx]; omega), hcx] at hy2
    exact ⟨padicValRat p y, by omega⟩

/-- A nonzero rational with even valuation at every prime not dividing `B` is a signed divisor
of `B` modulo squares. -/
theorem mwSqc_eq_divisor {q : ℚ} (hq : q ≠ 0) {B : ℕ} (hB : B ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬p ∣ B → Even (padicValRat p q)) :
    ∃ m : ℤ, m.natAbs ∣ B ∧ sqc q = sqc (m : ℚ) := by
  set N : ℤ := q.num * q.den with hN
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hNq : (N : ℚ) = q * (q.den : ℚ) ^ 2 := by
    rw [hN, Int.cast_mul, ← Rat.mul_den_eq_num]; push_cast; ring
  have hN0 : N ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_nz)
  obtain ⟨a, s, ha, hs, hsa, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hN0)
  refine ⟨N.sign * a, ?_, ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hN0, one_mul, Int.natAbs_natCast]
    rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff hB]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    refine ⟨hp.1, ?_, hB⟩
    by_contra hpB
    have := Fact.mk hp.1
    obtain ⟨r, hr⟩ := h p hp.1 hpB
    have hvN : padicValRat p (N : ℚ) = padicValRat p q + 2 * padicValRat p (q.den : ℚ) := by
      rw [hNq, padicValRat.mul hq (pow_ne_zero 2 hden), padicValRat.pow]; norm_num
    have hvN' : padicValRat p (N : ℚ) = 2 * padicValNat p s + padicValNat p a := by
      rw [padicValRat.of_int, padicValInt, ← hsa,
        padicValNat.mul (pow_ne_zero 2 hs.ne') ha.ne', padicValNat.pow]
      push_cast; ring
    have h1 := one_le_padicValNat_of_dvd ha.ne' hp.2.1
    have h2 : 2 ≤ padicValNat p a := by
      rw [hvN', hr, padicValRat.of_nat] at hvN
      omega
    have : p * p ∣ a := by
      rw [← pow_two]; exact (pow_dvd_pow p h2).trans pow_padicValNat_dvd
    exact hp.1.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  · rw [← (by rw [hNq, sqc_mul_sq _ hden] : sqc (N : ℚ) = sqc q)]
    conv_lhs => rw [← Int.sign_mul_natAbs N, ← hsa]
    push_cast
    rw [show (N.sign : ℚ) * ((s : ℚ) ^ 2 * a) = N.sign * a * (s : ℚ) ^ 2 by ring,
      sqc_mul_sq _ (by exact_mod_cast hs.ne')]

/-- **The Kummer image over `ℚ` is finite**: it lies in the classes of the signed divisors
of `c`. -/
theorem mwKummer_range_finite (c : ℤ) (hc : c ≠ 0) :
    (Set.range (kummer (c : ℚ))).Finite := by
  have hS : ((fun m : ℤ => sqc (m : ℚ)) '' {m : ℤ | m.natAbs ∣ c.natAbs}).Finite := by
    refine Set.Finite.image _ ((Set.finite_Icc (-(c.natAbs : ℤ)) c.natAbs).subset ?_)
    intro m hm
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hm
    simp only [Set.mem_Icc]
    omega
  refine hS.subset ?_
  rintro _ ⟨P, rfl⟩
  rcases P with _ | ⟨x, y, h⟩
  · refine ⟨1, by simp, ?_⟩
    show sqc ((1 : ℤ) : ℚ) = 1
    rw [Int.cast_one, show (1 : ℚ) = 1 ^ 2 by norm_num, sqc_sq]
  by_cases hx : x = 0
  · exact ⟨c, dvd_refl _, by rw [kummer_some]; simp [hx]⟩
  rw [kummer_some_of_ne _ _ hx]
  have he := (shortCurve_equation_iff _ x y).mp h.1
  obtain ⟨m, hm, e⟩ := mwSqc_eq_divisor hx (Int.natAbs_ne_zero.mpr hc) fun p hp hpc => by
    have := Fact.mk hp
    exact mwEven_padicValRat_x he hx (fun hd => hpc (Int.ofNat_dvd_left.mp hd))
  exact ⟨m, hm, e.symm⟩

end ZInQ.RouteK.Rank
