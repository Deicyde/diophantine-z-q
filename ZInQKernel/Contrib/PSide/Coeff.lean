import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# P2: the coefficients `cdCoeff d n` of `L(C_d, s)`

`cdCoeff d n` (`RouteK/Rank/LFunctionCd.lean`) is the `n`-th Dirichlet coefficient of the Euler
product `∏_p (cdEulerPoly d p)(p^{−s})^{−1}`, where `cdEulerPoly d p = 1` for `p ∣ 2d` and
`1 − a_p T + p T²` (`a_p = p + 1 − #C_d(𝔽_p)`) otherwise; `LSeries_cd_eq` identifies its Dirichlet
series with Mathlib's `L(C_d, s)` for odd squarefree `d`. This file gives its API, for every `d`:

* `cdCoeff_zero`, `cdCoeff_one`; `cdArith d`, the arithmetic function, and
  `isMultiplicative_cdArith`; `cdCoeff_mul` (multiplicativity on coprime arguments);
* `cdCoeff_prime_pow` (the value at `p ^ k`, as a power-series coefficient), `cdCoeff_prime`
  (`a_p`, resp. `0`);
* `cdCoeff_prime_pow_succ_succ`: the recursion `c_{p^{k+2}} = a_p c_{p^{k+1}} − p c_{p^k}` for
  `p ∤ 2d`, with `cdCoeff_prime_pow_zero` and `cdCoeff_prime_pow_one`;
* `cdCoeff_prime_pow_of_dvd` (`c_{p^k} = 0` for `p ∣ 2d`, `k ≥ 1`) and `cdCoeff_eq_zero_of_dvd`
  (`c_n = 0` whenever a prime dividing `2d` divides `n`; in particular `c_n = 0` for even `n`);
* for odd squarefree `d`: `LFunction_cd_eq_cdCoeff` (Mathlib's coefficient is `cdCoeff`) and the
  recursion on Mathlib's coefficients, `LFunction_cd_prime_pow_succ_succ`.
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve ArithmeticFunction

/-- The local factor's power-series inverse `1 / cdEulerPoly d p`. -/
noncomputable abbrev cdLocalSeries (d p : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1

theorem constantCoeff_cdEulerPoly (d p : ℕ) :
    PowerSeries.constantCoeff (cdEulerPoly d p : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    cdEulerPoly_coeff_zero]; rfl

theorem coeff_zero_cdLocalSeries (d p : ℕ) : PowerSeries.coeff 0 (cdLocalSeries d p) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]; simp

theorem cdCoeff_zero (d : ℕ) : cdCoeff d 0 = 0 := by simp [cdCoeff]

theorem cdCoeff_one (d : ℕ) : cdCoeff d 1 = 1 := by simp [cdCoeff]

/-- `cdCoeff d` as an arithmetic function. -/
noncomputable def cdArith (d : ℕ) : ArithmeticFunction ℤ := ⟨cdCoeff d, cdCoeff_zero d⟩

@[simp] theorem cdArith_apply (d n : ℕ) : cdArith d n = cdCoeff d n := rfl

/-- **Multiplicativity** of `cdCoeff d` on coprime arguments. -/
theorem cdCoeff_mul (d : ℕ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    cdCoeff d (m * n) = cdCoeff d m * cdCoeff d n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp [cdCoeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp [cdCoeff_one]
  simp only [cdCoeff, mul_ne_zero hm hn, hm, hn, ↓reduceIte]
  rw [Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint (by simpa using hmn.disjoint_primeFactors)]

theorem isMultiplicative_cdArith (d : ℕ) : (cdArith d).IsMultiplicative :=
  ⟨cdCoeff_one d, fun hmn => cdCoeff_mul d hmn⟩

/-- **The value at a prime power**: `c_{p^k}` is the coefficient of `T ^ k` in
`1 / cdEulerPoly d p`. -/
theorem cdCoeff_prime_pow (d : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cdCoeff d (p ^ k) = PowerSeries.coeff k (cdLocalSeries d p) := by
  simp only [cdCoeff, pow_ne_zero k hp.ne_zero, ↓reduceIte, hp.factorization_pow]
  rw [Finsupp.prod_single_index (coeff_zero_cdLocalSeries d p)]

theorem cdCoeff_prime_pow_zero (d p : ℕ) : cdCoeff d (p ^ 0) = 1 := by
  rw [pow_zero, cdCoeff_one]

/-- **The value at a prime**: `c_p = 0` for `p ∣ 2d`, and `c_p = p + 1 − #C_d(𝔽_p)` otherwise
(`#C_d(𝔽_p)` counts the point at infinity; `cdModel (ZMod p) d` is `y² = x³ − d² x`). -/
theorem cdCoeff_prime (d : ℕ) {p : ℕ} (hp : p.Prime) :
    cdCoeff d p = if p ∣ 2 * d then 0
      else (p : ℤ) + 1 - Nat.card (cdModel (ZMod p) d).toAffine.Point := by
  have h := cdCoeff_prime_pow d hp 1
  rw [pow_one] at h
  rw [h, coeff_one_invOfUnit _ (cdEulerPoly_coeff_zero d p)]
  unfold cdEulerPoly
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

theorem cdCoeff_prime_pow_one (d p : ℕ) : cdCoeff d (p ^ 1) = cdCoeff d p := by rw [pow_one]

/-- At a good prime, the Euler polynomial is `1 − c_p T + p T²`. -/
theorem cdEulerPoly_of_not_dvd (d : ℕ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2 * d) :
    cdEulerPoly d p = 1 - Polynomial.C (cdCoeff d p) * Polynomial.X +
      Polynomial.C (p : ℤ) * Polynomial.X ^ 2 := by
  rw [cdCoeff_prime d hp, cdEulerPoly]
  simp only [h, ↓reduceIte]

/-- **The Hecke recursion at a good prime**: for `p ∤ 2d`,
`c_{p^{k+2}} = c_p · c_{p^{k+1}} − p · c_{p^k}`. -/
theorem cdCoeff_prime_pow_succ_succ (d : ℕ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (k + 2)) = cdCoeff d p * cdCoeff d (p ^ (k + 1)) - p * cdCoeff d (p ^ k) := by
  simp only [cdCoeff_prime_pow d hp]
  set Q := cdLocalSeries d p
  have hmul := PowerSeries.mul_invOfUnit _ _ (constantCoeff_cdEulerPoly d p)
  have hP : (cdEulerPoly d p : PowerSeries ℤ) =
      1 - PowerSeries.C (cdCoeff d p) * PowerSeries.X +
        PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2 := by
    rw [cdEulerPoly_of_not_dvd d hp h]
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  have hmul' : (1 - PowerSeries.C (cdCoeff d p) * PowerSeries.X +
      PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2) * Q = 1 := by rw [← hP]; exact hmul
  have h2 := congrArg (PowerSeries.coeff (k + 2)) hmul'
  have e : (1 - PowerSeries.C (cdCoeff d p) * PowerSeries.X +
      PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2) * Q =
      Q - PowerSeries.C (cdCoeff d p) * (PowerSeries.X * Q) +
        PowerSeries.C (p : ℤ) * (PowerSeries.X ^ 2 * Q) := by ring
  rw [e, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one] at h2
  simp only [show 2 ≤ k + 2 by omega, ↓reduceIte, Nat.add_sub_cancel,
    show k + 2 ≠ 0 by omega] at h2
  linarith

/-- **Vanishing at bad primes**: for `p ∣ 2d` and `k ≥ 1`, `c_{p^k} = 0`. -/
theorem cdCoeff_prime_pow_of_dvd (d : ℕ) {p : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) {k : ℕ}
    (hk : k ≠ 0) : cdCoeff d (p ^ k) = 0 := by
  rw [cdCoeff_prime_pow d hp, cdLocalSeries, cdEulerPoly]
  simp only [h, ↓reduceIte, Polynomial.coe_one]
  have h1 : PowerSeries.invOfUnit (1 : PowerSeries ℤ) 1 = 1 := by
    have := PowerSeries.mul_invOfUnit (1 : PowerSeries ℤ) 1 (by simp)
    rwa [one_mul] at this
  rw [h1, PowerSeries.coeff_one]; simp [hk]

/-- **Vanishing at multiples of bad primes**: if a prime `p ∣ 2d` divides `n`, then `c_n = 0`. -/
theorem cdCoeff_eq_zero_of_dvd (d : ℕ) {p n : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) (hn : p ∣ n) :
    cdCoeff d n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact cdCoeff_zero d
  obtain ⟨k, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at hn
    exact hpm hn
  rw [cdCoeff_mul d ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk) _ _).mpr
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)), cdCoeff_prime_pow_of_dvd d hp h hk, zero_mul]

/-- `c_n = 0` for even `n`. -/
theorem cdCoeff_eq_zero_of_even (d : ℕ) {n : ℕ} (hn : Even n) : cdCoeff d n = 0 :=
  cdCoeff_eq_zero_of_dvd d Nat.prime_two (dvd_mul_right 2 d) (even_iff_two_dvd.mp hn)

/-- **Mathlib's coefficients are `cdCoeff`** (odd squarefree `d`; both are `0` at `n = 0`). -/
theorem LFunction_cd_eq_cdCoeff {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (n : ℕ) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction n = cdCoeff d n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cdCoeff]
  simp only [cdCoeff, hn, ↓reduceIte, LFunction_cd_apply hd hsq hn]

/-- **The recursion on Mathlib's coefficients of `L(C_d, s)`** (odd squarefree `d`, `p ∤ 2d`):
`a_{p^{k+2}} = a_p a_{p^{k+1}} − p a_{p^k}`. -/
theorem LFunction_cd_prime_pow_succ_succ {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ 2 * d) (k : ℕ) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (k + 2)) =
      (shortCurve (-(d : ℚ) ^ 2)).LFunction p * (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (k + 1))
        - p * (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ k) := by
  simp only [LFunction_cd_eq_cdCoeff hd hsq]
  exact cdCoeff_prime_pow_succ_succ d hp h k

end ZInQ.Contrib.PSide
