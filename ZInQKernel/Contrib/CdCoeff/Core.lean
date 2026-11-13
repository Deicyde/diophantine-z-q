import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Core API for the coefficients `cdCoeff` of `L(C_d, s)`

`ZInQ.Literature.cdCoeff d n` (in `ZInQKernel/RouteK/Rank/LFunctionCd.lean`) is defined from the
Euler polynomials `cdEulerPoly d p` by the factorization of `n`. This file proves its basic API,
issue #37 target P2 (core part; the recursion `c_{k+2} = a_p c_{k+1} − p c_k` is elsewhere).

All results except the comparison with Mathlib's `L`-function hold for every `d : ℕ`.

## Main results

* `cdCoeff_zero`, `cdCoeff_one`, `cdCoeff_of_ne_zero`.
* `cdCoeff_mul_of_coprime`, and `cdArith d : ArithmeticFunction ℤ` with
  `isMultiplicative_cdArith`.
* `cdCoeff_prime_pow`: `cdCoeff d (p ^ k) = [T ^ k] (1 / cdEulerPoly d p)`.
* `cdCoeff_prime_cdModel`, `cdCoeff_prime`, `cdCoeff_prime_of_dvd`, `cdCoeff_prime_of_not_dvd`,
  `cdCoeff_prime_eq_sub_card`: the coefficient at a prime `p`.
* `cdCoeff_prime_pow_of_dvd`, `cdCoeff_eq_zero_of_dvd`: vanishing at multiples of `p ∣ 2d`.
* `cdCoeff_eq_LFunction`, `cdArith_eq_LFunction` (odd squarefree `d`, every `n`, including `0`).
-/

namespace ZInQ.Contrib.CdCoeff

open ZInQ.Literature WeierstrassCurve ArithmeticFunction

/-- The constant coefficient of `1 / cdEulerPoly d p` is `1`. -/
theorem coeff_zero_invOfUnit_cdEulerPoly (d p : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
  simp

/-- `1 / cdEulerPoly d p = 1` at a bad prime `p ∣ 2d`. -/
theorem invOfUnit_cdEulerPoly_of_dvd {d p : ℕ} (h : p ∣ 2 * d) :
    PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1 = 1 := by
  have hP : cdEulerPoly d p = 1 := by simp [cdEulerPoly, h]
  rw [hP, Polynomial.coe_one]
  have h1 := PowerSeries.mul_invOfUnit (1 : PowerSeries ℤ) 1 (by simp)
  rwa [one_mul] at h1

@[simp]
theorem cdCoeff_zero (d : ℕ) : cdCoeff d 0 = 0 := by
  simp [cdCoeff]

@[simp]
theorem cdCoeff_one (d : ℕ) : cdCoeff d 1 = 1 := by
  simp [cdCoeff]

theorem cdCoeff_of_ne_zero (d : ℕ) {n : ℕ} (hn : n ≠ 0) :
    cdCoeff d n = n.factorization.prod fun p k =>
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  simp [cdCoeff, hn]

/-- **Multiplicativity** of `cdCoeff d` on coprime arguments, for every `d`. -/
theorem cdCoeff_mul_of_coprime (d : ℕ) {m n : ℕ} (h : m.Coprime n) :
    cdCoeff d (m * n) = cdCoeff d m * cdCoeff d n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp
  rw [cdCoeff_of_ne_zero d (mul_ne_zero hm hn), cdCoeff_of_ne_zero d hm, cdCoeff_of_ne_zero d hn,
    Nat.factorization_mul_of_coprime h, Finsupp.prod_add_index_of_disjoint]
  simpa [Nat.support_factorization] using h.disjoint_primeFactors

/-- `cdCoeff d` as an arithmetic function. -/
noncomputable def cdArith (d : ℕ) : ArithmeticFunction ℤ :=
  ⟨cdCoeff d, cdCoeff_zero d⟩

@[simp]
theorem cdArith_apply (d n : ℕ) : cdArith d n = cdCoeff d n := rfl

theorem isMultiplicative_cdArith (d : ℕ) : (cdArith d).IsMultiplicative :=
  ⟨by simp, fun h => by simpa using cdCoeff_mul_of_coprime d h⟩

/-- **Prime powers**: `cdCoeff d (p ^ k)` is the coefficient of `T ^ k` in `1 / cdEulerPoly d p`,
for every `d` (including `k = 0`). -/
theorem cdCoeff_prime_pow (d : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cdCoeff d (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  rw [cdCoeff_of_ne_zero d (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (coeff_zero_invOfUnit_cdEulerPoly d p)]

/-- The coefficient at a prime, through the integral model `cdModel (ZMod p) d`. -/
theorem cdCoeff_prime_cdModel (d : ℕ) {p : ℕ} (hp : p.Prime) :
    cdCoeff d p = if p ∣ 2 * d then 0
      else (p : ℤ) + 1 - Nat.card (cdModel (ZMod p) d).toAffine.Point := by
  have h := cdCoeff_prime_pow d hp 1
  rw [pow_one] at h
  rw [h, coeff_one_invOfUnit _ (cdEulerPoly_coeff_zero d p)]
  unfold cdEulerPoly
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

/-- **The coefficient at a prime** `p`, for every `d`: `a_p = p + 1 − #C_d(𝔽_p)` if `p ∤ 2d`,
and `0` if `p ∣ 2d`. -/
theorem cdCoeff_prime (d p : ℕ) [hp : Fact p.Prime] :
    cdCoeff d p = if p ∣ 2 * d then 0
      else (p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point := by
  rw [cdCoeff_prime_cdModel d hp.out, cdModel_eq_shortCurve]

theorem cdCoeff_prime_of_dvd (d : ℕ) {p : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) :
    cdCoeff d p = 0 := by
  simp [cdCoeff_prime_cdModel d hp, h]

theorem cdCoeff_prime_of_not_dvd (d p : ℕ) [Fact p.Prime] (h : ¬ p ∣ 2 * d) :
    cdCoeff d p = (p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point := by
  simp [cdCoeff_prime, h]

/-- `a_p` as an affine point count: `p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}` for `p ∤ 2d`. -/
theorem cdCoeff_prime_eq_sub_card (d p : ℕ) [Fact p.Prime] (h : ¬ p ∣ 2 * d) :
    cdCoeff d p =
      p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  rw [cdCoeff_prime_of_not_dvd d p h, natCard_point_shortCurve_zmod p h]
  push_cast; ring

/-- **Vanishing at bad prime powers**: `cdCoeff d (p ^ k) = 0` for `p ∣ 2d`, `k ≠ 0`. -/
theorem cdCoeff_prime_pow_of_dvd (d : ℕ) {p : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) {k : ℕ}
    (hk : k ≠ 0) : cdCoeff d (p ^ k) = 0 := by
  simp [cdCoeff_prime_pow d hp, invOfUnit_cdEulerPoly_of_dvd h, PowerSeries.coeff_one, hk]

/-- **Vanishing at multiples of bad primes**: `cdCoeff d n = 0` if a prime `p ∣ 2d` divides `n`. -/
theorem cdCoeff_eq_zero_of_dvd (d : ℕ) {p n : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) (hn : p ∣ n) :
    cdCoeff d n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact cdCoeff_zero d
  rw [cdCoeff_of_ne_zero d hn0, Finsupp.prod]
  have hmem : p ∈ n.factorization.support := by
    rw [Nat.support_factorization, Nat.mem_primeFactors]; exact ⟨hp, hn, hn0⟩
  refine Finset.prod_eq_zero hmem ?_
  simp [invOfUnit_cdEulerPoly_of_dvd h, PowerSeries.coeff_one,
    Finsupp.mem_support_iff.mp hmem]

/-- **`cdCoeff` is Mathlib's `L(C_d, s)` coefficient**, for odd squarefree `d` and every `n`
(including `n = 0`, where both are `0`). -/
theorem cdCoeff_eq_LFunction {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (n : ℕ) :
    cdCoeff d n = (shortCurve (-(d : ℚ) ^ 2)).LFunction n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [cdCoeff_of_ne_zero d hn, LFunction_cd_apply hd hsq hn]

theorem cdArith_eq_LFunction {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    cdArith d = (shortCurve (-(d : ℚ) ^ 2)).LFunction :=
  ArithmeticFunction.ext fun n => cdCoeff_eq_LFunction hd hsq n

end ZInQ.Contrib.CdCoeff
