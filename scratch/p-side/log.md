# p-side results log

## P1 — ZInQKernel/Contrib/PSide/APZero.lean (compiles, no sorry; VERIFIED 2026-11-12 22:15)
- `card_solutions_eq` : over a finite field of odd char, #{(x,y): y²=g x} = #F + Σ_x χ(g x).
- `charSum_odd_eq_zero` : χ(−1) = −1 and g odd ⇒ Σ χ(g x) = 0.
- `LFunction_cd_apply_prime_eq_neg_charSum` : a_p(C_d) = −Σ_x χ(x³ − d²x)  (d odd sqfree, p ∤ 2d).
- `LFunction_cd_apply_prime_of_mod_four_eq_three` : p ≡ 3 (4), p ∤ 2d ⇒ a_p(C_d) = 0.  [P1]
- `natCard_point_cd_of_mod_four_eq_three` : #C_d(F_p) = p + 1.  [P1, point-count form]
- `LFunction_cd_apply_prime_of_mod_four_eq_three'` : same with hypothesis p ∤ d.

## P2 — ZInQKernel/Contrib/PSide/Coeff.lean (compiles, no sorry; VERIFIED 22:30)
For every d (no hypothesis) unless noted:
- `cdCoeff_zero`, `cdCoeff_one`; `cdArith d : ArithmeticFunction ℤ`, `isMultiplicative_cdArith`.
- `cdCoeff_mul` : Coprime m n → c(mn) = c(m) c(n).
- `cdCoeff_prime_pow` : c(p^k) = [T^k] 1/cdEulerPoly d p.
- `cdCoeff_prime` : c(p) = if p ∣ 2d then 0 else p + 1 − #C_d(F_p).
- `cdEulerPoly_of_not_dvd` : cdEulerPoly d p = 1 − c(p) T + p T² for p ∤ 2d.
- `cdCoeff_prime_pow_succ_succ` : p ∤ 2d ⇒ c(p^{k+2}) = c(p) c(p^{k+1}) − p c(p^k).
- `cdCoeff_prime_pow_of_dvd` : p ∣ 2d, k ≠ 0 ⇒ c(p^k) = 0; `cdCoeff_eq_zero_of_dvd` (p ∣ 2d, p ∣ n ⇒ c(n) = 0); `cdCoeff_eq_zero_of_even`.
- d odd sqfree: `LFunction_cd_eq_cdCoeff` (Mathlib LFunction n = cdCoeff d n, all n), `LFunction_cd_prime_pow_succ_succ` (recursion on Mathlib's coefficients).

## P3 — ZInQKernel/Contrib/PSide/BadPrimes.lean (compiles, no sorry; VERIFIED 22:36)
- `cuspEquiv F : F ≃ {(x,y) : y² = x³}` (t ↦ (t², t³)); `natCard_cusp`.
- `natCard_cd_of_dvd` : p ∣ d ⇒ #{y² = x³ − d²x over F_p} = p.
- `natCard_cd_two` : d odd ⇒ #{y² = x³ − d²x over F_2} = 2 (decide).
- `LFunction_cd_apply_prime_eq_sub_card_of_dvd` : d odd sqfree, p ∣ 2d ⇒ a_p = p − N_p (= 0).  [P3]
- `LFunction_cd_apply_prime_eq_sub_card_all` : d odd sqfree, every prime p ⇒ a_p = p − N_p.
