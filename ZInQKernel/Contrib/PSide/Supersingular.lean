import ZInQKernel.Contrib.PSide.Hasse

/-!
# The coefficients `c_{p^k}` of `L(C_d, s)` at `p ≡ 3 (mod 4)` (supplement to P1, P2)

For a prime `p ≡ 3 (mod 4)` with `p ∤ 2d`, `c_p = 0` (P1, here for every `d` via the Jacobsthal
sum of `Hasse.lean`), so the recursion of `Coeff.lean` gives `c_{p^{2k+1}} = 0` and
`c_{p^{2k}} = (−p)^k`: the Euler factor is `(1 + p^{1−2s})^{−1}`.
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve

/-- `c_p = 0` for `p ≡ 3 (mod 4)`, `p ∤ 2d` (every `d`). -/
theorem cdCoeff_prime_of_mod_four_eq_three (d : ℕ) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (h : ¬ p ∣ 2 * d) : cdCoeff d p = 0 := by
  have := Fact.mk hp
  rw [cdCoeff_prime_eq_neg_jac d h, jac,
    charSum_odd_eq_zero (quadraticChar_zmod_neg_one_of_mod_four hp4) _ (fun x => by ring),
    neg_zero]

/-- **The prime-power coefficients at `p ≡ 3 (mod 4)`**: `c_{p^{2k+1}} = 0` and
`c_{p^{2k}} = (−p)^k`, for `p ∤ 2d` (every `d`). -/
theorem cdCoeff_prime_pow_of_mod_four_eq_three (d : ℕ) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (h : ¬ p ∣ 2 * d) (k : ℕ) :
    cdCoeff d (p ^ (2 * k)) = (-(p : ℤ)) ^ k ∧ cdCoeff d (p ^ (2 * k + 1)) = 0 := by
  have h0 := cdCoeff_prime_of_mod_four_eq_three d hp hp4 h
  induction k with
  | zero => simp [cdCoeff_one, h0]
  | succ k ih =>
    have e1 : cdCoeff d (p ^ (2 * (k + 1))) = -(p : ℤ) * (-(p : ℤ)) ^ k := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, cdCoeff_prime_pow_succ_succ d hp h, h0, ih.1]
      ring
    refine ⟨by rw [e1, pow_succ]; ring, ?_⟩
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, cdCoeff_prime_pow_succ_succ d hp h, h0,
      ih.2]
    ring

/-- The same on Mathlib's coefficients of `L(C_d, s)` (odd squarefree `d`). -/
theorem LFunction_cd_prime_pow_of_mod_four_eq_three {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (h : ¬ p ∣ 2 * d) (k : ℕ) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (2 * k)) = (-(p : ℤ)) ^ k ∧
      (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ (2 * k + 1)) = 0 := by
  simp only [LFunction_cd_eq_cdCoeff hd hsq]
  exact cdCoeff_prime_pow_of_mod_four_eq_three d hp hp4 h k

end ZInQ.Contrib.PSide
