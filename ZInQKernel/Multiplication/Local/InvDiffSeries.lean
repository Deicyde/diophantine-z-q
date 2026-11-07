import ZInQKernel.Multiplication.Local.FormalLog

/-!
# The binomial series `S = (1 - 4AT⁴)^{-1/2}`

Blueprint: `multiplication/local/logarithm-series.md` (part 2).

`S = invDiffSeries A = Σ_j binom(2j, j) Aʲ T^{4j}` satisfies `(1 - 4AT⁴) S' = 8AT³ S`
(`invDiffSeries_ode`) and hence `S² (1 - 4AT⁴) = 1` (`invDiffSeries_sq`). Both the identification
of the formal logarithm (`Local/LogSeries.lean`) and the invariant differential of the formal
group law (`FormalLog/InvDiff.lean`) use it.
-/

namespace ZInQ.Mult

open PowerSeries

variable {F : Type*} [Field F] [CharZero F]

theorem invDiffCoeff_succ_rec (A : F) (j : ℕ) :
    ((4 * j + 4 : ℕ) : F) * invDiffCoeff A (4 * j + 4) =
      8 * A * (2 * j + 1) * invDiffCoeff A (4 * j) := by
  have hc := Nat.succ_mul_centralBinom_succ j
  have hc' : ((j + 1 : ℕ) : F) * (Nat.centralBinom (j + 1) : F) =
      2 * (2 * j + 1) * (Nat.centralBinom j : F) := by exact_mod_cast hc
  simp only [invDiffCoeff]
  rw [ite_eq_left (by omega), ite_eq_left (by omega),
    show (4 * j + 4) / 4 = j + 1 by omega, show 4 * j / 4 = j by omega]
  push_cast at hc' ⊢
  rw [pow_succ]
  linear_combination (4 * A ^ j * A) * hc'

/-- The binomial series satisfies `(1 - 4Az⁴) S' = 8Az³ S`. -/
theorem invDiffSeries_ode (A : F) :
    derivative (R := F) (invDiffSeries A) =
      C (4 * A) * X ^ 4 * derivative (R := F) (invDiffSeries A) + C (8 * A) * X ^ 3 * invDiffSeries A := by
  ext n
  rw [show C (4 * A) * X ^ 4 * derivative (R := F) (invDiffSeries A) =
      C (4 * A) * (X ^ 4 * derivative (R := F) (invDiffSeries A)) by ring,
    show C (8 * A) * X ^ 3 * invDiffSeries A = C (8 * A) * (X ^ 3 * invDiffSeries A) by ring,
    map_add, coeff_derivative, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
  simp only [invDiffSeries, coeff_mk]
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 4 ∧ n = 4 * j + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 4).symm⟩
  interval_cases r
  · -- `n = 4j`
    have h1 : invDiffCoeff A (4 * j + 0 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 0 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      have h3 : invDiffCoeff A (4 * j + 0 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 0 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h3]; ring
    · ring
  · have h1 : invDiffCoeff A (4 * j + 1 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 1 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      have h3 : invDiffCoeff A (4 * j + 1 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 1 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h3]; ring
    · ring
  · have h1 : invDiffCoeff A (4 * j + 2 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 2 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      have h3 : invDiffCoeff A (4 * j + 2 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 2 - 3) = 0 := by simp only [invDiffCoeff]; rw [ite_eq_right (by omega)]
      rw [h3]; ring
    · ring
  · -- `n = 4j + 3`
    have hrec := invDiffCoeff_succ_rec A j
    rw [show 4 * j + 3 + 1 = 4 * j + 4 by omega, show 4 * j + 3 - 3 = 4 * j by omega]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk, show 4 * j + 3 - 4 + 1 = 4 * j by omega]
      push_cast at hrec ⊢
      have hj : (1 : ℕ) ≤ j := by omega
      rw [show ((4 * j - 1 : ℕ) : F) = 4 * (j : F) - 1 by
        rw [Nat.cast_sub (by omega)]; push_cast; ring]
      linear_combination hrec
    · omega
    · have hj : j = 0 := by omega
      subst hj
      push_cast at hrec ⊢
      linear_combination hrec
    · omega

/-- **Part 2.** `S² (1 - 4Az⁴) = 1`: `S = Σ binom(2j, j) Aʲ z^{4j}` is `(1 - 4Az⁴)^{-1/2}`. -/
theorem invDiffSeries_sq (A : F) : invDiffSeries A ^ 2 * (1 - C (4 * A) * X ^ 4) = 1 := by
  set S := invDiffSeries A
  set G := S ^ 2 * (1 - C (4 * A) * X ^ 4) with hG
  have hode := invDiffSeries_ode A
  have hD : derivative (R := F) G = 0 := by
    rw [hG, Derivation.leibniz, Derivation.leibniz_pow, map_sub, Derivation.map_one_eq_zero,
      Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul]
    have h8 : C (8 * A) = (2 : PowerSeries F) * C (4 * A) := by
      rw [show (8 : F) * A = 2 * (4 * A) by ring, map_mul]; rfl
    rw [h8] at hode
    linear_combination (2 * S) * hode
  ext n
  rcases n with _ | n
  · simp [hG, S, invDiffSeries, invDiffCoeff, sq]
  · have := congrArg (coeff n) hD
    rw [coeff_derivative, map_zero] at this
    have hn : ((n : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [coeff_one, ite_eq_right (Nat.succ_ne_zero n)]
    exact (mul_eq_zero.mp this).resolve_right hn

end ZInQ.Mult
