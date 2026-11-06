import ZInQKernel.Multiplication.Local.FormalLogarithm
import ZInQKernel.Multiplication.Local.LogCoefficients

/-!
# The formal logarithm of `E` is a binomial series

Blueprint: `multiplication/local/logarithm-series.md`.

For `W : y² = x³ + A x` over a field of characteristic `0`, with `z = -x/y`:

1. the inverse abscissa `u = 1/x` is the unique power series with `u = z² (1 + A u²)`
   (`uSeries_eq`, `uSeries_unique`), and `(1 - 2Az²u)² = 1 - 4Az⁴` with constant term `1`
   (`one_sub_uSeries_sq`); `u = ω/z` (`X_mul_uSeries`); for `E` (`A = -d²`), `u = z²` times a unit
   of `ℤ[s]⟦z⟧` (`uSeries_genE_unit`);
2. the invariant differential `dx/(2y) = z u'/(2u) dz` is `S(z) dz` with
   `S = Σ_j binom(2j, j) Aʲ z^{4j} = (1 - 4Az⁴)^{-1/2}` (`invDiffSeries_sq`,
   `X_mul_derivative_uSeries`, `invDiffSeries_mul`);
3. hence the formal logarithm, the formal integral of `S` with constant term `0`, is
   `Σ_j binom(2j, j) Aʲ T^{4j+1}/(4j+1)` (`formalLog`, `derivative_formalLog`); for `E` this is
   `Σ_j (-1)ʲ binom(2j, j) d^{2j} T^{4j+1}/(4j+1)` (`coeff_formalLog_genE`).

With `A = -d²` the identities read `z²(1 - d²u²) = u`, `1 + 2d²z²u = √(1 + 4d²z⁴)` and
`(1 + 4d²z⁴)^{-1/2} = Σ (-1)ʲ binom(2j, j) d^{2j} z^{4j}`, as in the article.
-/

namespace ZInQ.Mult

open PowerSeries

variable {F : Type*} [Field F] [CharZero F]

/-- The inverse abscissa `u = 1/x = ω/z` as a power series in `z`. -/
def uSeries {R : Type*} [CommRing R] (A : R) : PowerSeries R := mk fun n => omegaCoeff A (n + 1)

theorem X_mul_uSeries {R : Type*} [CommRing R] (A : R) : X * uSeries A = omegaSeries A := by
  ext n
  rcases n with _ | n
  · simp [coeff_omegaSeries, omegaCoeff_zero]
  · rw [coeff_succ_X_mul, uSeries, coeff_mk, coeff_omegaSeries]

omit [CharZero F] in
/-- **Part 1.** `u = z² (1 + A u²)`. -/
theorem uSeries_eq (A : F) : uSeries A = X ^ 2 * (1 + C A * uSeries A ^ 2) := by
  have h := omegaSeries_eq A
  rw [← X_mul_uSeries] at h
  have hX : (X : PowerSeries F) ≠ 0 := X_ne_zero
  apply mul_left_cancel₀ hX
  rw [h]; ring

omit [CharZero F] in
/-- **Part 1.** `u` is the unique power series with `u = z² (1 + A u²)`. -/
theorem uSeries_unique (A : F) {f : PowerSeries F} (hf : f = X ^ 2 * (1 + C A * f ^ 2)) :
    f = uSeries A := by
  have h : X * f = X ^ 3 + C A * X * (X * f) ^ 2 := by
    conv_lhs => rw [hf]
    ring
  have := omegaSeries_unique A h
  rw [← X_mul_uSeries] at this
  exact mul_left_cancel₀ X_ne_zero this

omit [CharZero F] in
/-- **Part 1.** `(1 - 2Az²u)² = 1 - 4Az⁴`, and `1 - 2Az²u` has constant term `1`: it is the
square root of `1 - 4Az⁴` with constant term `1`. -/
theorem one_sub_uSeries_sq (A : F) :
    (1 - C (2 * A) * X ^ 2 * uSeries A) ^ 2 = 1 - C (4 * A) * X ^ 4 ∧
      constantCoeff (1 - C (2 * A) * X ^ 2 * uSeries A) = 1 := by
  refine ⟨?_, by simp⟩
  have h := uSeries_eq A
  have h2 : C (2 * A) = (2 : PowerSeries F) * C A := by rw [map_mul]; rfl
  have h4 : C (4 * A) = (4 : PowerSeries F) * C A := by rw [map_mul]; rfl
  rw [h2, h4]
  linear_combination (-(4 : PowerSeries F) * C A * X ^ 2) * h

/-! ### The binomial series -/

theorem invDiffCoeff_succ_rec (A : F) (j : ℕ) :
    ((4 * j + 4 : ℕ) : F) * invDiffCoeff A (4 * j + 4) =
      8 * A * (2 * j + 1) * invDiffCoeff A (4 * j) := by
  have hc := Nat.succ_mul_centralBinom_succ j
  have hc' : ((j + 1 : ℕ) : F) * (Nat.centralBinom (j + 1) : F) =
      2 * (2 * j + 1) * (Nat.centralBinom j : F) := by exact_mod_cast hc
  simp only [invDiffCoeff]
  rw [if_pos (by omega), if_pos (by omega),
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
    have h1 : invDiffCoeff A (4 * j + 0 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 0 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      have h3 : invDiffCoeff A (4 * j + 0 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 0 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      rw [h3]; ring
    · ring
  · have h1 : invDiffCoeff A (4 * j + 1 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 1 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      have h3 : invDiffCoeff A (4 * j + 1 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 1 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      rw [h3]; ring
    · ring
  · have h1 : invDiffCoeff A (4 * j + 2 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
    rw [h1, zero_mul]
    split_ifs with ha hb
    · rw [coeff_derivative, coeff_mk]
      have h2 : invDiffCoeff A (4 * j + 2 - 4 + 1) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      have h3 : invDiffCoeff A (4 * j + 2 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
      rw [h2, h3]; ring
    · omega
    · have h3 : invDiffCoeff A (4 * j + 2 - 3) = 0 := by simp only [invDiffCoeff]; rw [if_neg (by omega)]
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
    rw [coeff_one, if_neg (Nat.succ_ne_zero n)]
    exact (mul_eq_zero.mp this).resolve_right hn

/-- **Part 2.** `S (1 - 2Az²u) = 1`: the invariant differential `dz/(1 - 2Az²u)` is
`S(z) dz = dz/√(1 - 4Az⁴)`. -/
theorem invDiffSeries_mul (A : F) :
    invDiffSeries A * (1 - C (2 * A) * X ^ 2 * uSeries A) = 1 := by
  set T := invDiffSeries A * (1 - C (2 * A) * X ^ 2 * uSeries A) with hT
  have hsq : T ^ 2 = 1 := by
    rw [hT, mul_pow, (one_sub_uSeries_sq A).1, invDiffSeries_sq]
  have hc : constantCoeff T = 1 := by
    rw [hT, map_mul, (one_sub_uSeries_sq A).2]
    simp [invDiffSeries, invDiffCoeff, ← coeff_zero_eq_constantCoeff_apply]
  have : (T - 1) * (T + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, hc, map_one, map_zero] at this
    norm_num at this

/-- **Part 2.** `dx/(2y) = z u'/(2u) dz = S dz`: `z u' = 2 u S`. -/
theorem X_mul_derivative_uSeries (A : F) :
    X * derivative (R := F) (uSeries A) = 2 * uSeries A * invDiffSeries A := by
  have h := uSeries_eq A
  -- differentiate `u = z² (1 + A u²)`
  have hd : derivative (R := F) (uSeries A) * (1 - C (2 * A) * X ^ 2 * uSeries A) =
      2 * X * (1 + C A * uSeries A ^ 2) := by
    have := congrArg (derivative (R := F)) h
    rw [Derivation.leibniz, Derivation.leibniz_pow, map_add, Derivation.map_one_eq_zero,
      Derivation.leibniz, derivative_C, Derivation.leibniz_pow, derivative_X] at this
    simp only [smul_eq_mul, nsmul_eq_mul] at this
    have h2 : C (2 * A) = (2 : PowerSeries F) * C A := by rw [map_mul]; rfl
    rw [h2]
    push_cast at this
    linear_combination this
  have hm := invDiffSeries_mul A
  have key : X * derivative (R := F) (uSeries A) * (1 - C (2 * A) * X ^ 2 * uSeries A) =
      2 * uSeries A := by
    rw [mul_assoc, hd]
    conv_rhs => rw [h]
    ring
  calc X * derivative (R := F) (uSeries A)
      = X * derivative (R := F) (uSeries A) * (1 - C (2 * A) * X ^ 2 * uSeries A) *
          invDiffSeries A := by
        rw [mul_assoc, mul_comm (1 - _), hm, mul_one]
    _ = 2 * uSeries A * invDiffSeries A := by rw [key]

/-! ### The curve `E` -/

theorem invDiffCoeff_genE (j : ℕ) :
    invDiffCoeff (-genD ^ 2) (4 * j) = (-1) ^ j * (Nat.centralBinom j : K0) * genD ^ (2 * j) := by
  simp only [invDiffCoeff, if_pos (show 4 * j % 4 = 0 by omega), show 4 * j / 4 = j by omega]
  rw [neg_pow, pow_mul]; ring

/-- **Part 3.** The formal logarithm of `E` is the binomial series
`Σ_j (-1)ʲ binom(2j, j) d^{2j} T^{4j+1}/(4j + 1)`. -/
theorem coeff_formalLog_genE (n : ℕ) :
    coeff n (formalLog (-genD ^ 2 : K0)) =
      if n % 4 = 1 then (logCoeff (n / 4) : K0) * genD ^ (2 * (n / 4)) else 0 := by
  rw [formalLog, coeff_mk, logCoeffA]
  split_ifs with h0 h1 h1
  · omega
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j, n = 4 * j + 1 := ⟨n / 4, by omega⟩
    rw [show 4 * j + 1 - 1 = 4 * j by omega, show (4 * j + 1) / 4 = j by omega,
      invDiffCoeff_genE, logCoeff]
    push_cast; ring
  · simp only [invDiffCoeff]
    rw [if_neg (by omega), zero_div]

/-- **Part 1, for `E`.** `u = z²` times a unit of `ℤ[s]⟦z⟧`. -/
theorem uSeries_genE_unit :
    ∃ w : PowerSeries Zs, IsUnit w ∧
      uSeries (-genD ^ 2 : K0) = X ^ 2 * PowerSeries.map Zs.toK0 w := by
  refine ⟨mk fun n => omegaCoeff (-genDZ ^ 2) (n + 3), ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk,
      omegaCoeff_three]
    exact isUnit_one
  · refine PowerSeries.ext fun n => ?_
    rw [uSeries, coeff_mk, coeff_X_pow_mul']
    split_ifs with h
    · rw [coeff_map, coeff_mk, omegaCoeff_map, show n - 2 + 3 = n + 1 by omega]
      simp
    · interval_cases n
      · exact omegaCoeff_one (-genD ^ 2 : K0)
      · exact omegaCoeff_two (-genD ^ 2 : K0)

end ZInQ.Mult
