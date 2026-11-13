import ZInQKernel.Multiplication.Local.FormalLogarithm
import ZInQKernel.Multiplication.Local.LogCoefficients
import ZInQKernel.Multiplication.Local.InvDiffSeries

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

/-! ### The binomial series

`S² (1 - 4Az⁴) = 1` is `invDiffSeries_sq` (`Local/InvDiffSeries.lean`). -/

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
  simp only [invDiffCoeff, ite_eq_left (show 4 * j % 4 = 0 by omega), show 4 * j / 4 = j by omega]
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
    rw [ite_eq_right (by omega), zero_div]

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
