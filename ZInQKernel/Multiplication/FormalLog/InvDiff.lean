import ZInQKernel.Multiplication.Local.InvDiffSeries
import ZInQKernel.Multiplication.Local.FormalGroupLaw

/-!
# The invariant differential series `S = (1 - 4AT⁴)^{-1/2}`

`S = invDiffSeries A = Σ_j binom(2j, j) Aʲ T^{4j}` satisfies `S² (1 - 4AT⁴) = 1`
(`invDiffSeries_sq`) and `S (1 - 2A T ω(T)) = 1` (`invDiffSeries_mul_omega`): `S(z) dz` is
the expansion `dz/(1 - 2Azω)` of the invariant differential `dx/(2y)` of `y² = x³ + A x`.

The first identity is proved in `Local/InvDiffSeries.lean`, which `Local/LogSeries.lean` also
imports.
-/

namespace ZInQ.Mult

open PowerSeries

variable {F : Type*} [Field F] [CharZero F]

/-- **`S (1 - 2A T ω(T)) = 1`**: the invariant differential `dz/(1 - 2Azω)` is `S(z) dz`. -/
theorem invDiffSeries_mul_omega (A : F) :
    invDiffSeries A * (1 - C (2 * A) * X * omegaSeries A) = 1 := by
  set V := 1 - C (2 * A) * X * omegaSeries A with hV
  have hω := omegaSeries_eq A
  have h2 : C (2 * A) = (2 : PowerSeries F) * C A := by rw [map_mul]; rfl
  have h4 : C (4 * A) = (4 : PowerSeries F) * C A := by rw [map_mul]; rfl
  have hVsq : V ^ 2 = 1 - C (4 * A) * X ^ 4 := by
    rw [hV, h2, h4]
    linear_combination (-(4 : PowerSeries F) * C A * X) * hω
  set T := invDiffSeries A * V with hT
  have hsq : T ^ 2 = 1 := by
    rw [hT, mul_pow, hVsq, invDiffSeries_sq]
  have hc : constantCoeff T = 1 := by
    rw [hT, hV]
    simp only [map_mul, map_sub, map_one, PowerSeries.constantCoeff_X, mul_zero, zero_mul,
      sub_zero, mul_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, invDiffSeries, PowerSeries.coeff_mk,
      invDiffCoeff_zero]
  have : (T - 1) * (T + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, hc, map_one, map_zero] at this
    norm_num at this

/-- `d/dT log(T) = S`. -/
theorem derivative_formalLog_aux (A : F) :
    derivative (R := F) (formalLog A) = invDiffSeries A := by
  ext n
  rw [coeff_derivative, formalLog, invDiffSeries, coeff_mk, coeff_mk]
  have := logCoeffA_mul A (r := n + 1) (by omega)
  push_cast at this
  rw [this]

end ZInQ.Mult
