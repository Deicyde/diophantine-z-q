import PGLight
/-! # period-glue: `S8Nonzero` reduced to a statement about one explicit matrix

Task period-glue, 2026-11-13. `S8Nonzero` (period-map, `PGLight`, unchanged) says
`Σ_{m even} θ_m(Ω(√2 + i))⁸ ≠ 0`. Proved here: `Ω(√2 + i) = Ω₀ := [[(−1+i)/2, 1], [1, −1+i]]`
exactly (`omega_cm4`), so `S8Nonzero ⇔ S8Omega0` (`s8Nonzero_iff`). `S8Omega0` is a statement about
theta constants at an explicit point of `𝔥₂` with `Im Ω₀ = diag(1/2, 1)`; its certificate is in
`docs/research/period-glue.md` §3 (`py/s8_exact.py`): `Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶` numerically to 60
digits, each `θ_m(Ω₀)⁸ ∈ {−¼, −1, −4, 0}·ϑ₀₀(i)¹⁶`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap

/-- The period matrix at the CM point `√2 + i` (discriminant `−4`). -/
def Omega0 : Matrix (Fin 2) (Fin 2) ℂ := !![(-1 + I) / 2, 1; 1, -1 + I]

theorem dF_cm4_ne : dF ((√2 : ℂ) + I) ≠ 0 := by
  unfold dF
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h3 : (√2 : ℂ) + I - 3 ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have h4 : (√2 : ℂ) + I + 1 ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) h3) h4
  exact div_ne_zero this two_ne_zero

/-- **`Ω(√2 + i) = Ω₀` (proved).** Closed form `omega_eq` (period-map) and `√2² = 2`, `i² = −1`;
the `linear_combination` coefficients are from `py/omega0_lc.py`. -/
theorem omega_cm4 : PkgI1.Omega ((√2 : ℂ) + I) = Omega0 := by
  ext i j
  rw [omega_eq, div_eq_iff dF_cm4_ne]
  fin_cases i <;> fin_cases j <;> simp only [Nf, dF, Omega0] <;> simp
  · linear_combination
      (2 * I ^ 2 + I * (√2 : ℂ) + (√2 : ℂ) + 4) / 4 * sqrt2_sq + (I * (√2 : ℂ) - √2 + 2) / 4 * I_mul_I
  · linear_combination (-1 : ℂ) * sqrt2_sq + I_mul_I
  · linear_combination (-1 : ℂ) * sqrt2_sq + I_mul_I
  · linear_combination
      (2 * I ^ 2 + I * (√2 : ℂ) + (√2 : ℂ) + 4) / 2 * sqrt2_sq + (I * (√2 : ℂ) - √2 + 2) / 2 * I_mul_I

/-- **GLUE (numerical, at an explicit matrix).** `Σ_{m even} θ_m(Ω₀)⁸ ≠ 0` for
`Ω₀ = [[(−1+i)/2, 1], [1, −1+i]]`.

Certificate (period-glue §3, `py/s8_exact.py`, VERIFIED numerically): since `(Ω₀)₀₁ = 1`, every
term factors, `θ_{(a,b)}(Ω₀) = u·ϑ[a₁, b₁+a₂]((−1+i)/2)·ϑ[a₂, b₂+a₁](−1+i)` with `u ∈ {1, −i}`;
`|exp(πi vᵀΩ₀v)| = exp(−π(v₀²/2 + v₁²))`, so truncating at `|n_k| ≤ 2` leaves a tail
`< 2.2·10⁻⁴` per theta constant; the truncated sums give `Σθ⁸ ∈ −33.9079 ± 0.01`. Exactly:
`θ_m(Ω₀)⁸ = −c_m ϑ₀₀(i)¹⁶` with `c_m = ¼, 1, 4, 0` (four, four, one, one characteristics), so
`Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶ < 0` (60 digits); a symbolic proof needs the transformation of
one-variable theta constants under `τ ↦ τ + 1`, `τ ↦ −1/τ` (Mathlib:
`jacobiTheta₂_functional_equation`) and the factorization. -/
def S8Omega0 : Prop := PkgI1.thetaSum8 Omega0 ≠ 0

/-- **`S8Nonzero ⇔ S8Omega0` (proved).** -/
theorem s8Nonzero_iff : S8Nonzero ↔ S8Omega0 := by
  unfold S8Nonzero S8Omega0
  rw [omega_cm4]

theorem s8Nonzero_of (h : S8Omega0) : S8Nonzero := s8Nonzero_iff.mpr h

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_iff
