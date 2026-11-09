import Mathlib

/-!
# The chain rule for substitution into a multivariate power series

For `a ∈ R⟦σ⟧` with constant coefficient `0` and `f ∈ R⟦X⟧`,
`∂ᵢ f(a) = f'(a) · ∂ᵢ a` (`pderiv_subst`). Mathlib has the one-variable case
(`PowerSeries.derivative_subst`); the proof is the same: the coefficient `e` of `f(a)` only
depends on the coefficients of `f` of degree `≤ deg e` (`coeff_subst_congr`), and the chain rule
holds for polynomials (`Derivation.comp_aeval_eq`).
-/

namespace ZInQ.Mult

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommRing R]

/-- If `a` has constant coefficient `0`, then `coeff e (aᵈ) = 0` for `deg e < d`. -/
theorem coeff_pow_eq_zero_of_degree_lt {a : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    {e : σ →₀ ℕ} {d : ℕ} (h : e.degree < d) : coeff e (a ^ d) = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast h)
    (le_order_pow_of_constantCoeff_eq_zero d ha))

/-- The coefficient `e` of `f(a)` only depends on the coefficients of `f` of degree
`≤ deg e`. -/
theorem coeff_subst_congr {a : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    {f g : PowerSeries R} (e : σ →₀ ℕ)
    (h : ∀ d ≤ e.degree, PowerSeries.coeff d f = PowerSeries.coeff d g) :
    coeff e (PowerSeries.subst a f) = coeff e (PowerSeries.subst a g) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : d ≤ e.degree
  · rw [h d hd]
  · rw [coeff_pow_eq_zero_of_degree_lt ha (not_le.mp hd), smul_zero, smul_zero]

/-- The chain rule for polynomials. -/
theorem pderiv_subst_coe (i : σ) {a : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    (p : Polynomial R) :
    pderiv i (PowerSeries.subst a (p : PowerSeries R)) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) (p : PowerSeries R)) * pderiv i a := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_coe hs, PowerSeries.derivative_coe, PowerSeries.subst_coe hs,
    Derivation.comp_aeval_eq, smul_eq_mul]

/-- **The chain rule** `∂ᵢ f(a) = f'(a) · ∂ᵢ a` for `a` with constant coefficient `0`. -/
theorem pderiv_subst (i : σ) {a : MvPowerSeries σ R} (ha : constantCoeff a = 0)
    (f : PowerSeries R) :
    pderiv i (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * pderiv i a := by
  classical
  ext n
  set N := n.degree + 2 with hN
  have h1 : coeff (n + Finsupp.single i 1) (PowerSeries.subst a f) =
      coeff (n + Finsupp.single i 1)
        (PowerSeries.subst a ((PowerSeries.trunc N f : Polynomial R) : PowerSeries R)) := by
    refine coeff_subst_congr ha _ fun d hd => ?_
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left]
    rw [map_add, Finsupp.degree_single] at hd
    omega
  rw [coeff_pderiv, h1, ← coeff_pderiv, pderiv_subst_coe i ha, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  congr 1
  refine coeff_subst_congr ha _ fun d hd => ?_
  have hle : pq.1.degree ≤ n.degree := by
    rw [← (Finset.HasAntidiagonal.mem_antidiagonal.mp hpq), map_add]; omega
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, Polynomial.coeff_coe,
    PowerSeries.coeff_trunc, ite_eq_left (by omega)]

end ZInQ.Mult
