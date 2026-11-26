import ZInQKernel.Contrib.OneProof.HRankD2.LSeriesHasseWeil

/-!
# The Hasse–Weil Euler product on global minimal equations

For a global minimal equation `E₀` over `ℚ` (`IsGlobalMinimalQ`) with `Δ ≠ 0`, this file
writes Mathlib's `WeierstrassCurve.LSeries` as the Euler product of Silverman, *The Arithmetic
of Elliptic Curves*, 2nd ed. (GTM 106, Springer, 2009), App. C, §16:

  `L(E/ℚ, s) = ∏_p L_p(p^{-s})^{-1}`,

with `L_p(p^{-s})` equal to `1 - a_p p^{-s} + p^{1-2s}` at good primes (`hwLocalFactor_good`),
`1 - p^{-s}` or `1 + p^{-s}` at split or nonsplit multiplicative primes
(`hwLocalFactor_split`, `hwLocalFactor_nonsplit`) and `1` at additive primes
(`hwLocalFactor_additive`).

`hasProd_LSeries_hasseWeil` holds at every `s` where the Hasse–Weil Dirichlet series
converges absolutely. By Hasse's bound `|a_p| ≤ 2√p` (Silverman, AEC, Thm. V.1.1) this
holds on the half-plane `Re s > 3/2` (AEC, App. C, §16); Hasse's bound is not in Mathlib,
so absolute convergence is a hypothesis here, and the theorem says nothing off the
half-plane of absolute convergence.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.RankModel

open Polynomial WeierstrassCurve

/-- The local Euler factor `L_p(p^{-s})`: the Hasse–Weil local polynomial `hwEulerPoly E₀ p`
evaluated at `T = p^{-s}`. -/
noncomputable def hwLocalFactor (E₀ : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  ((hwEulerPoly E₀ p).map (Int.castRingHom ℂ)).eval ((p : ℂ) ^ (-s))

/-- Good reduction (`p ∤ Δ`): `L_p(p^{-s}) = 1 - a_p p^{-s} + p^{1-2s}`, with
`a_p = p + 1 - #Ẽ(𝔽_p)`. -/
theorem hwLocalFactor_good (E₀ : WeierstrassCurve ℤ) {p : ℕ} (hp : p ≠ 0)
    (h : ¬ (p : ℤ) ∣ E₀.Δ) (s : ℂ) :
    hwLocalFactor E₀ p s = 1 - (((p : ℤ) + 1 - Nat.card (hwReduction E₀ p).toAffine.Point : ℤ)
      : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s) := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h2 : (p : ℂ) ^ (1 - 2 * s) = p * ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [show 1 - 2 * s = 1 + (-s + -s) by ring, Complex.cpow_add _ _ hp',
      Complex.cpow_add _ _ hp', Complex.cpow_one, sq]
  rw [h2, hwLocalFactor, hwEulerPoly]
  simp [h]

/-- Split multiplicative reduction: `L_p(p^{-s}) = 1 - p^{-s}`. -/
theorem hwLocalFactor_split (E₀ : WeierstrassCurve ℤ) {p : ℕ} (h : (p : ℤ) ∣ E₀.Δ)
    (hc : ¬ (p : ℤ) ∣ E₀.c₄) (hs : (tangentPolynomial (hwReduction E₀ p)).Splits) (s : ℂ) :
    hwLocalFactor E₀ p s = 1 - (p : ℂ) ^ (-s) := by
  rw [hwLocalFactor, hwEulerPoly]
  simp [h, hc, hs]

/-- Nonsplit multiplicative reduction: `L_p(p^{-s}) = 1 + p^{-s}`. -/
theorem hwLocalFactor_nonsplit (E₀ : WeierstrassCurve ℤ) {p : ℕ} (h : (p : ℤ) ∣ E₀.Δ)
    (hc : ¬ (p : ℤ) ∣ E₀.c₄) (hs : ¬ (tangentPolynomial (hwReduction E₀ p)).Splits) (s : ℂ) :
    hwLocalFactor E₀ p s = 1 + (p : ℂ) ^ (-s) := by
  rw [hwLocalFactor, hwEulerPoly]
  simp [h, hc, hs]

/-- Additive reduction: `L_p(p^{-s}) = 1`. -/
theorem hwLocalFactor_additive (E₀ : WeierstrassCurve ℤ) {p : ℕ} (h : (p : ℤ) ∣ E₀.Δ)
    (hc : (p : ℤ) ∣ E₀.c₄) (s : ℂ) : hwLocalFactor E₀ p s = 1 := by
  rw [hwLocalFactor, hwEulerPoly]
  simp [h, hc]

/-- A power series with integer coefficients `Q = 1 / P`, summed at a point `x` where it
converges absolutely, is `P(x)⁻¹`. -/
theorem tsum_invOfUnit_eq_inv (P : ℤ[X]) (hP : P.coeff 0 = 1) (x : ℂ)
    (hsum : Summable fun e : ℕ =>
      ‖((PowerSeries.coeff e (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) : ℤ) : ℂ) * x ^ e‖) :
    ∑' e : ℕ, ((PowerSeries.coeff e (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) : ℤ) : ℂ) *
      x ^ e = ((P.map (Int.castRingHom ℂ)).eval x)⁻¹ := by
  set Q := PowerSeries.invOfUnit (P : PowerSeries ℤ) 1 with hQ
  have hPQ : (P : PowerSeries ℤ) * Q = 1 := by
    refine PowerSeries.mul_invOfUnit _ _ ?_
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP]; rfl
  have hfin : ∀ i ∉ P.support, ((P.coeff i : ℤ) : ℂ) * x ^ i = 0 := fun i hi => by
    simp [Polynomial.notMem_support_iff.mp hi]
  have hPx : (P.map (Int.castRingHom ℂ)).eval x = ∑' i : ℕ, ((P.coeff i : ℤ) : ℂ) * x ^ i := by
    rw [tsum_eq_sum hfin, Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    simp
  have hnorm : Summable fun i : ℕ => ‖((P.coeff i : ℤ) : ℂ) * x ^ i‖ :=
    summable_of_ne_finset_zero (s := P.support) fun i hi => by rw [hfin i hi, norm_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [hPx, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hsum]
  have hterm : ∀ n : ℕ, (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((P.coeff kl.1 : ℤ) : ℂ) * x ^ kl.1 * (((PowerSeries.coeff kl.2 Q : ℤ) : ℂ) * x ^ kl.2)) =
      ((PowerSeries.coeff n ((P : PowerSeries ℤ) * Q) : ℤ) : ℂ) * x ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add, Polynomial.coeff_coe]
    push_cast
    ring
  simp only [hterm, hPQ, PowerSeries.coeff_one]
  rw [tsum_eq_single 0 fun n hn => by simp [hn]]
  simp

/-- The Dirichlet coefficient of the Hasse–Weil series at a prime power. -/
theorem hwCoeff_prime_pow (E₀ : WeierstrassCurve ℤ) (hΔ : E₀.Δ ≠ 0)
    (hmin : IsGlobalMinimalQ (E₀.baseChange ℚ)) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    hwCoeff E₀ (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (hwEulerPoly E₀ p : PowerSeries ℤ) 1) := by
  rw [← LFunction_apply_eq_hwCoeff E₀ hΔ hmin]
  exact LFunction_apply_prime_pow_of_localPolynomial _ (hwEulerPoly E₀)
    (localPolynomial_eq_hwEulerPoly E₀ hΔ hmin) p k

/-- **The Euler product (D2, product form).** For a global minimal equation `E₀` over `ℚ` with
`Δ ≠ 0`, at every `s` where the Hasse–Weil Dirichlet series converges absolutely, Mathlib's
`L(E, s)` is the convergent product `∏_p L_p(p^{-s})^{-1}` over the primes, with the local
factors of Silverman, AEC, App. C, §16 (`hwLocalFactor_good`, `hwLocalFactor_split`,
`hwLocalFactor_nonsplit`, `hwLocalFactor_additive`). -/
theorem hasProd_LSeries_hasseWeil (E₀ : WeierstrassCurve ℤ) (hΔ : E₀.Δ ≠ 0)
    (hmin : IsGlobalMinimalQ (E₀.baseChange ℚ)) (s : ℂ)
    (hs : LSeriesSummable (fun n => (hwCoeff E₀ n : ℂ)) s) :
    HasProd (fun p : Nat.Primes => (hwLocalFactor E₀ p s)⁻¹) ((E₀.baseChange ℚ).LSeries s) := by
  set f : ℕ → ℂ := LSeries.term (fun n => (hwCoeff E₀ n : ℂ)) s with hf
  have h0 : (fun n => (hwCoeff E₀ n : ℂ)) 0 = 0 := by simp [hwCoeff]
  have ht := LSeries.term_def₀ (f := fun n => (hwCoeff E₀ n : ℂ)) h0 s
  have hmulC : ∀ {m n : ℕ}, m.Coprime n → hwCoeff E₀ (m * n) = hwCoeff E₀ m * hwCoeff E₀ n := by
    intro m n hmn
    simp only [← LFunction_apply_eq_hwCoeff E₀ hΔ hmin]
    exact (ZInQ.Literature.isMultiplicative_LFunction _).map_mul_of_coprime hmn
  have hf1 : f 1 = 1 := by
    rw [hf, LSeries.term_of_ne_zero one_ne_zero]
    simp [hwCoeff]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    rw [hf, ht, ht, ht, hmulC hmn, Int.cast_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hnorm : Summable fun n => ‖f n‖ := summable_norm_iff.mpr hs
  have hE := EulerProduct.eulerProduct_hasProd hf1 hmul hnorm rfl
  have hL : (E₀.baseChange ℚ).LSeries s = ∑' n, f n := by
    have hfun : (Int.cast ∘ (E₀.baseChange ℚ).LFunction : ℕ → ℂ) =
        fun n => (hwCoeff E₀ n : ℂ) :=
      funext fun n => congrArg Int.cast (LFunction_apply_eq_hwCoeff E₀ hΔ hmin n)
    rw [WeierstrassCurve.LSeries, hfun]
    rfl
  rw [hL]
  convert hE using 1
  funext p
  have : Fact p.1.Prime := ⟨p.2⟩
  have hterm : ∀ e : ℕ, f (p ^ e) = ((PowerSeries.coeff e
      (PowerSeries.invOfUnit (hwEulerPoly E₀ p : PowerSeries ℤ) 1) : ℤ) : ℂ) *
        ((p : ℂ) ^ (-s)) ^ e := by
    intro e
    rw [hf, ht, hwCoeff_prime_pow E₀ hΔ hmin, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul]
  simp only [hterm]
  rw [hwLocalFactor]
  refine (tsum_invOfUnit_eq_inv _ (hwEulerPoly_coeff_zero E₀ p) _ ?_).symm
  have := hnorm.comp_injective (Nat.pow_right_injective p.2.two_le)
  simpa [Function.comp_def, hterm] using this

end ZInQ.Manuscript.RankModel
