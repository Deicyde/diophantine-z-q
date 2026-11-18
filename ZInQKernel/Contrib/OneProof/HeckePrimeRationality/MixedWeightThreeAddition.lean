import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionWeightThreeForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticAddition

/-!
# Mixed weight-three addition for torsion values

For torsion labels `P, Q` and `S = P + Q` at level `N`, with `x = ℘`, `y = ℘'` (the full Mathlib
derivative) and the completed weight-one values `λ`:

* if `P, Q, S` are all admissible,
  `(x_P - x_S) · (λ_P + λ_Q - λ_S) = (y_P + y_S) / 2` (`mixed_addition_value`);
* otherwise `λ_P + λ_Q - λ_S = 0`, so the left side vanishes (`mixed_value_bad`).

The analytic input is the derivative, in the first variable on an ordinary neighbourhood where all
three theta values are nonzero, of the Frobenius–Stickelberger square identity
`(L(u) + L(v) - L(u+v))² = -L'(u) - L'(v) - L'(u+v) + 3c`, with `L = H'/H`, `L' = c - ℘`,
`L'' = -℘'`.

The weight-three form `mixedForm` with these values equals `½ (y_P + y_S)` as a form on admissible
triples and `0` otherwise, and lies in the span of the weight-three forms whose values are the
convergent congruence-class sums `∑_{p} eisSummand 3 (a + N p₁, b + N p₂)` (`mixedForm_mem`).
-/

noncomputable section
set_option autoImplicit false
open Complex Filter
open scoped Topology Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeAddition

open CompletedTheta TorsionWeierstrassData TorsionWeightThree

/-! ### The analytic mixed identity -/

/-- Derivative of the square identity in the first variable. -/
theorem mixed_addition_analytic (τ : ℍ) {u v : ℂ} (hu : H τ u ≠ 0) (hv : H τ v ≠ 0)
    (huv : H τ (u + v) ≠ 0) :
    2 * (ThetaAddition.L τ u + ThetaAddition.L τ v - ThetaAddition.L τ (u + v)) *
        (deriv (ThetaAddition.L τ) u - deriv (ThetaAddition.L τ) (u + v)) =
      -deriv (deriv (ThetaAddition.L τ)) u - deriv (deriv (ThetaAddition.L τ)) (u + v) := by
  have hA : ∀ {z : ℂ}, H τ z ≠ 0 → AnalyticAt ℂ (ThetaAddition.L τ) z := fun {z} hz =>
    ((differentiable_H τ).analyticAt z).deriv.div ((differentiable_H τ).analyticAt z) hz
  have hev : ∀ᶠ w in 𝓝 u, H τ w ≠ 0 ∧ H τ (w + v) ≠ 0 := by
    have h1 := (differentiable_H τ).continuous.continuousAt.eventually_ne hu
    have h2 : ∀ᶠ w in 𝓝 u, H τ (w + v) ≠ 0 :=
      ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const : Continuous fun w : ℂ => w + v)).continuousAt.eventually_ne huv
    exact h1.and h2
  have heq : (fun w => (ThetaAddition.L τ w + ThetaAddition.L τ v - ThetaAddition.L τ (w + v)) ^ 2)
      =ᶠ[𝓝 u] fun w => -deriv (ThetaAddition.L τ) w - deriv (ThetaAddition.L τ) v -
        deriv (ThetaAddition.L τ) (w + v) + 3 * ThetaAddition.c τ :=
    hev.mono fun w hw => ThetaAddition.frobenius_stickelberger τ w v hw.1 hv hw.2
  have hF : HasDerivAt
      (fun w => (ThetaAddition.L τ w + ThetaAddition.L τ v - ThetaAddition.L τ (w + v)) ^ 2)
      (2 * (ThetaAddition.L τ u + ThetaAddition.L τ v - ThetaAddition.L τ (u + v)) *
        (deriv (ThetaAddition.L τ) u - deriv (ThetaAddition.L τ) (u + v))) u := by
    have h1 := (hA hu).differentiableAt.hasDerivAt
    have h2 := (hA huv).differentiableAt.hasDerivAt.comp_add_const u v
    have h := ((h1.add_const (ThetaAddition.L τ v)).sub h2).pow 2
    convert h using 1
    simp only [Pi.sub_apply]
    norm_num
  have hG : HasDerivAt
      (fun w => -deriv (ThetaAddition.L τ) w - deriv (ThetaAddition.L τ) v -
        deriv (ThetaAddition.L τ) (w + v) + 3 * ThetaAddition.c τ)
      (-deriv (deriv (ThetaAddition.L τ)) u - deriv (deriv (ThetaAddition.L τ)) (u + v)) u := by
    have h1 := (hA hu).deriv.differentiableAt.hasDerivAt
    have h2 := (hA huv).deriv.differentiableAt.hasDerivAt.comp_add_const u v
    have h := ((h1.neg.sub_const (deriv (ThetaAddition.L τ) v)).sub h2).add_const
      (3 * ThetaAddition.c τ)
    convert h using 1
  exact hF.unique (hG.congr_of_eventuallyEq heq)

theorem wp_eq_L (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    (ThetaWeierstrass.periodPair τ).weierstrassP z =
      -deriv (ThetaAddition.L τ) z + ThetaAddition.c τ := by
  rw [TorsionQuadraticAddition.addition_constant_eq_finitePart]
  exact ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ z
    (fun h => hz ((ThetaWeierstrass.H_zero_iff_mem_lattice τ z).mpr h))

theorem wp'_eq_L (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    (ThetaWeierstrass.periodPair τ).derivWeierstrassP z =
      -deriv (deriv (ThetaAddition.L τ)) z := by
  have hlog : logDeriv (H τ) = ThetaAddition.L τ := by
    funext w; rfl
  rw [wp_deriv_eq_neg_log_second τ hz, hlog, iteratedDeriv_succ, iteratedDeriv_one]

/-! ### Torsion values -/

variable {N : ℕ} [NeZero N]

/-- **Mixed addition on admissible triples**, with the full derivative `y = ℘'`. -/
theorem mixed_addition_value (a b c d : ℤ) (τ : ℍ)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    (xValue N a b τ - xValue N (a + c) (b + d) τ) *
        (lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ) =
      (yValue N a b τ + yValue N (a + c) (b + d) τ) / 2 := by
  have hP := H_torsion_ne_zero N (NeZero.pos N) τ a b hp
  have hQ := H_torsion_ne_zero N (NeZero.pos N) τ c d hq
  have hS := H_torsion_ne_zero N (NeZero.pos N) τ (a + c) (b + d) hs
  have hPQ : H τ (torsionPoint N a b τ + torsionPoint N c d τ) ≠ 0 := by
    rw [← TorsionQuadraticAddition.torsionPoint_add]; exact hS
  have hmix := mixed_addition_analytic τ hP hQ hPQ
  rw [TorsionQuadraticAddition.lambdaValue_add_difference a b c d τ hp hq hs,
    xValue_of_good N a b τ hp, xValue_of_good N (a + c) (b + d) τ hs,
    yValue_of_good N a b τ hp, yValue_of_good N (a + c) (b + d) τ hs,
    TorsionQuadraticAddition.torsionPoint_add, wp_eq_L τ hP, wp_eq_L τ hPQ,
    wp'_eq_L τ hP, wp'_eq_L τ hPQ]
  linear_combination hmix / 2

/-- On every non-admissible triple the completed weight-one combination vanishes. -/
theorem lambda_defect_bad (a b c d : ℤ) (τ : ℍ)
    (h : ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) ∨ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) ∨
      ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ = 0 := by
  unfold lambdaValue
  rcases h with ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ | ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ | ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  · have h1 : TorsionDistributionTwo.reg N a b τ = 0 :=
      TorsionDistributionTwo.reg_of_bad ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ τ
    have h2 : TorsionDistributionTwo.reg N (a + c) (b + d) τ = TorsionDistributionTwo.reg N c d τ := by
      rw [show a + c = c + (N : ℤ) * m by rw [hm]; ring, show b + d = d + (N : ℤ) * n by rw [hn]; ring,
        TorsionFourierComparison.reg_shift]
    rw [h1, h2]; ring
  · have h1 : TorsionDistributionTwo.reg N c d τ = 0 :=
      TorsionDistributionTwo.reg_of_bad ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ τ
    have h2 : TorsionDistributionTwo.reg N (a + c) (b + d) τ = TorsionDistributionTwo.reg N a b τ := by
      rw [show a + c = a + (N : ℤ) * m by rw [hm], show b + d = b + (N : ℤ) * n by rw [hn],
        TorsionFourierComparison.reg_shift]
    rw [h1, h2]; ring
  · have h1 : TorsionDistributionTwo.reg N (a + c) (b + d) τ = 0 :=
      TorsionDistributionTwo.reg_of_bad ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ τ
    have h2 : TorsionDistributionTwo.reg N c d τ = -TorsionDistributionTwo.reg N a b τ := by
      rw [show c = -a + (N : ℤ) * m by linarith, show d = -b + (N : ℤ) * n by linarith,
        TorsionFourierComparison.reg_shift, TorsionFourierComparison.reg_neg]
    rw [h1, h2]; ring

theorem mixed_value_bad (a b c d : ℤ) (τ : ℍ)
    (h : ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) ∨ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) ∨
      ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    (xValue N a b τ - xValue N (a + c) (b + d) τ) *
        (lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ) = 0 := by
  rw [lambda_defect_bad a b c d τ h, mul_zero]

/-! ### The weight-three forms -/

/-- The actual mixed weight-three form `(x_P - x_S)(λ_P + λ_Q - λ_S)`. -/
def mixedForm (N : ℕ) (hN : 0 < N) (a b c d : ℤ) : Weight N 3 :=
  ModularForm.mcast (by norm_num)
    ((WeierstrassForms.xForm N hN a b - WeierstrassForms.xForm N hN (a + c) (b + d)).mul
      (WeierstrassForms.lambdaForm N hN a b + WeierstrassForms.lambdaForm N hN c d -
        WeierstrassForms.lambdaForm N hN (a + c) (b + d)))

theorem mixedForm_apply (N : ℕ) (hN : 0 < N) (a b c d : ℤ) (τ : ℍ) :
    mixedForm N hN a b c d τ =
      (xValue N a b τ - xValue N (a + c) (b + d) τ) *
        (lambdaValue N a b τ + lambdaValue N c d τ - lambdaValue N (a + c) (b + d) τ) := by
  change (WeierstrassForms.xForm N hN a b τ - WeierstrassForms.xForm N hN (a + c) (b + d) τ) *
      (WeierstrassForms.lambdaForm N hN a b τ + WeierstrassForms.lambdaForm N hN c d τ -
        WeierstrassForms.lambdaForm N hN (a + c) (b + d) τ) = _
  rw [WeierstrassForms.xForm_apply, WeierstrassForms.xForm_apply, WeierstrassForms.lambdaForm_apply,
    WeierstrassForms.lambdaForm_apply, WeierstrassForms.lambdaForm_apply]

/-- On admissible triples the mixed form is `½ (y_P + y_S)` as a modular form. -/
theorem mixedForm_eq_good (N : ℕ) (hN : 0 < N) (a b c d : ℤ)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    mixedForm N hN a b c d = (1 / 2 : ℂ) • (yForm N hN a b + yForm N hN (a + c) (b + d)) := by
  have : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change _ = (1 / 2 : ℂ) * (yForm N hN a b τ + yForm N hN (a + c) (b + d) τ)
  rw [mixedForm_apply, mixed_addition_value a b c d τ hp hq hs, yForm_apply, yForm_apply]
  ring

/-- On every other triple the mixed form is zero. -/
theorem mixedForm_eq_bad (N : ℕ) (hN : 0 < N) (a b c d : ℤ)
    (h : ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) ∨ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) ∨
      ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    mixedForm N hN a b c d = 0 := by
  have : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  rw [mixedForm_apply, mixed_value_bad a b c d τ h]
  rfl

/-- The weight-three form whose value is the convergent congruence-class lattice sum. -/
def classSeriesForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 3 :=
  (-(1 / (2 * (N : ℂ) ^ 3))) • yForm N hN a b

theorem classSeriesForm_hasSum (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    HasSum (fun p : ℤ × ℤ => EisensteinSeries.eisSummand 3 ![a + N * p.1, b + N * p.2] τ)
      (classSeriesForm N hN a b τ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := hasSum_weightThree_congruence N hN a b τ
  change HasSum _ (-(1 / (2 * (N : ℂ) ^ 3)) * yForm N hN a b τ)
  rw [yForm_apply]
  convert h using 1
  field_simp

theorem classSeriesForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    classSeriesForm N hN a b τ =
      ∑' p : ℤ × ℤ, EisensteinSeries.eisSummand 3 ![a + N * p.1, b + N * p.2] τ :=
  (classSeriesForm_hasSum N hN a b τ).tsum_eq.symm

/-- The span of the convergent weight-three congruence-class series forms. -/
def classSeriesSpan (N : ℕ) (hN : 0 < N) : Submodule ℂ (Weight N 3) :=
  Submodule.span ℂ (Set.range fun q : ℤ × ℤ => classSeriesForm N hN q.1 q.2)

theorem yForm_eq_classSeries (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    yForm N hN a b = (-(2 * (N : ℂ) ^ 3)) • classSeriesForm N hN a b := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold classSeriesForm
  rw [smul_smul]
  have : -(2 * (N : ℂ) ^ 3) * -(1 / (2 * (N : ℂ) ^ 3)) = 1 := by field_simp
  rw [this, one_smul]

theorem yForm_mem_classSeriesSpan (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    yForm N hN a b ∈ classSeriesSpan N hN := by
  rw [yForm_eq_classSeries]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

/-- **Membership**: every mixed weight-three form lies in the class-series span. -/
theorem mixedForm_mem (N : ℕ) (hN : 0 < N) (a b c d : ℤ) :
    mixedForm N hN a b c d ∈ classSeriesSpan N hN := by
  by_cases h : ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) ∨ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) ∨
      ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)
  · rw [mixedForm_eq_bad N hN a b c d h]
    exact Submodule.zero_mem _
  · push Not at h
    rw [mixedForm_eq_good N hN a b c d (fun h' => h.1 h'.1 h'.2) (fun h' => h.2.1 h'.1 h'.2)
      (fun h' => h.2.2 h'.1 h'.2)]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (yForm_mem_classSeriesSpan N hN a b)
      (yForm_mem_classSeriesSpan N hN (a + c) (b + d)))

end ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeAddition
