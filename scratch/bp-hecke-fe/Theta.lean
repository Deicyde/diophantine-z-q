import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

/-!
# Weight-two theta kernels over shifted copies of `ℤ[i]`

For `a, b ∈ ℝ/ℤ` the function
`gaussTheta a b x = Σ_{(m,n) ∈ ℤ²} ((m+a) + i(n+b)) exp(−π((m+a)² + (n+b)²) x)`
is the product decomposition `oddKernel a · evenKernel b + i · evenKernel a · oddKernel b`
of Mathlib's Hurwitz kernels. It satisfies the weight-two transformation law
`gaussTheta a b (1/x) = x² · gaussThetaDual a b x` and decays exponentially at `∞`, so it
forms a strong FE-pair (`Mathlib.NumberTheory.LSeries.AbstractFuncEq`) with `k = 2`, `ε = 1`.
Its Mellin transform is entire and satisfies `Λ(2 − s) = Λ^dual(s)`.
-/

open Complex Real Set Filter Asymptotics HurwitzZeta

namespace BpHeckeFE

/-- The weight-two theta kernel of the shifted lattice `(a, b) + ℤ²`, with the linear
form `x + iy`. -/
noncomputable def gaussTheta (a b : UnitAddCircle) (x : ℝ) : ℂ :=
  (oddKernel a x : ℂ) * evenKernel b x + I * ((evenKernel a x : ℂ) * oddKernel b x)

/-- The dual kernel: `Σ_{(m,n)} −i (m + i n) e(am + bn) exp(−π(m² + n²) x)`. -/
noncomputable def gaussThetaDual (a b : UnitAddCircle) (x : ℝ) : ℂ :=
  (sinKernel a x : ℂ) * cosKernel b x + I * ((cosKernel a x : ℂ) * sinKernel b x)

theorem oddKernel_one_div (a : UnitAddCircle) {x : ℝ} (hx : 0 < x) :
    oddKernel a (1 / x) = x ^ (3 / 2 : ℝ) * sinKernel a x := by
  rw [oddKernel_functional_equation, one_div_one_div]
  simp [one_div, Real.inv_rpow hx.le]

theorem evenKernel_one_div (a : UnitAddCircle) {x : ℝ} (hx : 0 < x) :
    evenKernel a (1 / x) = x ^ (1 / 2 : ℝ) * cosKernel a x := by
  rw [evenKernel_functional_equation, one_div_one_div]
  simp [one_div, Real.inv_rpow hx.le]

/-- **Weight-two transformation law.** -/
theorem gaussTheta_one_div (a b : UnitAddCircle) {x : ℝ} (hx : 0 < x) :
    gaussTheta a b (1 / x) = ((x ^ (2 : ℝ) : ℝ) : ℂ) * gaussThetaDual a b x := by
  have h2 : x ^ (2 : ℝ) = x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← rpow_add hx]; norm_num
  simp only [gaussTheta, gaussThetaDual, oddKernel_one_div _ hx, evenKernel_one_div _ hx, h2]
  push_cast
  ring

theorem isBigO_atTop_of_sub_const {f : ℝ → ℝ} {c p : ℝ} (hp : 0 < p)
    (h : (fun x => f x - c) =O[atTop] (fun x => Real.exp (-p * x))) :
    f =O[atTop] (fun _ => (1 : ℝ)) := by
  have he : (fun x => Real.exp (-p * x)) =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [norm_of_nonneg (exp_pos _).le, norm_one, one_mul, exp_le_one_iff]
    nlinarith
  have := (h.trans he).add (Asymptotics.isBigO_const_const c one_ne_zero atTop)
  simpa using this

theorem evenKernel_isBigO_one (a : UnitAddCircle) :
    evenKernel a =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨p, hp, h⟩ := isBigO_atTop_evenKernel_sub a
  exact isBigO_atTop_of_sub_const hp h

theorem cosKernel_isBigO_one (a : UnitAddCircle) :
    cosKernel a =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨p, hp, h⟩ := isBigO_atTop_cosKernel_sub a
  exact isBigO_atTop_of_sub_const hp h

/-- A product `u * v` with `u` exponentially decaying and `v` bounded is `O(x ^ r)` for every
`r`. -/
theorem prod_isBigO_rpow {u v : ℝ → ℝ}
    (hu : ∃ p, 0 < p ∧ u =O[atTop] (fun x => Real.exp (-p * x)))
    (hv : v =O[atTop] (fun _ => (1 : ℝ))) (r : ℝ) :
    (fun x => ((u x : ℂ) * v x)) =O[atTop] (· ^ r) := by
  obtain ⟨p, hp, hu⟩ := hu
  have h1 : (fun x => u x * v x) =O[atTop] (fun x => Real.exp (-p * x) * 1) := hu.mul hv
  simp only [mul_one] at h1
  have h2 := h1.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  have : (fun x => ((u x : ℂ) * v x)) = (fun x => ((u x * v x : ℝ) : ℂ)) := by
    funext x; push_cast; rfl
  rw [this]
  exact Complex.isBigO_ofReal_left.mpr h2

theorem gaussTheta_isBigO (a b : UnitAddCircle) (r : ℝ) :
    gaussTheta a b =O[atTop] (· ^ r) := by
  have h1 := prod_isBigO_rpow (isBigO_atTop_oddKernel a) (evenKernel_isBigO_one b) r
  have h2 := prod_isBigO_rpow (isBigO_atTop_oddKernel b) (evenKernel_isBigO_one a) r
  have h3 := h1.add (h2.const_mul_left I)
  refine h3.congr_left fun x => ?_
  simp only [gaussTheta]; ring

theorem gaussThetaDual_isBigO (a b : UnitAddCircle) (r : ℝ) :
    gaussThetaDual a b =O[atTop] (· ^ r) := by
  have h1 := prod_isBigO_rpow (isBigO_atTop_sinKernel a) (cosKernel_isBigO_one b) r
  have h2 := prod_isBigO_rpow (isBigO_atTop_sinKernel b) (cosKernel_isBigO_one a) r
  have h3 := h1.add (h2.const_mul_left I)
  refine h3.congr_left fun x => ?_
  simp only [gaussThetaDual]; ring

theorem continuousOn_gaussTheta (a b : UnitAddCircle) : ContinuousOn (gaussTheta a b) (Ioi 0) := by
  have ho := fun c : UnitAddCircle => continuous_ofReal.comp_continuousOn (continuousOn_oddKernel c)
  have he := fun c : UnitAddCircle =>
    continuous_ofReal.comp_continuousOn (continuousOn_evenKernel c)
  exact ((ho a).mul (he b)).add (continuousOn_const.mul ((he a).mul (ho b)))

theorem continuousOn_gaussThetaDual (a b : UnitAddCircle) :
    ContinuousOn (gaussThetaDual a b) (Ioi 0) := by
  have ho := fun c : UnitAddCircle => continuous_ofReal.comp_continuousOn (continuousOn_sinKernel c)
  have he := fun c : UnitAddCircle =>
    continuous_ofReal.comp_continuousOn (continuousOn_cosKernel c)
  exact ((ho a).mul (he b)).add (continuousOn_const.mul ((he a).mul (ho b)))

/-- The strong FE-pair `(gaussTheta a b, gaussThetaDual a b)` of weight `2`. -/
noncomputable def gaussFEPair (a b : UnitAddCircle) : WeakFEPair ℂ where
  f := gaussTheta a b
  g := gaussThetaDual a b
  k := 2
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_gaussTheta a b).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_gaussThetaDual a b).locallyIntegrableOn measurableSet_Ioi
  hk := two_pos
  hε := one_ne_zero
  h_feq x hx := by
    rw [gaussTheta_one_div a b hx, one_mul, smul_eq_mul]
  hf_top r := by simpa using gaussTheta_isBigO a b r
  hg_top r := by simpa using gaussThetaDual_isBigO a b r

theorem isStrong_gaussFEPair (a b : UnitAddCircle) : IsStrongFEPair (gaussFEPair a b) :=
  ⟨rfl, rfl⟩

/-- The completed L-function of the shifted lattice: the Mellin transform of `gaussTheta`. -/
noncomputable def gaussLambda (a b : UnitAddCircle) (s : ℂ) : ℂ := mellin (gaussTheta a b) s

/-- The dual completed L-function. -/
noncomputable def gaussLambdaDual (a b : UnitAddCircle) (s : ℂ) : ℂ :=
  mellin (gaussThetaDual a b) s

/-- **Entireness**: `gaussLambda a b` is entire. -/
theorem differentiable_gaussLambda (a b : UnitAddCircle) : Differentiable ℂ (gaussLambda a b) := by
  have h := (isStrong_gaussFEPair a b).differentiable_Λ
  rwa [(isStrong_gaussFEPair a b).Λ_eq] at h

theorem differentiable_gaussLambdaDual (a b : UnitAddCircle) :
    Differentiable ℂ (gaussLambdaDual a b) := by
  have h := (isStrong_gaussFEPair a b).symm.differentiable_Λ
  rwa [(isStrong_gaussFEPair a b).symm.Λ_eq] at h

/-- The Mellin integral converges for every `s`. -/
theorem mellinConvergent_gaussTheta (a b : UnitAddCircle) (s : ℂ) :
    MellinConvergent (gaussTheta a b) s :=
  ((isStrong_gaussFEPair a b).hasMellin s).1

/-- **Functional equation** `Λ(2 − s) = Λ^dual(s)`. -/
theorem gaussLambda_two_sub (a b : UnitAddCircle) (s : ℂ) :
    gaussLambda a b (2 - s) = gaussLambdaDual a b s := by
  have h := (gaussFEPair a b).functional_equation s
  rw [(isStrong_gaussFEPair a b).Λ_eq, (isStrong_gaussFEPair a b).symm.Λ_eq] at h
  simpa [gaussFEPair, gaussLambda, gaussLambdaDual, WeakFEPair.symm] using h

end BpHeckeFE
