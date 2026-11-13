import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Hypotheses.CR3Literature

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


/-! ### The Mellin transform as a lattice Dirichlet series -/

/-- The lattice point `(m + a) + i (n + b)`. -/
noncomputable def gz (a b : ℝ) (p : ℤ × ℤ) : ℂ := ((p.1 : ℂ) + a) + ((p.2 : ℂ) + b) * I

/-- Its norm `(m + a)² + (n + b)²`. -/
noncomputable def gq (a b : ℝ) (p : ℤ × ℤ) : ℝ := ((p.1 : ℝ) + a) ^ 2 + ((p.2 : ℝ) + b) ^ 2

theorem gq_eq_norm_sq (a b : ℝ) (p : ℤ × ℤ) : gq a b p = ‖gz a b p‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [gz, gq]; ring

theorem hasSum_gaussTheta (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun p : ℤ × ℤ => gz a b p * rexp (-π * gq a b p * t)) (gaussTheta a b t) := by
  set fo : ℝ → ℤ → ℝ := fun c n => ((n : ℝ) + c) * rexp (-π * ((n : ℝ) + c) ^ 2 * t)
  set fe : ℝ → ℤ → ℝ := fun c n => rexp (-π * ((n : ℝ) + c) ^ 2 * t)
  have ho : ∀ c : ℝ, HasSum (fo c) (oddKernel c t) := fun c => hasSum_int_oddKernel c ht
  have he : ∀ c : ℝ, HasSum (fe c) (evenKernel c t) := fun c => hasSum_int_evenKernel c ht
  have hon : ∀ c : ℝ, Summable fun n => ‖fo c n‖ := fun c =>
    (summable_abs_iff.mpr (ho c).summable).congr fun n => (Real.norm_eq_abs _).symm
  have hen : ∀ c : ℝ, Summable fun n => ‖fe c n‖ := fun c =>
    (summable_abs_iff.mpr (he c).summable).congr fun n => (Real.norm_eq_abs _).symm
  have P1 : HasSum (fun p : ℤ × ℤ => fo a p.1 * fe b p.2) (oddKernel a t * evenKernel b t) :=
    (ho a).mul (he b) (summable_mul_of_summable_norm (hon a) (hen b))
  have P2 : HasSum (fun p : ℤ × ℤ => fe a p.1 * fo b p.2) (evenKernel a t * oddKernel b t) :=
    (he a).mul (ho b) (summable_mul_of_summable_norm (hen a) (hon b))
  have P : HasSum (fun p : ℤ × ℤ => ((fo a p.1 * fe b p.2 : ℝ) : ℂ) +
      I * ((fe a p.1 * fo b p.2 : ℝ) : ℂ))
      (((oddKernel a t * evenKernel b t : ℝ) : ℂ) + I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ)) :=
    (Complex.hasSum_ofReal.mpr P1).add ((Complex.hasSum_ofReal.mpr P2).mul_left I)
  have hval : gaussTheta a b t =
      ((oddKernel a t * evenKernel b t : ℝ) : ℂ) + I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ) := by
    simp only [gaussTheta]; push_cast; ring
  rw [hval]
  convert P using 1
  funext p
  have h1 : rexp (-π * gq a b p * t) =
      rexp (-π * ((p.1 : ℝ) + a) ^ 2 * t) * rexp (-π * ((p.2 : ℝ) + b) ^ 2 * t) := by
    rw [← Real.exp_add]; simp only [gq]; ring_nf
  simp only [gz, fo, fe, h1]
  push_cast
  ring

/-- The standard `ℤ`-lattice `ℤ + ℤ i` in `ℂ`, as a Mathlib `PeriodPair`. -/
noncomputable def gaussPeriodPair : PeriodPair where
  ω₁ := 1
  ω₂ := I
  indep := by
    have := Complex.basisOneI.linearIndependent
    rwa [Complex.coe_basisOneI] at this

theorem summable_norm_gz_rpow (a b : ℝ) {r : ℝ} (hr : r < -2) :
    Summable fun p : ℤ × ℤ => ‖gz a b p‖ ^ r := by
  set L := gaussPeriodPair
  have h := ZLattice.summable_norm_sub_rpow L.lattice r (by simpa using hr) (-(a + b * I))
  have h2 := (L.latticeEquivProd.symm.toEquiv.summable_iff).mpr h
  refine h2.congr fun p => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
  congr 2
  simp [gz, L, gaussPeriodPair]; ring

/-- **Mellin transform = lattice Dirichlet series**, for `Re s > 3/2`. -/
theorem hasSum_gaussLambda (a b : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    HasSum (fun p : ℤ × ℤ => π ^ (-s) * Gamma s * gz a b p / (gq a b p : ℂ) ^ s)
      (gaussLambda a b s) := by
  refine hasSum_mellin_pi_mul (fun p => ?_) (by linarith) (fun t ht => hasSum_gaussTheta a b ht)
    ?_
  · by_cases h : gz a b p = 0
    · exact Or.inl h
    · right; rw [gq_eq_norm_sq]; positivity
  · refine (summable_norm_gz_rpow a b (r := 1 - 2 * s.re) (by linarith)).congr fun p => ?_
    rw [gq_eq_norm_sq]
    rcases eq_or_ne ‖gz a b p‖ 0 with h | h
    · rw [h, Real.zero_rpow (by linarith), zero_div]
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), div_eq_mul_inv,
        ← Real.rpow_neg (norm_nonneg _), ← Real.rpow_one_add' (norm_nonneg _)]
      · push_cast; ring_nf
      · push_cast; linarith

/-- The lattice Dirichlet series `Σ_{(m,n)} ((m+a) + i(n+b)) / ((m+a)² + (n+b)²)^s`. -/
noncomputable def gaussL (a b : ℝ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, gz a b p / (gq a b p : ℂ) ^ s

/-- **Entire continuation of the lattice Dirichlet series** (Hecke). -/
theorem gaussL_continuation (a b : ℝ) : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    ∀ s : ℂ, 3 / 2 < s.re → F s = gaussL a b s := by
  refine ⟨fun s => (π : ℂ) ^ s * (Gamma s)⁻¹ * gaussLambda a b s, ?_, fun s hs => ?_⟩
  · have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
    have : NeZero (π : ℂ) := ⟨hpi⟩
    exact ((differentiable_const_cpow_of_neZero (π : ℂ)).mul differentiable_one_div_Gamma).mul
      (differentiable_gaussLambda a b)
  · have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hpi : (π : ℂ) ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
      (by rintro rfl; norm_num at hs)).mpr (ofReal_ne_zero.mpr pi_ne_zero)
    show (π : ℂ) ^ s * (Gamma s)⁻¹ * gaussLambda a b s = gaussL a b s
    rw [← (hasSum_gaussLambda a b hs).tsum_eq, gaussL]
    simp_rw [mul_div_assoc]
    rw [tsum_mul_left, cpow_neg]
    field_simp


/-! ### Periodic twists: `Σ_{α ∈ ℤ[i]} c(α mod M) α N(α)^{−s}` -/

/-- The lattice series of `ℤ[i]` twisted by a function `c` of `α mod M`. -/
noncomputable def twistedL (M : ℕ) (c : ZMod M × ZMod M → ℂ) (s : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p / (gq 0 0 p : ℂ) ^ s

/-- `ℤ² ≃ (Fin M)² × ℤ²`, `(q, j) ↦ qM + j`. -/
def blockEquiv (M : ℕ) [NeZero M] : (Fin M × Fin M) × (ℤ × ℤ) ≃ ℤ × ℤ :=
  (Equiv.mk (fun x : (Fin M × Fin M) × (ℤ × ℤ) => ((x.2.1, x.1.1), (x.2.2, x.1.2)))
    (fun y => ((y.1.2, y.2.2), (y.1.1, y.2.1))) (fun _ => rfl) (fun _ => rfl)).trans
    (Equiv.prodCongr (Int.divModEquiv M).symm (Int.divModEquiv M).symm)

theorem blockEquiv_apply (M : ℕ) [NeZero M] (j : Fin M × Fin M) (q : ℤ × ℤ) :
    blockEquiv M (j, q) = (q.1 * M + j.1, q.2 * M + j.2) := rfl

theorem gz_block (M : ℕ) [NeZero M] (j : Fin M × Fin M) (q : ℤ × ℤ) :
    gz 0 0 (blockEquiv M (j, q)) = (M : ℂ) * gz ((j.1 : ℝ) / M) ((j.2 : ℝ) / M) q := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  simp only [blockEquiv_apply, gz]
  push_cast
  field_simp
  ring

theorem gq_block (M : ℕ) [NeZero M] (j : Fin M × Fin M) (q : ℤ × ℤ) :
    gq 0 0 (blockEquiv M (j, q)) = (M : ℝ) ^ 2 * gq ((j.1 : ℝ) / M) ((j.2 : ℝ) / M) q := by
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  simp only [blockEquiv_apply, gq]
  push_cast
  field_simp
  ring

theorem gq_nonneg (a b : ℝ) (p : ℤ × ℤ) : 0 ≤ gq a b p := by
  unfold gq; positivity

theorem summable_gz_div (a b : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable fun p : ℤ × ℤ => ‖gz a b p / (gq a b p : ℂ) ^ s‖ := by
  have h := (hasSum_gaussLambda a b hs).summable.mul_left (π ^ (-s) * Gamma s)⁻¹
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (π : ℂ) ^ (-s) ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
      (by rintro h; rw [neg_eq_zero] at h; subst h; norm_num at hs)).mpr
      (ofReal_ne_zero.mpr pi_ne_zero)
  refine summable_norm_iff.mpr (h.congr fun p => ?_)
  field_simp

theorem summable_twisted (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    Summable fun p : ℤ × ℤ => c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p / (gq 0 0 p : ℂ) ^ s := by
  set C := ∑ x, ‖c x‖
  refine Summable.of_norm_bounded ((summable_gz_div 0 0 hs).mul_left C) fun p => ?_
  rw [mul_div_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun x => ‖c x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _))
    (norm_nonneg _)

/-- **Block decomposition** of the twisted series into shifted lattice series. -/
theorem twistedL_eq (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ} (hs : 3 / 2 < s.re) :
    twistedL M c s = ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
      ((M : ℂ) / (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ s) * gaussL ((j.1 : ℝ) / M) ((j.2 : ℝ) / M) s := by
  have hsum := summable_twisted M c hs
  have h2 := (blockEquiv M).summable_iff.mpr hsum
  rw [twistedL, ← (blockEquiv M).tsum_eq]
  refine (h2.tsum_prod).trans ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussL, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  simp only [Function.comp_apply]
  rw [gz_block, gq_block, ofReal_mul,
    mul_cpow_ofReal_nonneg (by positivity) (gq_nonneg _ _ _)]
  have hc : c ((((blockEquiv M (j, q)).1 : ℤ) : ZMod M), (((blockEquiv M (j, q)).2 : ℤ) : ZMod M)) =
      c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) := by
    simp [blockEquiv_apply]
  rw [hc]
  ring

/-- **Hecke's continuation for periodic twists**: for every `c : (ℤ/M)² → ℂ`, the series
`Σ_{α ∈ ℤ[i]} c(α mod M) α N(α)^{−s}` (absolutely convergent for `Re s > 3/2`) has an entire
continuation. -/
theorem twistedL_continuation (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = twistedL M c s := by
  choose G hG hGeq using fun j : Fin M × Fin M => gaussL_continuation ((j.1 : ℝ) / M) ((j.2 : ℝ) / M)
  have hM : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM⟩
  refine ⟨fun s => ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
      ((M : ℂ) / (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ s) * G j s, ?_, fun s hs => ?_⟩
  · refine Differentiable.fun_sum fun j _ => ?_
    refine (Differentiable.const_mul ?_ _).mul (hG j)
    simp_rw [div_eq_mul_inv, ← cpow_neg]
    exact (differentiable_const_cpow_of_neZero _).comp differentiable_id.neg |>.const_mul _
  · rw [twistedL_eq M c hs]
    exact Finset.sum_congr rfl fun j _ => by rw [hGeq j s hs]


/-! ### From lattice sums to Dirichlet series: grouping by the norm -/

/-- The points of `ℤ²` of norm `n`, i.e. the `α ∈ ℤ[i]` with `N(α) = n`. -/
def normFiber (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = n)

theorem mem_normFiber {n : ℕ} {p : ℤ × ℤ} : p ∈ normFiber n ↔ p.1 ^ 2 + p.2 ^ 2 = n := by
  simp only [normFiber, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_abs p.1,
      sq_abs p.2, abs_nonneg p.1, abs_nonneg p.2, neg_abs_le p.1, le_abs_self p.1,
      neg_abs_le p.2, le_abs_self p.2]

/-- **Grouping by the norm.** If `a n = Σ_{N(α) = n} c(α mod M) α` for `n ≠ 0`, then the Dirichlet
series of `a` is the twisted lattice series, for `Re s > 3/2`. -/
theorem LSeries_eq_twistedL (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) (a : ℕ → ℂ)
    (ha : ∀ n : ℕ, n ≠ 0 →
      a n = ∑ p ∈ normFiber n, c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p)
    {s : ℂ} (hs : 3 / 2 < s.re) : LSeries a s = twistedL M c s := by
  set T := fun p : ℤ × ℤ => c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p / (gq 0 0 p : ℂ) ^ s
  have hT : HasSum T (twistedL M c s) := (summable_twisted M c hs).hasSum
  set g : ℤ × ℤ → ℕ := fun p => (p.1 ^ 2 + p.2 ^ 2).toNat
  have hfib := hT.tsum_fiberwise g
  rw [LSeries]
  refine HasSum.tsum_eq (hfib.congr_fun fun n => ?_)
  symm
  have hset : g ⁻¹' {n} = ↑(normFiber n) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_normFiber, g]
    have : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
    omega
  rw [hset, Finset.tsum_subtype' (normFiber n) T, LSeries.term_def]
  have hq : ∀ p ∈ normFiber n, (gq 0 0 p : ℂ) = (n : ℂ) := by
    intro p hp
    have h := mem_normFiber.mp hp
    have : gq 0 0 p = (n : ℝ) := by
      simp only [gq, add_zero]; exact_mod_cast h
    rw [this]; push_cast; rfl
  split_ifs with hn
  · subst hn
    refine Finset.sum_eq_zero fun p hp => ?_
    have h := mem_normFiber.mp hp
    push_cast at h
    have h1 : p.1 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    have h2 : p.2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    simp [T, gz, h1, h2]
  · rw [ha n hn, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [T, hq p hp]

/-! ### The Hecke character of `C_d` and the reduction of `HeckeContinuation` -/

/-- The unit `u ∈ {±1, ±i}` with `u α ≡ 1 (mod 2 + 2i)` ("primary"), as a function of
`α = a + bi mod 4`; `0` if `(1 + i) ∣ α`. So `ψ₁(α) = unitOf(α) · α` is the Hecke character of
`ℚ(i)` of conductor `(1 + i)³` attached to `y² = x³ − x`. -/
def unitOf (t : ZMod 4 × ZMod 4) : ℂ :=
  if t = (1, 0) ∨ t = (3, 2) then 1
  else if t = (3, 0) ∨ t = (1, 2) then -1
  else if t = (0, 3) ∨ t = (2, 1) then I
  else if t = (0, 1) ∨ t = (2, 3) then -I
  else 0

/-- The finite part of the Hecke character `ψ_d = ψ₁ · (χ_d ∘ N)` of `C_d`, on `ℤ[i] / 4d`:
`c_d(α) = (N(α) / d) · unitOf(α mod 4)` with the Jacobi symbol. -/
noncomputable def cdChar (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : ℂ :=
  (jacobiSym ((x.1.val : ℤ) ^ 2 + (x.2.val : ℤ) ^ 2) d : ℂ) *
    unitOf (((x.1.val : ℤ) : ZMod 4), ((x.2.val : ℤ) : ZMod 4))

theorem cdChar_intCast {d : ℕ} [NeZero d] (p : ℤ × ℤ) :
    cdChar d ((p.1 : ZMod (4 * d)), (p.2 : ZMod (4 * d))) =
      (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) := by
  have h4d : ∀ x : ℤ, ((x : ZMod (4 * d)).val : ℤ) ≡ x [ZMOD (4 * d : ℕ)] := fun x => by
    rw [ZMod.val_intCast]; exact Int.emod_emod_of_dvd x (dvd_refl _)
  have hd : ∀ x : ℤ, ((x : ZMod (4 * d)).val : ℤ) ≡ x [ZMOD d] := fun x => by
    have := h4d x; push_cast at this; exact this.of_mul_left 4
  have h4 : ∀ x : ℤ, ((x : ZMod (4 * d)).val : ℤ) ≡ x [ZMOD 4] := fun x => by
    have := h4d x; push_cast at this; exact this.of_mul_right d
  unfold cdChar
  dsimp only
  rw [jacobiSym.mod_left' (((hd p.1).pow 2).add ((hd p.2).pow 2)),
    (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (h4 p.1),
    (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (h4 p.2)]

/-- `(1/4) Σ_{N(α) = n} ψ_d(α)`: the `n`-th coefficient of the Hecke L-function `L(ψ_d, s)`
(the four units of `ℤ[i]` give each ideal four generators). -/
noncomputable def heckeCoeff (d n : ℕ) : ℂ :=
  (1 / 4) * ∑ p ∈ normFiber n,
    (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p

/-- **Deuring's identity for `C_d`** (Gauss for `a_p`; the CM theory of `y² = x³ − d²x`):
`L(C_d, s) = L(ψ_d, s)` coefficientwise. Stated over the coefficients `cdCoeff d` that
`LFunctionCd.lean` proves to be those of Mathlib's `L(C_d, s)` (odd squarefree `d`).
Numerically VERIFIED for `d ∈ {1, 5, 13, 21, 29, 37, 53, 85}`, `n ≤ 400` (`deuring_check.py`). -/
def DeuringCd (d : ℕ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ((ZInQ.Literature.cdCoeff d n : ℤ) : ℂ) = heckeCoeff d n

/-- **`HeckeContinuation` for `C_d` from Deuring's identity**: for odd squarefree `d`, if
`DeuringCd d` then Mathlib's `L(C_d, s)` has an entire continuation. -/
theorem isLContinuation_of_deuring {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (hD : DeuringCd d) :
    ∃ F : ℂ → ℂ, ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F := by
  have : NeZero d := ⟨by rintro rfl; simp at hd⟩
  have : NeZero (4 * d) := ⟨by have := NeZero.ne d; omega⟩
  set c : ZMod (4 * d) × ZMod (4 * d) → ℂ := fun x => (1 / 4) * cdChar d x
  obtain ⟨G, hG, hGeq⟩ := twistedL_continuation (4 * d) c
  refine ⟨G, hG, fun s hs => ?_⟩
  rw [hGeq s hs, ZInQ.Literature.LSeries_cd_eq hd hsq s]
  refine (LSeries_eq_twistedL (4 * d) c _ (fun n hn => ?_) hs).symm
  rw [hD n hn, heckeCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [c, cdChar_intCast]
  ring

/-- **The reduction for the CR₃ case**: Deuring's identity for every squarefree `d ≡ 5 (mod 8)`
gives the continuation that `TYZRow5b`'s documented route (`tyzRow5b_of_readingA`) uses. -/
theorem heckeContinuation5_of_deuring (hD : ∀ d : ℕ, d % 8 = 5 → Squarefree d → DeuringCd d) :
    ∀ d : ℕ, d % 8 = 5 → Squarefree d →
      ∃ F : ℂ → ℂ, ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F :=
  fun d h5 hsq => isLContinuation_of_deuring (Nat.odd_iff.mpr (by omega)) hsq (hD d h5 hsq)

/-! ### The dual kernel as a lattice sum, and its Mellin transform -/

theorem norm_cexp_two_pi_I (x : ℝ) : ‖cexp (2 * π * I * x)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- `e(a ν₁ + b ν₂)`. -/
noncomputable def ech (a b : ℝ) (p : ℤ × ℤ) : ℂ := cexp (2 * π * I * (a * p.1 + b * p.2))

theorem norm_ech (a b : ℝ) (p : ℤ × ℤ) : ‖ech a b p‖ = 1 := by
  have := norm_cexp_two_pi_I (a * p.1 + b * p.2)
  simpa [ech] using this

theorem hasSum_gaussThetaDual (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun p : ℤ × ℤ => -I * gz 0 0 p * ech a b p * rexp (-π * gq 0 0 p * t))
      (gaussThetaDual a b t) := by
  set fs : ℝ → ℤ → ℂ := fun c n => -I * n * cexp (2 * π * I * c * n) * rexp (-π * n ^ 2 * t)
  set fc : ℝ → ℤ → ℂ := fun c n => cexp (2 * π * I * c * n) * rexp (-π * n ^ 2 * t)
  have hs : ∀ c : ℝ, HasSum (fs c) (sinKernel c t) := fun c => hasSum_int_sinKernel c ht
  have hc : ∀ c : ℝ, HasSum (fc c) (cosKernel c t) := fun c => hasSum_int_cosKernel c ht
  have hsn : ∀ c : ℝ, Summable fun n => ‖fs c n‖ := fun c => by
    have h0 := (hasSum_int_oddKernel 0 ht).summable
    refine (summable_abs_iff.mpr h0).congr fun n => ?_
    have h1 := norm_cexp_two_pi_I (c * n)
    simp only [fs, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_intCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (exp_pos _), add_zero]
    rw [show (2 * π * I * c * n : ℂ) = 2 * π * I * ((c * n : ℝ) : ℂ) by push_cast; ring, h1,
      mul_one, abs_mul, abs_of_pos (exp_pos _)]
  have hcn : ∀ c : ℝ, Summable fun n => ‖fc c n‖ := fun c => by
    have h0 := (hasSum_int_evenKernel 0 ht).summable
    refine (summable_abs_iff.mpr h0).congr fun n => ?_
    have h1 := norm_cexp_two_pi_I (c * n)
    simp only [fc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _), add_zero]
    rw [show (2 * π * I * c * n : ℂ) = 2 * π * I * ((c * n : ℝ) : ℂ) by push_cast; ring, h1,
      one_mul]
  have P1 : HasSum (fun p : ℤ × ℤ => fs a p.1 * fc b p.2) (sinKernel a t * cosKernel b t) := by
    have := (hs a).mul (hc b) (summable_mul_of_summable_norm (hsn a) (hcn b))
    exact_mod_cast this
  have P2 : HasSum (fun p : ℤ × ℤ => fc a p.1 * fs b p.2) (cosKernel a t * sinKernel b t) := by
    have := (hc a).mul (hs b) (summable_mul_of_summable_norm (hcn a) (hsn b))
    exact_mod_cast this
  have P := P1.add (P2.mul_left I)
  have hval : gaussThetaDual a b t = (sinKernel a t * cosKernel b t : ℂ) +
      I * (cosKernel a t * sinKernel b t : ℂ) := rfl
  rw [hval]
  convert P using 1
  funext p
  have h1 : rexp (-π * gq 0 0 p * t) =
      rexp (-π * (p.1 : ℝ) ^ 2 * t) * rexp (-π * (p.2 : ℝ) ^ 2 * t) := by
    rw [← Real.exp_add]; simp only [gq, add_zero]; ring_nf
  have h2 : ech a b p = cexp (2 * π * I * a * p.1) * cexp (2 * π * I * b * p.2) := by
    rw [ech, ← Complex.exp_add]; ring_nf
  simp only [gz, fs, fc, h1, h2]
  push_cast
  ring

/-- **Mellin transform of the dual kernel** as a lattice Dirichlet series, `Re s > 3/2`. -/
theorem hasSum_gaussLambdaDual (a b : ℝ) {s : ℂ} (hs : 3 / 2 < s.re) :
    HasSum (fun p : ℤ × ℤ => π ^ (-s) * Gamma s * (-I * gz 0 0 p * ech a b p) /
      (gq 0 0 p : ℂ) ^ s) (gaussLambdaDual a b s) := by
  refine hasSum_mellin_pi_mul (fun p => ?_) (by linarith)
    (fun t ht => hasSum_gaussThetaDual a b ht) ?_
  · by_cases h : gz 0 0 p = 0
    · left; rw [h]; ring
    · right; rw [gq_eq_norm_sq]; positivity
  · refine (summable_norm_gz_rpow 0 0 (r := 1 - 2 * s.re) (by linarith)).congr fun p => ?_
    rw [gq_eq_norm_sq, norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_ech, mul_one]
    rcases eq_or_ne ‖gz 0 0 p‖ 0 with h | h
    · rw [h, Real.zero_rpow (by linarith), zero_div]
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), div_eq_mul_inv,
        ← Real.rpow_neg (norm_nonneg _), ← Real.rpow_one_add' (norm_nonneg _)]
      · push_cast; ring_nf
      · push_cast; linarith

/-! ### The functional equation of periodic twists, given a Fourier relation -/

/-- The finite Fourier transform `ĉ(ν) = Σ_{j ∈ (ℤ/M)²} c(j) e((j₁ν₁ + j₂ν₂)/M)`. -/
noncomputable def fourierHat (M : ℕ) (c : ZMod M × ZMod M → ℂ) (p : ℤ × ℤ) : ℂ :=
  ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
    ech (((j.1 : ℕ) : ℝ) / (M : ℝ)) (((j.2 : ℕ) : ℝ) / (M : ℝ)) p

/-- The completed twisted L-function `Λ_c = Σ_j c(j) Λ_{j/M}` (entire). -/
noncomputable def lambdaC (M : ℕ) (c : ZMod M × ZMod M → ℂ) (s : ℂ) : ℂ :=
  ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
    gaussLambda (((j.1 : ℕ) : ℝ) / (M : ℝ)) (((j.2 : ℕ) : ℝ) / (M : ℝ)) s

theorem differentiable_lambdaC (M : ℕ) (c : ZMod M × ZMod M → ℂ) :
    Differentiable ℂ (lambdaC M c) :=
  Differentiable.fun_sum fun _ _ => (differentiable_gaussLambda _ _).const_mul _

/-- `Λ_c(s) = M^{2s−1} π^{−s} Γ(s) T_c(s)`, in the form `π^{−s}Γ(s)T_c(s) = M (M²)^{−s} Λ_c(s)`. -/
theorem lambdaC_eq (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ} (hs : 3 / 2 < s.re) :
    π ^ (-s) * Gamma s * twistedL M c s =
      (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s := by
  rw [twistedL_eq M c hs, lambdaC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (hasSum_gaussLambda _ _ hs).tsum_eq, gaussL]
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]
  simp only [cpow_neg]
  ring

/-- The dual side as a Dirichlet series with the Fourier transform. -/
theorem dual_eq (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {s : ℂ} (hs : 3 / 2 < s.re) :
    ∑ j : Fin M × Fin M, c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
      gaussLambdaDual (((j.1 : ℕ) : ℝ) / (M : ℝ)) (((j.2 : ℕ) : ℝ) / (M : ℝ)) s =
    π ^ (-s) * Gamma s * (-I) *
      ∑' p : ℤ × ℤ, fourierHat M c p * gz 0 0 p / (gq 0 0 p : ℂ) ^ s := by
  have h := hasSum_sum (s := Finset.univ) fun (j : Fin M × Fin M) _ =>
    (hasSum_gaussLambdaDual (((j.1 : ℕ) : ℝ) / (M : ℝ)) (((j.2 : ℕ) : ℝ) / (M : ℝ)) hs).mul_left
      (c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)))
  rw [← h.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [fourierHat, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The Fourier relation: `ĉ` vanishes off `(1+i)ℤ[i]` and `ĉ((1+i)μ) = κ c(μ)`. -/
def FourierRel (M : ℕ) (c : ZMod M × ZMod M → ℂ) (κ : ℂ) : Prop :=
  (∀ μ : ℤ × ℤ, fourierHat M c (μ.1 - μ.2, μ.1 + μ.2) = κ * c ((μ.1 : ZMod M), (μ.2 : ZMod M))) ∧
  (∀ ν : ℤ × ℤ, Odd (ν.1 + ν.2) → fourierHat M c ν = 0)

theorem fourierRel_const_mul {M : ℕ} {c : ZMod M × ZMod M → ℂ} {κ : ℂ} (h : FourierRel M c κ)
    (r : ℂ) : FourierRel M (fun x => r * c x) κ := by
  have hh : ∀ p, fourierHat M (fun x => r * c x) p = r * fourierHat M c p := fun p => by
    rw [fourierHat, fourierHat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨fun μ => ?_, fun ν hν => ?_⟩
  · rw [hh, h.1 μ]; ring
  · rw [hh, h.2 ν hν, mul_zero]

/-- `μ ↦ (1 + i) μ` on `ℤ²`. -/
def mulOneAddI (μ : ℤ × ℤ) : ℤ × ℤ := (μ.1 - μ.2, μ.1 + μ.2)

theorem mulOneAddI_injective : Function.Injective mulOneAddI := by
  intro x y h
  simp only [mulOneAddI, Prod.mk.injEq] at h
  ext <;> omega

theorem fourier_tsum_eq (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {κ : ℂ}
    (hF : FourierRel M c κ) (s : ℂ) :
    ∑' p : ℤ × ℤ, fourierHat M c p * gz 0 0 p / (gq 0 0 p : ℂ) ^ s =
      κ * (1 + I) * (2 : ℂ) ^ (-s) * twistedL M c s := by
  set f := fun p : ℤ × ℤ => fourierHat M c p * gz 0 0 p / (gq 0 0 p : ℂ) ^ s
  have hsupp : Function.support f ⊆ Set.range mulOneAddI := by
    intro ν hν
    by_cases hpar : Odd (ν.1 + ν.2)
    · exact absurd (by simp [f, hF.2 ν hpar]) hν
    · rw [Int.not_odd_iff_even] at hpar
      obtain ⟨k, hk⟩ := hpar
      refine ⟨(k, k - ν.1), ?_⟩
      simp only [mulOneAddI]
      ext <;> simp; omega
  rw [← mulOneAddI_injective.tsum_eq hsupp, twistedL, ← tsum_mul_left]
  refine tsum_congr fun μ => ?_
  simp only [f, mulOneAddI]
  rw [hF.1 μ]
  have hz : gz 0 0 (μ.1 - μ.2, μ.1 + μ.2) = (1 + I) * gz 0 0 μ := by
    simp only [gz]; push_cast; ring_nf; rw [I_sq]; ring
  have hq : gq 0 0 (μ.1 - μ.2, μ.1 + μ.2) = 2 * gq 0 0 μ := by
    simp only [gq]; push_cast; ring
  rw [hz, hq, ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) (gq_nonneg _ _ _), cpow_neg]
  push_cast
  field_simp

/-- **Functional equation of `Λ_c`** under the Fourier relation:
`Λ_c(2 − s) = −iκ(1+i) · 2^{−s} · M · (M²)^{−s} · Λ_c(s)` for all `s`. -/
theorem lambdaC_two_sub (M : ℕ) [NeZero M] (c : ZMod M × ZMod M → ℂ) {κ : ℂ}
    (hF : FourierRel M c κ) (s : ℂ) :
    lambdaC M c (2 - s) = -I * κ * (1 + I) * (2 : ℂ) ^ (-s) * (M : ℂ) *
      (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s := by
  have hM2 : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM2⟩
  have hdiff1 : Differentiable ℂ (fun s => lambdaC M c (2 - s)) :=
    (differentiable_lambdaC M c).comp ((differentiable_const _).sub differentiable_id)
  have hdiff2 : Differentiable ℂ (fun s => -I * κ * (1 + I) * (2 : ℂ) ^ (-s) * (M : ℂ) *
      (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s) := by
    refine (((Differentiable.const_mul ?_ _).mul_const _).mul ?_).mul (differentiable_lambdaC M c)
    · exact (differentiable_const_cpow_of_neZero (2 : ℂ)).comp differentiable_id.neg
    · exact (differentiable_const_cpow_of_neZero _).comp differentiable_id.neg
  -- agreement on `Re s > 3/2`
  have hU : {s : ℂ | 3 / 2 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : (fun s => lambdaC M c (2 - s)) =ᶠ[nhds (2 : ℂ)] (fun s => -I * κ * (1 + I) *
      (2 : ℂ) ^ (-s) * (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s) := by
    refine Filter.mem_of_superset hU fun s hs' => ?_
    have hs : 3 / 2 < s.re := hs'
    have h1 : lambdaC M c (2 - s) = ∑ j : Fin M × Fin M,
        c (((j.1 : ℤ) : ZMod M), ((j.2 : ℤ) : ZMod M)) *
          gaussLambdaDual (((j.1 : ℕ) : ℝ) / (M : ℝ)) (((j.2 : ℕ) : ℝ) / (M : ℝ)) s := by
      rw [lambdaC]
      exact Finset.sum_congr rfl fun j _ => by rw [gaussLambda_two_sub]
    show lambdaC M c (2 - s) = _
    rw [h1, dual_eq M c hs, fourier_tsum_eq M c hF s]
    have h2 := lambdaC_eq M c hs
    linear_combination (-I * κ * (1 + I) * (2 : ℂ) ^ (-s)) * h2
  have hfa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff1
  have hga := Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff2
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ (Set.mem_univ 2) hev
    (Set.mem_univ s)

/-! ### `FunctionalEquation5` from Deuring's identity and the Fourier identity -/

/-- **The finite Fourier identity for `C_d`** (quadratic Gauss sums; §2.4 of the report):
`ĉ_d((1+i)μ) = 4d(1+i)(2/d) c_d(μ)` and `ĉ_d = 0` off `(1+i)ℤ[i]`.
Numerically VERIFIED (`fourier_check.py`) on its 2-part and odd part. -/
def CdFourier (d : ℕ) : Prop :=
  FourierRel (4 * d) (cdChar d) (4 * d * (1 + I) * (jacobiSym 2 d : ℂ))

theorem jacobiSym_two_of_mod_eight {d : ℕ} (hd : d % 8 = 5) : jacobiSym 2 d = -1 := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : d % 2 ≠ 0 := by omega
  simp [h2, hd]

theorem cpow_of_pos {r : ℝ} (hr : 0 < r) (z : ℂ) : (r : ℂ) ^ z = cexp (Real.log r * z) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

/-- The bookkeeping of constants: conductor `N = 32d² = 2M²`, `M = 4d`. -/
theorem const_identity {d : ℕ} (hd : 0 < d) (s : ℂ) :
    ((32 * d ^ 2 : ℕ) : ℂ) ^ ((2 - s) / 2) * (2 : ℂ) ^ (-(2 - s)) * ((4 * d : ℕ) : ℂ) *
        ((((4 * d : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(2 - s)) * (-8 * d) * (2 : ℂ) ^ (-s) *
        ((4 * d : ℕ) : ℂ) * ((((4 * d : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) =
      -(((32 * d ^ 2 : ℕ) : ℂ) ^ (s / 2) * (2 : ℂ) ^ (-s) * ((4 * d : ℕ) : ℂ) *
        ((((4 * d : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  set m : ℝ := ((4 * d : ℕ) : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hN : ((32 * d ^ 2 : ℕ) : ℂ) = ((2 * m ^ 2 : ℝ) : ℂ) := by
    rw [hm]; push_cast; ring
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hM : ((4 * d : ℕ) : ℂ) = cexp (Real.log m) := by
    rw [← ofReal_exp, Real.exp_log hm0, hm]; push_cast; ring
  have h8 : (-8 * d : ℂ) = -cexp (Real.log 2 + Real.log m) := by
    rw [← ofReal_add, ← ofReal_exp, Real.exp_add, Real.exp_log two_pos, Real.exp_log hm0, hm]
    push_cast; ring
  have hlogN : Real.log (2 * m ^ 2) = Real.log 2 + 2 * Real.log m := by
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]; push_cast; ring
  have hlogM2 : Real.log (m ^ 2) = 2 * Real.log m := by rw [Real.log_pow]; push_cast; ring
  rw [hN, h8, hM, h2]
  simp only [cpow_of_pos (show (0 : ℝ) < 2 * m ^ 2 by positivity),
    cpow_of_pos (show (0 : ℝ) < m ^ 2 by positivity), cpow_of_pos (show (0 : ℝ) < 2 by norm_num),
    hlogN, hlogM2]
  simp only [neg_mul, mul_neg, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **`FunctionalEquation5` for one `d`, from `DeuringCd d` and `CdFourier d`.** -/
theorem functionalEquation5_of_deuring_fourier {d : ℕ} (h5 : d % 8 = 5) (hsq : Squarefree d)
    (hD : DeuringCd d) (hFo : CdFourier d) (F : ℂ → ℂ)
    (hF : ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F) (s : ℂ)
    (hs0 : 0 < s.re) (hs2 : s.re < 2) :
    ZInQ.Literature.completedL (32 * d ^ 2) F (2 - s) =
      -ZInQ.Literature.completedL (32 * d ^ 2) F s := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨by omega⟩
  have : NeZero (4 * d) := ⟨by omega⟩
  set M := 4 * d with hMdef
  set c : ZMod M × ZMod M → ℂ := fun x => (1 / 4) * cdChar d x
  set κ : ℂ := 4 * d * (1 + I) * (jacobiSym 2 d : ℂ)
  have hFc : FourierRel M c κ := fourierRel_const_mul hFo (1 / 4)
  have hκ : -I * κ * (1 + I) = -8 * d := by
    simp only [κ, jacobiSym_two_of_mod_eight h5]
    push_cast; linear_combination (4 * (d : ℂ) * I + 8 * d) * I_sq
  -- Step 1: `F = T_c` on `Re s > 3/2`.
  have step1 : ∀ s : ℂ, 3 / 2 < s.re → F s = twistedL M c s := by
    intro s hs
    rw [hF.2 s hs, ZInQ.Literature.LSeries_cd_eq hodd hsq s]
    refine LSeries_eq_twistedL M c _ (fun n hn => ?_) hs
    rw [hD n hn, heckeCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [c, M, cdChar_intCast]
    ring
  -- Step 2: `π^{−s} Γ(s) F(s) = M (M²)^{−s} Λ_c(s)` on `Re s > 0`.
  have hM2 : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM2⟩
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have : NeZero (π : ℂ) := ⟨hpi⟩
  set U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hGam : ∀ s ∈ U, DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s fun m hm => by
      have : s.re = -(m : ℝ) := by rw [hm]; simp
      have h0 : (0 : ℝ) < s.re := hs
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  have step2 : ∀ s ∈ U, (π : ℂ) ^ (-s) * Complex.Gamma s * F s =
      (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s := by
    have hf : AnalyticOnNhd ℂ (fun s => (π : ℂ) ^ (-s) * Complex.Gamma s * F s) U := by
      refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
      exact ((((differentiable_const_cpow_of_neZero (π : ℂ)).comp differentiable_id.neg) s).mul
        (hGam s hs) |>.mul (hF.1 s)).differentiableWithinAt
    have hg : AnalyticOnNhd ℂ (fun s => (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) *
        lambdaC M c s) U := by
      refine DifferentiableOn.analyticOnNhd (fun s _ => ?_) hUo
      exact (((((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul
        _).mul (differentiable_lambdaC M c)) s).differentiableWithinAt
    have hU2 : {s : ℂ | 3 / 2 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hev : (fun s => (π : ℂ) ^ (-s) * Complex.Gamma s * F s) =ᶠ[nhds (2 : ℂ)]
        (fun s => (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s) := by
      refine Filter.mem_of_superset hU2 fun s hs' => ?_
      have hs : 3 / 2 < s.re := hs'
      show (π : ℂ) ^ (-s) * Complex.Gamma s * F s = _
      rw [step1 s hs, lambdaC_eq M c hs]
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ U by simp [U]) hev
  -- Step 3: the constants.
  have hsU : s ∈ U := hs0
  have hsU' : 2 - s ∈ U := show 0 < (2 - s).re by rw [sub_re]; norm_num; linarith
  have hsplit : ∀ z : ℂ, (2 * Real.pi : ℂ) ^ (-z) = (2 : ℂ) ^ (-z) * (π : ℂ) ^ (-z) := fun z => by
    have := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) pi_pos.le (-z)
    push_cast at this; exact this
  have hL : ∀ z ∈ U, ZInQ.Literature.completedL (32 * d ^ 2) F z =
      ((32 * d ^ 2 : ℕ) : ℂ) ^ (z / 2) * (2 : ℂ) ^ (-z) * ((M : ℂ) *
        (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-z) * lambdaC M c z) := fun z hz => by
    rw [ZInQ.Literature.completedL, hsplit, ← step2 z hz]; ring
  rw [hL _ hsU', hL _ hsU, lambdaC_two_sub M c hFc s, hκ]
  have hc := const_identity hd0 s
  simp only [M] at *
  linear_combination lambdaC (4 * d) c s * hc

/-- **`FunctionalEquation5` from Deuring's identity and the Fourier identity.** -/
theorem functionalEquation5_of_deuring_fourier'
    (hD : ∀ d : ℕ, d % 8 = 5 → Squarefree d → DeuringCd d)
    (hFo : ∀ d : ℕ, d % 8 = 5 → Squarefree d → CdFourier d) :
    ZInQ.Literature.FunctionalEquation5 :=
  fun d h5 hsq F hF s hs0 hs2 =>
    functionalEquation5_of_deuring_fourier h5 hsq (hD d h5 hsq) (hFo d h5 hsq) F hF s hs0 hs2

end BpHeckeFE
