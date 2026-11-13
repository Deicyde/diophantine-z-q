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

/-! ### `DeuringCd` at the primes `p ≢ 1 (mod 4)` (node B4) -/

/-- `Σ_x ((x³ − d²x)/p) = 0` for `p ≡ 3 (mod 4)` (the involution `x ↦ −x`). -/
theorem sum_quadraticChar_cd_eq_zero {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (d : ℕ) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) = 0 := by
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one hc, ZMod.card]; exact ZMod.χ₄_nat_three_mod_four hp
  set S := ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x)
  have h : S = -S := by
    calc S = ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 - (d : ZMod p) ^ 2 * (-x)) :=
          (Fintype.sum_equiv (Equiv.neg _) _ _ (fun x => rfl)).symm
      _ = ∑ x : ZMod p, quadraticChar (ZMod p) (-1) *
            quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← map_mul]; congr 1; ring
      _ = -S := by rw [hneg]; simp [S]
  linarith

/-- `#{(x, y) ∈ 𝔽_p² : y² = x³ − d²x} = p` for `p ≡ 3 (mod 4)`. -/
theorem card_cd_affine_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (d : ℕ) :
    Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfib : ((Finset.univ.filter fun xy : ZMod p × ZMod p =>
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1).card : ℤ) =
      ∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) + 1) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← quadraticChar_card_sqrts hc, Set.toFinset_ofPred, Finset.card_filter]
    push_cast; rfl
  have h2 : ((Finset.univ.filter fun xy : ZMod p × ZMod p =>
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1).card : ℤ) = p := by
    rw [hfib, Finset.sum_add_distrib, sum_quadraticChar_cd_eq_zero hp d]
    simp [ZMod.card]
  exact_mod_cast h2

theorem cdCoeff_eq_LFunction {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {n : ℕ} (hn : n ≠ 0) :
    ZInQ.Literature.cdCoeff d n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n := by
  rw [ZInQ.Literature.LFunction_cd_apply hd hsq hn]
  simp only [ZInQ.Literature.cdCoeff, hn, ↓reduceIte]

/-- `a_p(C_d) = 0` for `p ≡ 3 (mod 4)`, `p ∤ d`. -/
theorem cdCoeff_prime_of_mod_four_eq_three {d p : ℕ} (hd : Odd d) (hsq : Squarefree d)
    [hpp : Fact p.Prime] (hp : p % 4 = 3) (hpd : ¬ p ∣ d) : ZInQ.Literature.cdCoeff d p = 0 := by
  have h2d : ¬ p ∣ 2 * d := by
    intro h
    rcases (Nat.Prime.dvd_mul hpp.out).mp h with h | h
    · have := Nat.le_of_dvd two_pos h; omega
    · exact hpd h
  rw [cdCoeff_eq_LFunction hd hsq hpp.out.ne_zero,
    ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card hd hsq p h2d,
    card_cd_affine_of_mod_four_eq_three hp d, sub_self]

theorem normFiber_eq_empty_of_mod_four_eq_three {n : ℕ} (hn : n % 4 = 3) : normFiber n = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
  have h := congrArg (Int.cast : ℤ → ZMod 4) (mem_normFiber.mp hq)
  push_cast at h
  have h3 : (n : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod, hn]; rfl
  rw [h3] at h
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
  exact key _ _ h

/-- **`DeuringCd` at a prime `p ≡ 3 (mod 4)`**, `p ∤ d`: both coefficients vanish. -/
theorem deuring_prime_of_mod_four_eq_three {d p : ℕ} (hd : Odd d) (hsq : Squarefree d)
    [Fact p.Prime] (hp : p % 4 = 3) (hpd : ¬ p ∣ d) :
    ((ZInQ.Literature.cdCoeff d p : ℤ) : ℂ) = heckeCoeff d p := by
  rw [cdCoeff_prime_of_mod_four_eq_three hd hsq hp hpd, heckeCoeff,
    normFiber_eq_empty_of_mod_four_eq_three hp]
  simp

/-- **`DeuringCd` at a prime `p ∣ d`**: both coefficients vanish. -/
theorem deuring_prime_of_dvd {d p : ℕ} (hd : Odd d) (hsq : Squarefree d) [hpp : Fact p.Prime]
    (hpd : p ∣ d) : ((ZInQ.Literature.cdCoeff d p : ℤ) : ℂ) = heckeCoeff d p := by
  have hd0 : NeZero d := ⟨by rintro rfl; simp at hd⟩
  rw [cdCoeff_eq_LFunction hd hsq hpp.out.ne_zero,
    ZInQ.Literature.LFunction_cd_apply_prime_of_dvd hd hsq p (dvd_mul_of_dvd_right hpd 2),
    heckeCoeff, Int.cast_zero]
  symm
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  rw [mem_normFiber.mp hq]
  have hJ : jacobiSym (p : ℤ) d = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    intro h
    have h1 : (p : ℤ).gcd d = p := by
      rw [Int.gcd_natCast_natCast]; exact Nat.gcd_eq_left hpd
    rw [h1] at h
    exact hpp.out.one_lt.ne' h
  simp [hJ]

/-- **`DeuringCd` at `p = 2`**: both coefficients vanish (`(1+i) ∣ α` when `N α = 2`). -/
theorem deuring_two {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    ((ZInQ.Literature.cdCoeff d 2 : ℤ) : ℂ) = heckeCoeff d 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [cdCoeff_eq_LFunction hd hsq two_ne_zero,
    ZInQ.Literature.LFunction_cd_apply_prime_of_dvd hd hsq 2 (dvd_mul_right 2 d), heckeCoeff,
    Int.cast_zero]
  symm
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  have h := congrArg (Int.cast : ℤ → ZMod 4) (mem_normFiber.mp hq)
  push_cast at h
  have hc : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 = 2 →
      ¬ ((a, b) = (1, 0) ∨ (a, b) = (3, 2)) ∧ ¬ ((a, b) = (3, 0) ∨ (a, b) = (1, 2)) ∧
      ¬ ((a, b) = (0, 3) ∨ (a, b) = (2, 1)) ∧ ¬ ((a, b) = (0, 1) ∨ (a, b) = (2, 3)) := by decide
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 = 2 → unitOf (a, b) = 0 := by
    intro a b hab
    obtain ⟨h1, h2, h3, h4⟩ := hc a b hab
    simp only [unitOf, h1, h2, h3, h4, ite_false]
  rw [key _ _ h]; simp

/-! ### `DeuringCd` from the Euler product of `L(ψ_d, s)` and the split primes -/

/-- The Euler polynomial of `L(ψ_d, s)` at `p`: `1 − heckeCoeff(p) T + p T²` (`1` at `p ∣ 2d`). -/
noncomputable def heckeEulerPoly (d p : ℕ) : Polynomial ℂ :=
  if p ∣ 2 * d then 1
  else 1 - Polynomial.C (heckeCoeff d p) * Polynomial.X + Polynomial.C (p : ℂ) * Polynomial.X ^ 2

/-- **Euler product of the Hecke L-function** (node B2, a statement about `ℤ[i]` only):
`heckeCoeff d n = Π_{p^k ∥ n} [T^k] (1 / heckeEulerPoly d p)`. -/
def HeckeEuler (d : ℕ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → heckeCoeff d n = n.factorization.prod fun p k =>
    PowerSeries.coeff k (PowerSeries.invOfUnit ((heckeEulerPoly d p : Polynomial ℂ) :
      PowerSeries ℂ) 1)

theorem map_invOfUnit_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (φ : PowerSeries R) (h : PowerSeries.constantCoeff φ = 1) :
    PowerSeries.map f (PowerSeries.invOfUnit φ 1) = PowerSeries.invOfUnit (PowerSeries.map f φ) 1 := by
  have h1 : φ * PowerSeries.invOfUnit φ 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by simp [h])
  have h1' : PowerSeries.map f (PowerSeries.invOfUnit φ 1) * PowerSeries.map f φ = 1 := by
    rw [← map_mul, mul_comm, h1, map_one]
  have h2 : PowerSeries.map f φ * PowerSeries.invOfUnit (PowerSeries.map f φ) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h, map_one, Units.val_one])
  exact left_inv_eq_right_inv h1' h2

/-- The coefficient of `L(C_d, s)` at a good prime in the form of `cdEulerPoly`. -/
theorem cdCoeff_prime_eq {d p : ℕ} (hd : Odd d) (hsq : Squarefree d) [hpp : Fact p.Prime]
    (hp : ¬ p ∣ 2 * d) :
    ZInQ.Literature.cdCoeff d p =
      (p : ℤ) + 1 - Nat.card (ZInQ.Literature.cdModel (ZMod p) d).toAffine.Point := by
  rw [cdCoeff_eq_LFunction hd hsq hpp.out.ne_zero, ZInQ.Literature.LFunction_cd_apply_prime hd hsq p]
  simp only [hp, ↓reduceIte, ZInQ.Literature.cdModel_eq_shortCurve]

/-- **`DeuringCd` from the Euler product and the primes.** If `heckeCoeff d` has the Euler
product `HeckeEuler d` and agrees with `a_p(C_d)` at every prime, then `DeuringCd d`. -/
theorem deuringCd_of_heckeEuler {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (hE : HeckeEuler d)
    (hP : ∀ p : ℕ, p.Prime → ((ZInQ.Literature.cdCoeff d p : ℤ) : ℂ) = heckeCoeff d p) :
    DeuringCd d := by
  intro n hn
  rw [hE n hn, ZInQ.Literature.cdCoeff]
  simp only [hn, ↓reduceIte]
  rw [Finsupp.prod, Int.cast_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have : Fact p.Prime := ⟨hpp⟩
  have hc0 : PowerSeries.constantCoeff
      ((ZInQ.Literature.cdEulerPoly d p : Polynomial ℤ) : PowerSeries ℤ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      ZInQ.Literature.cdEulerPoly_coeff_zero]
  have hpoly : heckeEulerPoly d p = (ZInQ.Literature.cdEulerPoly d p).map (Int.castRingHom ℂ) := by
    unfold heckeEulerPoly ZInQ.Literature.cdEulerPoly
    split_ifs with h
    · simp
    · rw [← hP p hpp, cdCoeff_prime_eq hd hsq h]
      simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul]
  rw [hpoly, Polynomial.polynomial_map_coe, ← map_invOfUnit_one _ _ hc0, PowerSeries.coeff_map]
  rfl

/-- **Gauss's theorem at the split primes** (node B3): `a_p(C_d) = heckeCoeff d p` for primes
`p ≡ 1 (mod 4)`, `p ∤ d`; that is, `a_p = (p/d)(π + π̄)` with `π ≡ 1 (mod 2+2i)`, `ππ̄ = p`. -/
def GaussSplit (d : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ¬ p ∣ d →
    ((ZInQ.Literature.cdCoeff d p : ℤ) : ℂ) = heckeCoeff d p

/-- **`DeuringCd` from the Euler product of `L(ψ_d, s)` and Gauss's theorem at split primes**
(the other primes are `deuring_prime_of_mod_four_eq_three`, `deuring_prime_of_dvd`,
`deuring_two`). -/
theorem deuringCd_of_heckeEuler_gaussSplit {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (hE : HeckeEuler d) (hS : GaussSplit d) : DeuringCd d := by
  refine deuringCd_of_heckeEuler hd hsq hE fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpd : p ∣ d
  · exact deuring_prime_of_dvd hd hsq hpd
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact deuring_two hd hsq
  have : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp hodd; omega
  rcases this with h1 | h3
  · exact hS p hp h1 hpd
  · exact deuring_prime_of_mod_four_eq_three hd hsq h3 hpd

/-- **The two literature Props from two statements about `ℤ[i]` and `𝔽_p`, plus `CdFourier`.** -/
theorem literature_hecke_fe_of_euler_gauss_fourier
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GaussSplit d)
    (hFo : ∀ d : ℕ, d % 8 = 5 → Squarefree d → CdFourier d) :
    (∀ d : ℕ, d % 8 = 5 → Squarefree d →
      ∃ F : ℂ → ℂ, ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F) ∧
    ZInQ.Literature.FunctionalEquation5 := by
  have hD : ∀ d : ℕ, d % 8 = 5 → Squarefree d → DeuringCd d := fun d h5 hsq =>
    deuringCd_of_heckeEuler_gaussSplit (Nat.odd_iff.mpr (by omega)) hsq (hE d h5 hsq) (hS d h5 hsq)
  exact ⟨heckeContinuation5_of_deuring hD, functionalEquation5_of_deuring_fourier' hD hFo⟩

/-- `HeckeContinuation` restricted to the case the headline uses. -/
def HeckeContinuation5 : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∃ F : ℂ → ℂ, ZInQ.Literature.IsLContinuation (ZInQ.shortCurve (-(d : ℚ) ^ 2)) F

/-- The documented route to `TYZRow5b` (`tyzRow5b_of_readingA`) needs only `HeckeContinuation5`. -/
theorem tyzRow5b_of_readingA_five (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hH : HeckeContinuation5) : ZInQ.Literature.TYZRow5b := by
  intro d hd hsq h5b
  obtain ⟨F, hF⟩ := hH d hd hsq
  refine ⟨F, hF, ?_⟩
  by_contra h
  have h0 := (hA d hd hsq F hF (ZInQ.Literature.two_le_of_not_le_one h)).2
  rw [h0] at h5b
  exact zero_ne_one h5b

theorem heckeContinuation5_of_literature
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GaussSplit d) : HeckeContinuation5 :=
  heckeContinuation5_of_deuring fun d h5 hsq =>
    deuringCd_of_heckeEuler_gaussSplit (Nat.odd_iff.mpr (by omega)) hsq (hE d h5 hsq) (hS d h5 hsq)

/-! ### The Hecke character `ψ_d` is completely multiplicative (node B1) -/

/-- `unitOf` with values in `ℤ[i]` (decidable equality). -/
def unitG (t : ZMod 4 × ZMod 4) : GaussianInt :=
  if t = (1, 0) ∨ t = (3, 2) then 1
  else if t = (3, 0) ∨ t = (1, 2) then -1
  else if t = (0, 3) ∨ t = (2, 1) then ⟨0, 1⟩
  else if t = (0, 1) ∨ t = (2, 3) then ⟨0, -1⟩
  else 0

theorem unitOf_eq_unitG (t : ZMod 4 × ZMod 4) : unitOf t = ((unitG t : GaussianInt) : ℂ) := by
  unfold unitOf unitG
  split_ifs <;> simp [GaussianInt.toComplex_def']

/-- Multiplicativity of the unit normalization on `(ℤ[i]/4)`: a finite check. -/
theorem unitG_mul : ∀ a b c e : ZMod 4,
    unitG (a * c - b * e, a * e + b * c) = unitG (a, b) * unitG (c, e) := by
  decide

/-- Gaussian multiplication on `ℤ²`. -/
def gmul (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- The Hecke character `ψ_d(α) = (N(α)/d) u(α) α` on `ℤ[i] = ℤ²`. -/
noncomputable def psi (d : ℕ) (p : ℤ × ℤ) : ℂ :=
  (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p

/-- **`ψ_d` is completely multiplicative.** -/
theorem psi_mul (d : ℕ) (p q : ℤ × ℤ) : psi d (gmul p q) = psi d p * psi d q := by
  have hN : (gmul p q).1 ^ 2 + (gmul p q).2 ^ 2 = (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by
    simp only [gmul]; ring
  have hU : unitOf (((gmul p q).1 : ZMod 4), ((gmul p q).2 : ZMod 4)) =
      unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) := by
    rw [unitOf_eq_unitG, unitOf_eq_unitG, unitOf_eq_unitG, ← map_mul, ← unitG_mul]
    simp only [gmul]; push_cast; rfl
  have hz : gz 0 0 (gmul p q) = gz 0 0 p * gz 0 0 q := by
    simp only [gz, gmul]; push_cast; ring_nf; rw [I_sq]; ring
  rw [psi, psi, psi, hN, jacobiSym.mul_left, hU, hz]
  push_cast
  ring

/-- `heckeCoeff d n = ¼ Σ_{N(α) = n} ψ_d(α)`. -/
theorem heckeCoeff_eq_sum_psi (d n : ℕ) :
    heckeCoeff d n = (1 / 4) * ∑ p ∈ normFiber n, psi d p := rfl

/-- `ψ_d(ε) = 1` for the four units `ε ∈ {±1, ±i}`; so `ψ_d(εα) = ψ_d(α)` and `ψ_d` is a
function of the ideal `(α)`. -/
theorem psi_units (d : ℕ) :
    psi d (1, 0) = 1 ∧ psi d (-1, 0) = 1 ∧ psi d (0, 1) = 1 ∧ psi d (0, -1) = 1 := by
  have hc : unitOf ((1 : ZMod 4), (0 : ZMod 4)) = 1 ∧ unitOf ((-1 : ZMod 4), (0 : ZMod 4)) = -1 ∧
      unitOf ((0 : ZMod 4), (1 : ZMod 4)) = -I ∧ unitOf ((0 : ZMod 4), (-1 : ZMod 4)) = I := by
    simp only [unitOf_eq_unitG]
    have h : unitG (1, 0) = 1 ∧ unitG (-1, 0) = -1 ∧ unitG (0, 1) = ⟨0, -1⟩ ∧
        unitG (0, -1) = ⟨0, 1⟩ := by decide
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
    simp [GaussianInt.toComplex_def']
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [psi, gz] <;> push_cast <;>
    simp [h1, h2, h3, h4, jacobiSym.one_left]

theorem psi_unit_mul (d : ℕ) (p : ℤ × ℤ) :
    psi d (gmul (0, 1) p) = psi d p ∧ psi d (gmul (-1, 0) p) = psi d p := by
  obtain ⟨-, h2, h3, -⟩ := psi_units d
  exact ⟨by rw [psi_mul, h3, one_mul], by rw [psi_mul, h2, one_mul]⟩

/-! ### `CdFourier` from the odd quadratic Gauss sum (node C2): CRT and the 2-part -/

/-- The CRT parametrization `(a, b) ↦ d a + 4 b` of `ℤ / 4d`, `d` odd. -/
theorem crt_injective {d : ℕ} (hd : Odd d) :
    Function.Injective fun x : Fin 4 × Fin d =>
      ((d * x.1 + 4 * x.2) % (4 * d) : ℕ) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  have hM : d * a + 4 * b ≡ d * a' + 4 * b' [MOD 4 * d] := h
  have h4 : d * a ≡ d * a' [MOD 4] := by
    have := hM.of_mul_right d
    have e1 : d * a + 4 * b ≡ d * a [MOD 4] := by
      simp [Nat.ModEq, Nat.add_mul_mod_self_left]
    have e2 : d * a' + 4 * b' ≡ d * a' [MOD 4] := by
      simp [Nat.ModEq, Nat.add_mul_mod_self_left]
    exact e1.symm.trans (this.trans e2)
  have hdd : d * a + 4 * b ≡ d * a' + 4 * b' [MOD d] := hM.of_mul_left 4
  have hd' : 4 * b ≡ 4 * b' [MOD d] := by
    have e1 : d * a + 4 * b ≡ 4 * b [MOD d] := by
      simp [Nat.ModEq]
    have e2 : d * a' + 4 * b' ≡ 4 * b' [MOD d] := by
      simp [Nat.ModEq]
    exact e1.symm.trans (hdd.trans e2)
  have hc4 : Nat.gcd 4 d = 1 := by
    have : Nat.Coprime 2 d := (Nat.coprime_two_left).mpr hd
    exact Nat.Coprime.pow_left 2 this
  have ha := Nat.ModEq.cancel_left_of_coprime hc4 h4
  have hb := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc4) hd'
  have ha' : (a : ℕ) = a' := by
    have := ha; unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt a'.2] at this
  have hb' : (b : ℕ) = b' := by
    have := hb; unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt b'.2] at this
  rw [Fin.ext ha', Fin.ext hb']

/-- **CRT for sums**: for a `4d`-periodic `g`, `Σ_{j mod 4d} g(j) = Σ_{a mod 4} Σ_{b mod d} g(da + 4b)`. -/
theorem sum_crt {d : ℕ} (hd : Odd d) (g : ℤ → ℂ) (hg : ∀ x : ℤ, g x = g (x % (4 * d : ℕ))) :
    ∑ j : Fin (4 * d), g j = ∑ a : Fin 4, ∑ b : Fin d, g (d * a + 4 * b) := by
  have hd0 : 0 < d := hd.pos
  rw [← Finset.sum_product']
  let φ : Fin 4 × Fin d → Fin (4 * d) := fun x =>
    ⟨(d * x.1 + 4 * x.2) % (4 * d), Nat.mod_lt _ (by positivity)⟩
  have hinj : Function.Injective φ := fun x y h => crt_injective hd (Fin.ext_iff.mp h)
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [Fintype.card_fin, Fintype.card_prod]⟩
  refine (Fintype.sum_bijective φ hbij _ _ fun x => ?_).symm
  simp only [φ]
  rw [hg (d * x.1 + 4 * x.2)]
  congr 1

/-- The 2-part of `ĉ_d`: `Σ_{a ∈ (ℤ/4)²} u(a) e((a₁ν₁ + a₂ν₂)/4)`. -/
noncomputable def g2Sum (ν : ℤ × ℤ) : ℂ :=
  ∑ a : Fin 4 × Fin 4, unitOf ((((a.1 : ℕ) : ℤ) : ZMod 4), (((a.2 : ℕ) : ℤ) : ZMod 4)) *
    cexp (2 * π * I * (((a.1 : ℕ) : ℂ) * ν.1 + ((a.2 : ℕ) : ℂ) * ν.2) / 4)

/-- The odd part of `ĉ_d`: `Σ_{b ∈ (ℤ/d)²} (N(b)/d) e((b₁ν₁ + b₂ν₂)/d)`. -/
noncomputable def oddSum (d : ℕ) (ν : ℤ × ℤ) : ℂ :=
  ∑ b : Fin d × Fin d, (jacobiSym (((b.1 : ℕ) : ℤ) ^ 2 + ((b.2 : ℕ) : ℤ) ^ 2) d : ℂ) *
    cexp (2 * π * I * (((b.1 : ℕ) : ℂ) * ν.1 + ((b.2 : ℕ) : ℂ) * ν.2) / d)

theorem cexp_two_pi_I_int_mul (n : ℤ) : cexp (2 * π * I * n) = 1 := by
  rw [show (2 * π * I * n : ℂ) = n * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem cexp_shift {M : ℕ} (hM : (M : ℂ) ≠ 0) (A : ℂ) (k n : ℤ) :
    cexp (2 * π * I * (A + ((k * M : ℤ) : ℂ) * n) / M) = cexp (2 * π * I * A / M) := by
  rw [show 2 * π * I * (A + ((k * M : ℤ) : ℂ) * n) / M = 2 * π * I * A / M +
      2 * π * I * ((k * n : ℤ) : ℂ) by push_cast; field_simp,
    Complex.exp_add, cexp_two_pi_I_int_mul, mul_one]

theorem intCast_emod_eq (x : ℤ) (M : ℕ) :
    ((x % (M : ℤ) : ℤ) : ℂ) = (x : ℂ) + ((-(x / (M : ℤ)) * M : ℤ) : ℂ) := by
  have := Int.emod_add_ediv_mul x (M : ℤ)
  have h : x % (M : ℤ) = x + (-(x / (M : ℤ)) * M) := by linarith
  rw [h]; push_cast; ring

/-- **Factorization of `ĉ_d`** into the 2-part and the odd part (`d ≡ 1 (mod 4)`). -/
theorem fourierHat_cd_eq {d : ℕ} (hd4 : d % 4 = 1) (ν : ℤ × ℤ) :
    fourierHat (4 * d) (cdChar d) ν = g2Sum ν * oddSum d ν := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd0 : 0 < d := hodd.pos
  have : NeZero d := ⟨hd0.ne'⟩
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hMC : ((4 * d : ℕ) : ℂ) ≠ 0 := by push_cast; exact mul_ne_zero (by norm_num) hdC
  set F : ℤ → ℤ → ℂ := fun x y => (jacobiSym (x ^ 2 + y ^ 2) d : ℂ) *
    unitOf ((x : ZMod 4), (y : ZMod 4)) *
      cexp (2 * π * I * ((x : ℂ) * ν.1 + (y : ℂ) * ν.2) / ((4 * d : ℕ) : ℂ)) with hFdef
  -- periodicity of `F`
  have hmodd : ∀ x : ℤ, x % ((4 * d : ℕ) : ℤ) ≡ x [ZMOD d] := fun x => by
    have : (x % ((4 * d : ℕ) : ℤ)) ≡ x [ZMOD ((4 * d : ℕ) : ℤ)] :=
      Int.emod_emod_of_dvd x (dvd_refl _)
    push_cast at this
    exact this.of_mul_left 4
  have hmod4 : ∀ x : ℤ, ((x % ((4 * d : ℕ) : ℤ) : ℤ) : ZMod 4) = (x : ZMod 4) := fun x => by
    have : (x % ((4 * d : ℕ) : ℤ)) ≡ x [ZMOD ((4 * d : ℕ) : ℤ)] :=
      Int.emod_emod_of_dvd x (dvd_refl _)
    push_cast at this
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (this.of_mul_right d)
  have hperx : ∀ x y : ℤ, F x y = F (x % ((4 * d : ℕ) : ℤ)) y := fun x y => by
    simp only [F]
    rw [hmod4, jacobiSym.mod_left' (((hmodd x).pow 2).add_right _).symm, intCast_emod_eq,
      add_mul, add_right_comm, cexp_shift hMC]
  have hpery : ∀ x y : ℤ, F x y = F x (y % ((4 * d : ℕ) : ℤ)) := fun x y => by
    simp only [F]
    rw [hmod4, jacobiSym.mod_left' (((hmodd y).pow 2).add_left _).symm, intCast_emod_eq,
      add_mul, ← add_assoc, cexp_shift hMC]
  -- the summand of `fourierHat` is `F`
  have h1 : fourierHat (4 * d) (cdChar d) ν =
      ∑ j1 : Fin (4 * d), ∑ j2 : Fin (4 * d), F j1 j2 := by
    rw [fourierHat, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
    rw [cdChar_intCast (d := d) ((j1 : ℤ), (j2 : ℤ))]
    simp only [F, ech]
    congr 2
    push_cast
    ring
  -- CRT on both coordinates
  have h2 : ∑ j1 : Fin (4 * d), ∑ j2 : Fin (4 * d), F j1 j2 =
      ∑ a1 : Fin 4, ∑ b1 : Fin d, ∑ a2 : Fin 4, ∑ b2 : Fin d,
        F (d * a1 + 4 * b1) (d * a2 + 4 * b2) := by
    have hin : ∀ x : ℤ, ∑ j2 : Fin (4 * d), F x j2 =
        ∑ a2 : Fin 4, ∑ b2 : Fin d, F x (d * a2 + 4 * b2) := fun x =>
      sum_crt hodd (F x) fun y => hpery x y
    simp_rw [hin]
    exact sum_crt hodd (fun x => ∑ a2 : Fin 4, ∑ b2 : Fin d, F x (d * a2 + 4 * b2))
      fun x => Finset.sum_congr rfl fun a2 _ =>
        Finset.sum_congr rfl fun b2 _ => hperx x _
  -- each term factors
  have hd4' : (d : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, hd4]; rfl
  have hJ16 : jacobiSym 16 d = 1 := by
    have h4 : Int.gcd 4 d = 1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
      exact Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr hodd)
    have := jacobiSym.sq_one' h4
    norm_num at this; exact this
  have h3 : ∀ (a1 a2 : Fin 4) (b1 b2 : Fin d),
      F (d * a1 + 4 * b1) (d * a2 + 4 * b2) =
        (unitOf ((((a1 : ℕ) : ℤ) : ZMod 4), (((a2 : ℕ) : ℤ) : ZMod 4)) *
          cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / 4)) *
        ((jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) d : ℂ) *
          cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / d)) := by
    intro a1 a2 b1 b2
    simp only [F]
    have hj : jacobiSym ((d * a1 + 4 * b1 : ℤ) ^ 2 + (d * a2 + 4 * b2 : ℤ) ^ 2) d =
        jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) d := by
      rw [jacobiSym.mod_left' (b := d) (a₂ := 16 * (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2)),
        jacobiSym.mul_left, hJ16, one_mul]
      exact Int.modEq_of_dvd ⟨-(d * ((a1 : ℕ) : ℤ) ^ 2 + 8 * ((a1 : ℕ) : ℤ) * ((b1 : ℕ) : ℤ) +
        d * ((a2 : ℕ) : ℤ) ^ 2 + 8 * ((a2 : ℕ) : ℤ) * ((b2 : ℕ) : ℤ)), by ring⟩
    have hu : (((d * a1 + 4 * b1 : ℤ) : ZMod 4), ((d * a2 + 4 * b2 : ℤ) : ZMod 4)) =
        ((((a1 : ℕ) : ℤ) : ZMod 4), (((a2 : ℕ) : ℤ) : ZMod 4)) := by
      push_cast
      rw [hd4', show (4 : ZMod 4) = 0 from rfl]
      simp
    have he : cexp (2 * π * I * (((d * a1 + 4 * b1 : ℤ) : ℂ) * ν.1 +
        ((d * a2 + 4 * b2 : ℤ) : ℂ) * ν.2) / ((4 * d : ℕ) : ℂ)) =
        cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / 4) *
        cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / d) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [hj, hu, he]
    ring
  rw [h1, h2, g2Sum, oddSum, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b2 _ => h3 a1 a2 b1 b2

/-- `i^k` in `ℤ[i]` for `k ∈ ℤ/4`. -/
def iPow (k : ZMod 4) : GaussianInt := (⟨0, 1⟩ : GaussianInt) ^ k.val

theorem cexp_two_pi_I_div_four (m : ℤ) :
    cexp (2 * π * I * m / 4) = ((iPow (m : ZMod 4) : GaussianInt) : ℂ) := by
  have hI : cexp (π / 2 * I) = I := by
    rw [Complex.exp_mul_I, ← ofReal_ofNat, ← ofReal_div, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  have h1 : cexp (2 * π * I * m / 4) = I ^ m := by
    rw [show (2 * π * I * m / 4 : ℂ) = m * (π / 2 * I) by ring, Complex.exp_int_mul, hI]
  have h4 : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, Complex.I_pow_four]
  have h2 : I ^ m = I ^ ((m : ZMod 4).val) := by
    have hm : m = 4 * (m / 4) + ((m : ZMod 4).val : ℤ) := by
      rw [ZMod.val_intCast]; omega
    conv_lhs => rw [hm]
    rw [zpow_add₀ I_ne_zero, zpow_mul, h4, one_zpow, one_mul, zpow_natCast]
  rw [h1, h2, iPow, map_pow]
  congr 1
  simp [GaussianInt.toComplex_def']

/-- The 2-part in `ℤ[i]`. -/
def g2G (n : ZMod 4 × ZMod 4) : GaussianInt :=
  ∑ a : Fin 4 × Fin 4, unitG ((((a.1 : ℕ) : ℤ) : ZMod 4), (((a.2 : ℕ) : ℤ) : ZMod 4)) *
    iPow ((((a.1 : ℕ) : ℤ) : ZMod 4) * n.1 + (((a.2 : ℕ) : ℤ) : ZMod 4) * n.2)

theorem g2Sum_eq (ν : ℤ × ℤ) : g2Sum ν = ((g2G ((ν.1 : ZMod 4), (ν.2 : ZMod 4)) : GaussianInt) : ℂ) := by
  rw [g2Sum, g2G, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← unitOf_eq_unitG]
  congr 1
  have := cexp_two_pi_I_div_four (((a.1 : ℕ) : ℤ) * ν.1 + ((a.2 : ℕ) : ℤ) * ν.2)
  push_cast at this ⊢
  exact this

/-- The 2-part table (16 × 16 terms), by `decide`. -/
theorem g2G_table :
    (∀ m1 m2 : ZMod 4, g2G (m1 - m2, m1 + m2) = 4 * (1 + ⟨0, 1⟩) * unitG (m1, m2)) ∧
    (∀ n1 n2 : ZMod 4, (n1 + n2).val % 2 = 1 → g2G (n1, n2) = 0) := by
  decide

/-- **The odd quadratic Gauss sum over `(ℤ/d)²`** (node C2, odd part):
`Σ_{b ∈ (ℤ/d)²} (N(b)/d) e((b₁ν₁ + b₂ν₂)/d) = d (N(ν)/d)`. Numerically VERIFIED for
`d ∈ {5, 13, 21, 3, 7}` (`fourier_check.py`); for prime `d = p` it is `g(χ_p)² χ_p(−1) = p`
(`p ≡ 1 (mod 4)`) or the quadratic Gauss sum of `𝔽_{p²}` (`p ≡ 3 (mod 4)`). -/
def OddGauss (d : ℕ) : Prop :=
  ∀ ν : ℤ × ℤ, oddSum d ν = d * (jacobiSym (ν.1 ^ 2 + ν.2 ^ 2) d : ℂ)

/-- **`CdFourier` from the odd Gauss sum** (the CRT and the 2-part are proved). -/
theorem cdFourier_of_oddGauss {d : ℕ} (hd4 : d % 4 = 1) (hO : OddGauss d) : CdFourier d := by
  have : NeZero d := ⟨by omega⟩
  refine ⟨fun μ => ?_, fun ν hν => ?_⟩
  · rw [fourierHat_cd_eq hd4, g2Sum_eq, hO, cdChar_intCast]
    push_cast
    rw [g2G_table.1, map_mul, map_mul, ← unitOf_eq_unitG]
    have hN : (μ.1 - μ.2) ^ 2 + (μ.1 + μ.2) ^ 2 = 2 * (μ.1 ^ 2 + μ.2 ^ 2) := by ring
    simp only [hN, jacobiSym.mul_left]
    push_cast
    have h4 : GaussianInt.toComplex 4 = 4 := map_ofNat _ 4
    simp [GaussianInt.toComplex_def', h4]
    ring
  · rw [fourierHat_cd_eq hd4, g2Sum_eq]
    have hpar : (((ν.1 : ZMod 4) + (ν.2 : ZMod 4))).val % 2 = 1 := by
      have h := ZMod.val_intCast (n := 4) (ν.1 + ν.2)
      push_cast at h
      obtain ⟨k, hk⟩ := hν
      have : ((((ν.1 : ZMod 4) + (ν.2 : ZMod 4))).val : ℤ) % 2 = 1 := by rw [h]; omega
      omega
    rw [g2G_table.2 _ _ hpar]
    simp

/-- **The two literature Props from three elementary statements**: the Euler product of
`L(ψ_d, s)` (`HeckeEuler`, about `ℤ[i]`), Gauss's theorem at split primes (`GaussSplit`), and the
odd quadratic Gauss sum (`OddGauss`). -/
theorem literature_hecke_fe_of_euler_gauss_oddGauss
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GaussSplit d)
    (hO : ∀ d : ℕ, d % 8 = 5 → Squarefree d → OddGauss d) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_euler_gauss_fourier hE hS fun d h5 hsq =>
    cdFourier_of_oddGauss (by omega) (hO d h5 hsq)

/-! ### `OddGauss` is multiplicative: reduction to odd primes -/

theorem crt_injective2 {m n : ℕ} (hmn : Nat.Coprime m n) :
    Function.Injective fun x : Fin m × Fin n => ((n * x.1 + m * x.2) % (m * n) : ℕ) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  have hM : n * a + m * b ≡ n * a' + m * b' [MOD m * n] := h
  have hm' : n * a ≡ n * a' [MOD m] := by
    have := hM.of_mul_right n
    have e1 : n * a + m * b ≡ n * a [MOD m] := by simp [Nat.ModEq]
    have e2 : n * a' + m * b' ≡ n * a' [MOD m] := by simp [Nat.ModEq]
    exact e1.symm.trans (this.trans e2)
  have hn' : m * b ≡ m * b' [MOD n] := by
    have := hM.of_mul_left m
    have e1 : n * a + m * b ≡ m * b [MOD n] := by simp [Nat.ModEq]
    have e2 : n * a' + m * b' ≡ m * b' [MOD n] := by simp [Nat.ModEq]
    exact e1.symm.trans (this.trans e2)
  have ha := Nat.ModEq.cancel_left_of_coprime hmn hm'
  have hb := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hmn) hn'
  have ha' : (a : ℕ) = a' := by
    have := ha; unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt a'.2] at this
  have hb' : (b : ℕ) = b' := by
    have := hb; unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt b'.2] at this
  rw [Fin.ext ha', Fin.ext hb']

theorem sum_crt2 {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (g : ℤ → ℂ)
    (hg : ∀ x : ℤ, g x = g (x % (m * n : ℕ))) :
    ∑ j : Fin (m * n), g j = ∑ a : Fin m, ∑ b : Fin n, g (n * a + m * b) := by
  rw [← Finset.sum_product']
  let φ : Fin m × Fin n → Fin (m * n) := fun x =>
    ⟨(n * x.1 + m * x.2) % (m * n), Nat.mod_lt _ (by positivity)⟩
  have hinj : Function.Injective φ := fun x y h => crt_injective2 hmn (Fin.ext_iff.mp h)
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [Fintype.card_fin, Fintype.card_prod]⟩
  refine (Fintype.sum_bijective φ hbij _ _ fun x => ?_).symm
  simp only [φ]
  rw [hg (n * x.1 + m * x.2)]
  congr 1

/-- **Multiplicativity of the odd Gauss sum**: `OddGauss m ∧ OddGauss n ⟹ OddGauss (mn)` for
coprime `m, n > 0`. -/
theorem oddGauss_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n)
    (hOm : OddGauss m) (hOn : OddGauss n) : OddGauss (m * n) := by
  intro ν
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hMC : ((m * n : ℕ) : ℂ) ≠ 0 := by push_cast; exact mul_ne_zero hmC hnC
  set G : ℤ → ℤ → ℂ := fun x y => (jacobiSym (x ^ 2 + y ^ 2) (m * n) : ℂ) *
    cexp (2 * π * I * ((x : ℂ) * ν.1 + (y : ℂ) * ν.2) / ((m * n : ℕ) : ℂ)) with hGdef
  have hmodd : ∀ x : ℤ, x % ((m * n : ℕ) : ℤ) ≡ x [ZMOD ((m * n : ℕ) : ℤ)] := fun x =>
    Int.emod_emod_of_dvd x (dvd_refl _)
  have hperx : ∀ x y : ℤ, G x y = G (x % ((m * n : ℕ) : ℤ)) y := fun x y => by
    simp only [G]
    rw [jacobiSym.mod_left' (((hmodd x).pow 2).add_right _).symm, intCast_emod_eq,
      add_mul, add_right_comm, cexp_shift hMC]
  have hpery : ∀ x y : ℤ, G x y = G x (y % ((m * n : ℕ) : ℤ)) := fun x y => by
    simp only [G]
    rw [jacobiSym.mod_left' (((hmodd y).pow 2).add_left _).symm, intCast_emod_eq,
      add_mul, ← add_assoc, cexp_shift hMC]
  have h1 : oddSum (m * n) ν = ∑ j1 : Fin (m * n), ∑ j2 : Fin (m * n), G j1 j2 := by
    rw [oddSum, Fintype.sum_prod_type]
    rfl
  have h2 : ∑ j1 : Fin (m * n), ∑ j2 : Fin (m * n), G j1 j2 =
      ∑ a1 : Fin m, ∑ b1 : Fin n, ∑ a2 : Fin m, ∑ b2 : Fin n,
        G (n * a1 + m * b1) (n * a2 + m * b2) := by
    have hin : ∀ x : ℤ, ∑ j2 : Fin (m * n), G x j2 =
        ∑ a2 : Fin m, ∑ b2 : Fin n, G x (n * a2 + m * b2) := fun x =>
      sum_crt2 hmn hm hn (G x) fun y => hpery x y
    simp_rw [hin]
    exact sum_crt2 hmn hm hn (fun x => ∑ a2 : Fin m, ∑ b2 : Fin n, G x (n * a2 + m * b2))
      fun x => Finset.sum_congr rfl fun a2 _ => Finset.sum_congr rfl fun b2 _ => hperx x _
  have hgm : Int.gcd (n : ℤ) m = 1 := by
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hmn
  have hgn : Int.gcd (m : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hmn
  have h3 : ∀ (a1 a2 : Fin m) (b1 b2 : Fin n),
      G (n * a1 + m * b1) (n * a2 + m * b2) =
        ((jacobiSym (((a1 : ℕ) : ℤ) ^ 2 + ((a2 : ℕ) : ℤ) ^ 2) m : ℂ) *
          cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / m)) *
        ((jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) n : ℂ) *
          cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / n)) := by
    intro a1 a2 b1 b2
    simp only [G]
    have hjm : jacobiSym (((n : ℤ) * a1 + m * b1) ^ 2 + ((n : ℤ) * a2 + m * b2) ^ 2) m =
        jacobiSym (((a1 : ℕ) : ℤ) ^ 2 + ((a2 : ℕ) : ℤ) ^ 2) m := by
      rw [jacobiSym.mod_left' (b := m) (a₂ := (n : ℤ) ^ 2 * (((a1 : ℕ) : ℤ) ^ 2 + ((a2 : ℕ) : ℤ) ^ 2)),
        jacobiSym.mul_left, jacobiSym.sq_one' hgm, one_mul]
      exact Int.modEq_of_dvd ⟨-(2 * n * ((a1 : ℕ) : ℤ) * ((b1 : ℕ) : ℤ) + m * ((b1 : ℕ) : ℤ) ^ 2 +
        2 * n * ((a2 : ℕ) : ℤ) * ((b2 : ℕ) : ℤ) + m * ((b2 : ℕ) : ℤ) ^ 2), by ring⟩
    have hjn : jacobiSym (((n : ℤ) * a1 + m * b1) ^ 2 + ((n : ℤ) * a2 + m * b2) ^ 2) n =
        jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) n := by
      rw [jacobiSym.mod_left' (b := n) (a₂ := (m : ℤ) ^ 2 * (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2)),
        jacobiSym.mul_left, jacobiSym.sq_one' hgn, one_mul]
      exact Int.modEq_of_dvd ⟨-(n * ((a1 : ℕ) : ℤ) ^ 2 + 2 * m * ((a1 : ℕ) : ℤ) * ((b1 : ℕ) : ℤ) +
        n * ((a2 : ℕ) : ℤ) ^ 2 + 2 * m * ((a2 : ℕ) : ℤ) * ((b2 : ℕ) : ℤ)), by ring⟩
    have he : cexp (2 * π * I * ((((n : ℤ) * a1 + m * b1 : ℤ) : ℂ) * ν.1 +
        (((n : ℤ) * a2 + m * b2 : ℤ) : ℂ) * ν.2) / ((m * n : ℕ) : ℂ)) =
        cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / m) *
        cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / n) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [jacobiSym.mul_right, hjm, hjn, he]
    push_cast
    ring
  have h4 : ∑ a1 : Fin m, ∑ b1 : Fin n, ∑ a2 : Fin m, ∑ b2 : Fin n,
      G (n * a1 + m * b1) (n * a2 + m * b2) = oddSum m ν * oddSum n ν := by
    rw [oddSum, oddSum, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a2 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b1 _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b2 _ => h3 a1 a2 b1 b2
  rw [h1, h2, h4, hOm ν, hOn ν, jacobiSym.mul_right]
  push_cast
  ring

theorem oddGauss_one : OddGauss 1 := by
  intro ν
  simp [oddSum, jacobiSym.one_right]

/-- **`OddGauss d` for odd squarefree `d` from the odd primes.** -/
theorem oddGauss_of_prime (hP : ∀ p : ℕ, p.Prime → p ≠ 2 → OddGauss p) :
    ∀ d : ℕ, Odd d → Squarefree d → OddGauss d := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd hsq
    have hp' : p.Prime := hp
    have hk1 : k = 1 := ((Nat.squarefree_pow_iff hp'.one_lt.ne' hk.ne').mp hsq).2
    subst hk1
    rw [pow_one] at hodd ⊢
    exact hP p hp' (by rintro rfl; exact absurd hodd (by decide))
  | zero => intro h; simp at h
  | one => intro _ _; exact oddGauss_one
  | coprime a b ha hb hab iha ihb =>
    intro hodd hsq
    have hoa : Odd a := (Nat.odd_mul.mp hodd).1
    have hob : Odd b := (Nat.odd_mul.mp hodd).2
    exact oddGauss_mul hab (by omega) (by omega) (iha hoa (Squarefree.of_mul_left hsq))
      (ihb hob (Squarefree.of_mul_right hsq))

/-- **The two literature Props from three elementary statements**: the Euler product of
`L(ψ_d, s)` (`HeckeEuler`, about `ℤ[i]`), Gauss's theorem at split primes (`GaussSplit`), and the
quadratic Gauss sum over `𝔽_p²` for odd primes `p` (`OddGauss p`). -/
theorem literature_hecke_fe_of_euler_gauss_oddGaussPrime
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → GaussSplit d)
    (hP : ∀ p : ℕ, p.Prime → p ≠ 2 → OddGauss p) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_euler_gauss_oddGauss hE hS fun d h5 hsq =>
    oddGauss_of_prime hP d (Nat.odd_iff.mpr (by omega)) hsq

/-! ### `GaussSplit d` from `GaussSplit 1` (quadratic twist) -/

/-- `#{(x, y) ∈ 𝔽_p² : y² = x³ − d²x} = p + Σ_x ((x³ − d²x)/p)` for odd `p`. -/
theorem card_cd_affine_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (d : ℕ) :
    (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} : ℤ) =
      p + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  have : ∀ x : ZMod p, (∑ y : ZMod p, if y ^ 2 = x ^ 3 - (d : ZMod p) ^ 2 * x then (1 : ℤ) else 0) =
      quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) + 1 := fun x => by
    rw [← quadraticChar_card_sqrts hc, Set.toFinset_ofPred, Finset.card_filter]
    push_cast; rfl
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp [ZMod.card, add_comm]

/-- The quadratic twist: `Σ_x ((x³ − d²x)/p) = (d/p) Σ_x ((x³ − x)/p)` for `p ∤ d`. -/
theorem sum_quadraticChar_twist {p : ℕ} [Fact p.Prime] (d : ℕ) (hpd : (d : ZMod p) ≠ 0) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) =
      quadraticChar (ZMod p) d * ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft₀ (d : ZMod p) hpd)]
  refine Finset.sum_congr rfl fun t _ => ?_
  change quadraticChar (ZMod p) (((d : ZMod p) * t) ^ 3 - (d : ZMod p) ^ 2 * ((d : ZMod p) * t)) = _
  have h : ((d : ZMod p) * t) ^ 3 - (d : ZMod p) ^ 2 * ((d : ZMod p) * t) =
      (d : ZMod p) ^ 2 * ((d : ZMod p) * (t ^ 3 - t)) := by ring
  rw [h, map_mul, quadraticChar_sq_one' hpd, one_mul, map_mul]

/-- `heckeCoeff d p = (p/d) · heckeCoeff 1 p` (the factor `(N α/d)` is constant on the fiber). -/
theorem heckeCoeff_prime_twist (d p : ℕ) :
    heckeCoeff d p = (jacobiSym p d : ℂ) * heckeCoeff 1 p := by
  rw [heckeCoeff, heckeCoeff, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_normFiber.mp hq, jacobiSym.one_right]
  push_cast
  ring

/-- **`GaussSplit d` from the single curve `y² = x³ − x`** (`d ≡ 1 (mod 4)`, odd squarefree). -/
theorem gaussSplit_of_one {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) (h1 : GaussSplit 1) :
    GaussSplit d := by
  intro p hp hp4 hpd
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2d : ¬ p ∣ 2 * d := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hpd h
  have h21 : ¬ p ∣ 2 * 1 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hp.one_lt.ne' (Nat.dvd_one.mp h)
  have hpdZ : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpd
  -- `a_p(C_d) = (d/p) a_p(C_1)`
  have hcd : ZInQ.Literature.cdCoeff d p = -∑ x : ZMod p,
      quadraticChar (ZMod p) (x ^ 3 - (d : ZMod p) ^ 2 * x) := by
    rw [cdCoeff_eq_LFunction hodd hsq hp.ne_zero,
      ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card hodd hsq p h2d, card_cd_affine_eq hp2]
    ring
  have hc1 : ZInQ.Literature.cdCoeff 1 p = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) := by
    rw [cdCoeff_eq_LFunction odd_one squarefree_one hp.ne_zero]
    rw [ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card odd_one squarefree_one p h21,
      card_cd_affine_eq hp2 1]
    simp only [Nat.cast_one, one_pow, one_mul]
    ring
  have hleg : quadraticChar (ZMod p) d = jacobiSym p d := by
    have := jacobiSym.legendreSym.to_jacobiSym p d
    rw [legendreSym] at this
    push_cast at this
    rw [this, jacobiSym.quadratic_reciprocity_one_mod_four' hodd hp4]
  rw [heckeCoeff_prime_twist, ← h1 p hp hp4 (by
    intro h; exact hp.one_lt.ne' (Nat.dvd_one.mp h)), hcd, hc1,
    sum_quadraticChar_twist d hpdZ, hleg]
  push_cast
  ring

/-- **Final form**: the two literature Props from `HeckeEuler` (about `ℤ[i]`), Gauss's theorem for
the single curve `y² = x³ − x` (`GaussSplit 1`), and the quadratic Gauss sums `OddGauss p`. -/
theorem literature_hecke_fe_final
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d)
    (h1 : GaussSplit 1)
    (hP : ∀ p : ℕ, p.Prime → p ≠ 2 → OddGauss p) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_euler_gauss_oddGaussPrime hE
    (fun d h5 hsq => gaussSplit_of_one (by omega) hsq h1) hP

/-! ### `OddGauss p` for odd primes `p` (node C2'') -/

section OddGaussPrime

variable {p : ℕ} [hpp : Fact p.Prime]

/-- The quadratic character of `𝔽_p` with complex values. -/
noncomputable abbrev chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The Gauss sum `g = Σ_t χ(t) e(t/p)`. -/
noncomputable abbrev gP (p : ℕ) [Fact p.Prime] : ℂ := gaussSum (chiC p) ZMod.stdAddChar

theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

theorem chiC_ne_one (hp2 : p ≠ 2) : chiC p ≠ 1 := by
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2))

/-- `Σ_t χ(t) e(tm/p) = χ(m) g` for every `m` (including `m = 0`). -/
theorem sum_chi_psi_mul (hp2 : p ≠ 2) (m : ZMod p) :
    ∑ t : ZMod p, chiC p t * ZMod.stdAddChar (t * m) = chiC p m * gP p := by
  by_cases hm : m = 0
  · subst hm
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, zero_mul]
    exact MulChar.sum_eq_zero_of_ne_one (chiC_ne_one hp2)
  · have hu : IsUnit m := isUnit_iff_ne_zero.mpr hm
    have h := gaussSum_mulShift_eq (chiC p) ZMod.stdAddChar hu.unit
    rw [chiC_isQuadratic.inv] at h
    simp only [IsUnit.unit_spec] at h
    rw [← h, gaussSum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddChar.mulShift_apply, mul_comm m t]

theorem chiC_sq_of_ne_zero {t : ZMod p} (ht : t ≠ 0) : chiC p t ^ 2 = 1 := by
  have := quadraticChar_sq_one ht
  simp only [chiC, MulChar.ringHomComp_apply, eq_intCast]
  exact_mod_cast this

/-- `Σ_x e(tx²/p) = χ(t) g` for `t ≠ 0`. -/
theorem sum_psi_sq (hp2 : p ≠ 2) {t : ZMod p} (ht : t ≠ 0) :
    ∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2) = chiC p t * gP p := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h1 : ∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2) =
      ∑ y : ZMod p, ((quadraticChar (ZMod p) y + 1 : ℤ) : ℂ) * ZMod.stdAddChar (t * y) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)
      (fun x => ZMod.stdAddChar (t * x ^ 2))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => ZMod.stdAddChar (t * y)) (fun x hx => by
      rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul,
      ← quadraticChar_card_sqrts hc y, Set.toFinset_ofPred]
    push_cast; rfl
  rw [h1]
  simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  have h2 : ∑ y : ZMod p, ZMod.stdAddChar (t * y) = 0 := by
    have := AddChar.sum_mulShift (R := ZMod p) t (ZMod.isPrimitive_stdAddChar p)
    simp only [ht, ↓reduceIte, Nat.cast_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun y _ => by rw [mul_comm]
  rw [h2, add_zero, ← sum_chi_psi_mul hp2 t]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [chiC, MulChar.ringHomComp_apply, eq_intCast]
  rw [mul_comm t y]

/-- Completing the square: `Σ_x e((tx² + nx)/p) = e(−n²/(4t)/p) Σ_x e(tx²/p)` for `t ≠ 0`. -/
theorem sum_psi_complete_sq (hp2 : p ≠ 2) {t : ZMod p} (ht : t ≠ 0) (n : ZMod p) :
    ∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2 + n * x) =
      ZMod.stdAddChar (-(n ^ 2 / (4 * t))) * ∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_two).mp this)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  set c : ZMod p := n / (2 * t)
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.subRight c)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Equiv.subRight_apply, c]
  field_simp
  ring

theorem chiC_zero : chiC p 0 = 0 := MulChar.map_zero _

theorem chiC_inv_eq {w : ZMod p} : chiC p w⁻¹ = chiC p w := by
  by_cases hw : w = 0
  · simp [hw]
  · have h1 : chiC p w⁻¹ * chiC p w = 1 := by rw [← map_mul, inv_mul_cancel₀ hw, map_one]
    have h2 := chiC_sq_of_ne_zero hw
    calc chiC p w⁻¹ = chiC p w⁻¹ * (chiC p w) ^ 2 := by rw [h2, mul_one]
      _ = (chiC p w⁻¹ * chiC p w) * chiC p w := by ring
      _ = chiC p w := by rw [h1, one_mul]

theorem gP_sq (hp2 : p ≠ 2) : gP p ^ 2 = chiC p (-1) * p := by
  have h : gP p ^ 2 = chiC p (-1) * Fintype.card (ZMod p) :=
    gaussSum_sq (chiC_ne_one hp2) chiC_isQuadratic (ZMod.isPrimitive_stdAddChar p)
  rwa [ZMod.card] at h

theorem gP_ne_zero (hp2 : p ≠ 2) : gP p ≠ 0 := by
  intro h
  have hsq := gP_sq hp2
  rw [h, zero_pow two_ne_zero] at hsq
  have hm1 : chiC p (-1) ^ 2 = 1 := chiC_sq_of_ne_zero (neg_ne_zero.mpr one_ne_zero)
  have : chiC p (-1) * (p : ℂ) ≠ 0 := by
    refine mul_ne_zero (fun h0 => ?_) (Nat.cast_ne_zero.mpr hpp.out.ne_zero)
    rw [h0] at hm1; norm_num at hm1
  exact this hsq.symm

/-- **The two-dimensional quadratic Gauss sum over `𝔽_p`.** -/
theorem gauss2D (hp2 : p ≠ 2) (n1 n2 : ZMod p) :
    ∑ x : ZMod p, ∑ y : ZMod p, chiC p (x ^ 2 + y ^ 2) * ZMod.stdAddChar (x * n1 + y * n2) =
      p * chiC p (n1 ^ 2 + n2 ^ 2) := by
  have hg : gP p ≠ 0 := gP_ne_zero hp2
  have hχ : ∀ m : ZMod p, chiC p m =
      (gP p)⁻¹ * ∑ t : ZMod p, chiC p t * ZMod.stdAddChar (t * m) := fun m => by
    rw [sum_chi_psi_mul hp2 m]; field_simp
  -- expand and separate the variables
  have hexp : ∑ x : ZMod p, ∑ y : ZMod p, chiC p (x ^ 2 + y ^ 2) *
      ZMod.stdAddChar (x * n1 + y * n2) =
      (gP p)⁻¹ * ∑ t : ZMod p, chiC p t *
        ((∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2 + n1 * x)) *
          (∑ y : ZMod p, ZMod.stdAddChar (t * y ^ 2 + n2 * y))) := by
    calc _ = ∑ x : ZMod p, ∑ y : ZMod p, ∑ t : ZMod p, (gP p)⁻¹ * (chiC p t *
          (ZMod.stdAddChar (t * x ^ 2 + n1 * x) * ZMod.stdAddChar (t * y ^ 2 + n2 * y))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [hχ, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun t _ => ?_
          have : ZMod.stdAddChar (t * (x ^ 2 + y ^ 2)) * ZMod.stdAddChar (x * n1 + y * n2) =
              ZMod.stdAddChar (t * x ^ 2 + n1 * x) * ZMod.stdAddChar (t * y ^ 2 + n2 * y) := by
            rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
          linear_combination ((gP p)⁻¹ * chiC p t) * this
      _ = ∑ t : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p, (gP p)⁻¹ * (chiC p t *
          (ZMod.stdAddChar (t * x ^ 2 + n1 * x) * ZMod.stdAddChar (t * y ^ 2 + n2 * y))) :=
          (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
  -- evaluate the inner sums
  have hin : ∀ t : ZMod p, chiC p t * ((∑ x : ZMod p, ZMod.stdAddChar (t * x ^ 2 + n1 * x)) *
      (∑ y : ZMod p, ZMod.stdAddChar (t * y ^ 2 + n2 * y))) =
      gP p ^ 2 * (chiC p t * ZMod.stdAddChar (-((n1 ^ 2 + n2 ^ 2) / (4 * t)))) := fun t => by
    by_cases ht : t = 0
    · simp [ht]
    · rw [sum_psi_complete_sq hp2 ht, sum_psi_complete_sq hp2 ht, sum_psi_sq hp2 ht]
      have hsq : chiC p t ^ 2 = 1 := chiC_sq_of_ne_zero ht
      have hadd : ZMod.stdAddChar (-(n1 ^ 2 / (4 * t))) * ZMod.stdAddChar (-(n2 ^ 2 / (4 * t))) =
          (ZMod.stdAddChar (-((n1 ^ 2 + n2 ^ 2) / (4 * t))) : ℂ) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      linear_combination (gP p ^ 2 * chiC p t * ZMod.stdAddChar (-(n1 ^ 2 / (4 * t))) *
          ZMod.stdAddChar (-(n2 ^ 2 / (4 * t)))) * hsq + (gP p ^ 2 * chiC p t) * hadd
  -- the substitution `u = −1/(4t)`
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_two).mp this)
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hχ4 : chiC p 4 = 1 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, map_pow]; exact chiC_sq_of_ne_zero h2
  let φ : ZMod p ≃ ZMod p :=
    { toFun := fun u => -(4 * u)⁻¹
      invFun := fun u => -(4 * u)⁻¹
      left_inv := fun u => by
        simp only
        by_cases hu : u = 0
        · simp [hu]
        · field_simp
      right_inv := fun u => by
        simp only
        by_cases hu : u = 0
        · simp [hu]
        · field_simp }
  have hsub : ∑ t : ZMod p, chiC p t * ZMod.stdAddChar (-((n1 ^ 2 + n2 ^ 2) / (4 * t))) =
      chiC p (-1) * (chiC p (n1 ^ 2 + n2 ^ 2) * gP p) := by
    rw [← sum_chi_psi_mul hp2 (n1 ^ 2 + n2 ^ 2), Finset.mul_sum, ← Equiv.sum_comp φ]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = 0
    · simp [φ, hu]
    · have e1 : (φ u : ZMod p) = -(4 * u)⁻¹ := rfl
      have e2 : -((n1 ^ 2 + n2 ^ 2) / (4 * φ u)) = u * (n1 ^ 2 + n2 ^ 2) := by
        rw [e1]; field_simp
      rw [e2, e1, show -(4 * u)⁻¹ = (-1) * (4 * u)⁻¹ by ring, map_mul, chiC_inv_eq, map_mul, hχ4,
        one_mul]
      ring
  rw [hexp]
  simp_rw [hin]
  rw [← Finset.mul_sum, hsub]
  have hm1 : chiC p (-1) ^ 2 = 1 := chiC_sq_of_ne_zero (neg_ne_zero.mpr one_ne_zero)
  have hsq := gP_sq hp2
  have : (gP p)⁻¹ * (gP p ^ 2 * (chiC p (-1) * (chiC p (n1 ^ 2 + n2 ^ 2) * gP p))) =
      chiC p (-1) * gP p ^ 2 * chiC p (n1 ^ 2 + n2 ^ 2) := by
    field_simp
  rw [this, hsq]
  linear_combination (p * chiC p (n1 ^ 2 + n2 ^ 2)) * hm1

theorem jacobiSym_eq_chiC (m : ℤ) : (jacobiSym m p : ℂ) = chiC p (m : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  simp [chiC, MulChar.ringHomComp_apply]

/-- **`OddGauss p` for every odd prime `p`.** -/
theorem oddGauss_prime (hp2 : p ≠ 2) : OddGauss p := by
  intro ν
  set f : Fin p × Fin p → ZMod p × ZMod p := fun b => (((b.1 : ℕ) : ZMod p), ((b.2 : ℕ) : ZMod p))
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f, Prod.mk.injEq] at h
    have h1 := congrArg ZMod.val h.1
    have h2 := congrArg ZMod.val h.2
    rw [ZMod.val_natCast_of_lt a.2, ZMod.val_natCast_of_lt a'.2] at h1
    rw [ZMod.val_natCast_of_lt b.2, ZMod.val_natCast_of_lt b'.2] at h2
    rw [Fin.ext h1, Fin.ext h2]
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [Fintype.card_prod, ZMod.card]⟩
  have hR : chiC p ((ν.1 ^ 2 + ν.2 ^ 2 : ℤ) : ZMod p) =
      chiC p ((ν.1 : ZMod p) ^ 2 + (ν.2 : ZMod p) ^ 2) := by push_cast; rfl
  rw [oddSum, jacobiSym_eq_chiC, hR, ← gauss2D hp2, ← Fintype.sum_prod_type']
  refine Fintype.sum_bijective f hbij _ _ fun b => ?_
  simp only [f]
  rw [jacobiSym_eq_chiC]
  congr 1
  · push_cast; rfl
  · rw [show (2 * π * I * (((b.1 : ℕ) : ℂ) * ν.1 + ((b.2 : ℕ) : ℂ) * ν.2) / p : ℂ) =
        2 * π * I * ((((b.1 : ℕ) * ν.1 + (b.2 : ℕ) * ν.2 : ℤ)) : ℂ) / p by push_cast; ring,
      ← ZMod.stdAddChar_coe]
    push_cast; rfl

end OddGaussPrime

/-- **Final form**: the two literature Props from `HeckeEuler` (the Euler product of `L(ψ_d, s)`,
a statement about `ℤ[i]`) and Gauss's theorem for the single curve `y² = x³ − x`
(`GaussSplit 1`). The Fourier side (`OddGauss`) is fully proved. -/
theorem literature_hecke_fe_of_heckeEuler_gaussSplit
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d) (h1 : GaussSplit 1) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_final hE h1 fun p hp hp2 => by
    have : Fact p.Prime := ⟨hp⟩
    exact oddGauss_prime hp2

/-- **`GaussSplit 1` as a pure point count** (no L-function): for primes `p ≡ 1 (mod 4)`,
`p − #{(x, y) ∈ 𝔽_p² : y² = x³ − x} = ¼ Σ_{a² + b² = p} u(a + bi)(a + bi)`. -/
def GaussPointCount : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    (p : ℂ) - (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℂ) =
      (1 / 4) * ∑ q ∈ normFiber p, unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) * gz 0 0 q

theorem gaussSplit_one_of_pointCount (h : GaussPointCount) : GaussSplit 1 := by
  intro p hp hp4 _
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h21 : ¬ p ∣ 2 * 1 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hp.one_lt.ne' (Nat.dvd_one.mp h)
  rw [cdCoeff_eq_LFunction odd_one squarefree_one hp.ne_zero,
    ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card odd_one squarefree_one p h21]
  have hc := h p hp hp4
  simp only [Nat.cast_one, one_pow, one_mul]
  push_cast
  rw [hc, heckeCoeff]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [jacobiSym.one_right]; push_cast; ring

/-- **Final form, with Gauss's theorem as a point count.** -/
theorem literature_hecke_fe_of_heckeEuler_gaussPointCount
    (hE : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeEuler d) (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_heckeEuler_gaussSplit hE (gaussSplit_one_of_pointCount h1)

/-! ### `HeckeEuler` from multiplicativity and the prime-power recursion (node B2 split) -/

/-- Multiplicativity of `heckeCoeff d` (node B2a; unique factorization in `ℤ[i]`). -/
def HeckeMult (d : ℕ) : Prop :=
  ∀ m n : ℕ, Nat.Coprime m n → heckeCoeff d (m * n) = heckeCoeff d m * heckeCoeff d n

/-- The prime-power recursion of `heckeCoeff d` (node B2b; the elements of norm `p^k`). -/
def HeckePrimePow (d : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, heckeCoeff d (p ^ (k + 2)) =
    heckeCoeff d p * heckeCoeff d (p ^ (k + 1)) -
      (if p ∣ 2 * d then 0 else (p : ℂ)) * heckeCoeff d (p ^ k)

theorem normFiber_one : normFiber 1 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by decide

theorem heckeCoeff_one (d : ℕ) : heckeCoeff d 1 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := psi_units d
  rw [heckeCoeff_eq_sum_psi, normFiber_one]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, h4]
  norm_num

/-- Coefficients of `1 / (1 − aT + bT²)`. -/
theorem coeff_inv_quadratic (a b : ℂ) :
    let ψ := PowerSeries.invOfUnit (((1 - Polynomial.C a * Polynomial.X +
      Polynomial.C b * Polynomial.X ^ 2 : Polynomial ℂ)) : PowerSeries ℂ) 1
    PowerSeries.coeff 0 ψ = 1 ∧ PowerSeries.coeff 1 ψ = a ∧
      ∀ k : ℕ, PowerSeries.coeff (k + 2) ψ =
        a * PowerSeries.coeff (k + 1) ψ - b * PowerSeries.coeff k ψ := by
  intro ψ
  set φ : PowerSeries ℂ := ((1 - Polynomial.C a * Polynomial.X +
      Polynomial.C b * Polynomial.X ^ 2 : Polynomial ℂ) : PowerSeries ℂ) with hφdef
  have hφ : φ = 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C b * PowerSeries.X ^ 2 := by
    rw [hφdef]; push_cast; simp
  have hc0 : PowerSeries.constantCoeff φ = 1 := by
    rw [hφ]; simp
  have hmul : φ * ψ = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [hc0]; simp)
  have hexp : φ * ψ = ψ - PowerSeries.C a * (PowerSeries.X * ψ) +
      PowerSeries.C b * (PowerSeries.X ^ 2 * ψ) := by rw [hφ]; ring
  have h0 : PowerSeries.coeff 0 ψ = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]; simp
  refine ⟨h0, ?_, fun k => ?_⟩
  · have := congrArg (PowerSeries.coeff 1) (hexp.symm.trans hmul)
    rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', h0] at this
    simp at this
    linear_combination this
  · have := congrArg (PowerSeries.coeff (k + 2)) (hexp.symm.trans hmul)
    rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul'] at this
    simp at this
    linear_combination this

theorem heckeCoeff_prime_of_dvd {d p : ℕ} (hd : Odd d) (hsq : Squarefree d) (hp : p.Prime)
    (h : p ∣ 2 * d) : heckeCoeff d p = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hc : ZInQ.Literature.cdCoeff d p = 0 := by
    rw [cdCoeff_eq_LFunction hd hsq hp.ne_zero,
      ZInQ.Literature.LFunction_cd_apply_prime_of_dvd hd hsq p h]
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | hpd
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst this
    rw [← deuring_two hd hsq, hc, Int.cast_zero]
  · rw [← deuring_prime_of_dvd hd hsq hpd, hc, Int.cast_zero]

/-- **`HeckeEuler d` from multiplicativity and the prime-power recursion.** -/
theorem heckeEuler_of_mult_primePow {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (hM : HeckeMult d)
    (hP : HeckePrimePow d) : HeckeEuler d := by
  intro n hn
  rw [Nat.multiplicative_factorization (heckeCoeff d) hM (heckeCoeff_one d) hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  set b : ℂ := if p ∣ 2 * d then 0 else (p : ℂ)
  have hpoly : heckeEulerPoly d p = 1 - Polynomial.C (heckeCoeff d p) * Polynomial.X +
      Polynomial.C b * Polynomial.X ^ 2 := by
    unfold heckeEulerPoly
    by_cases h : p ∣ 2 * d
    · simp [b, h, heckeCoeff_prime_of_dvd hd hsq hpp h]
    · simp [b, h]
  rw [hpoly]
  obtain ⟨c0, c1, crec⟩ := coeff_inv_quadratic (heckeCoeff d p) b
  have key : ∀ k : ℕ, heckeCoeff d (p ^ k) = PowerSeries.coeff k (PowerSeries.invOfUnit
      (((1 - Polynomial.C (heckeCoeff d p) * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2 :
        Polynomial ℂ)) : PowerSeries ℂ) 1) ∧
      heckeCoeff d (p ^ (k + 1)) = PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit
      (((1 - Polynomial.C (heckeCoeff d p) * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2 :
        Polynomial ℂ)) : PowerSeries ℂ) 1) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [pow_zero, heckeCoeff_one, c0], by rw [zero_add, pow_one, c1]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, hP p hpp k, crec k, ← ih.1, ← ih.2]
  exact (key _).1

/-- **Final form**: the two literature Props from multiplicativity and the prime-power recursion
of `heckeCoeff` (statements about `ℤ[i]`) and Gauss's point count on `y² = x³ − x`. -/
theorem literature_hecke_fe_of_mult_primePow_gaussPointCount
    (hM : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeMult d)
    (hP : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckePrimePow d) (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_heckeEuler_gaussPointCount
    (fun d h5 hsq => heckeEuler_of_mult_primePow (Nat.odd_iff.mpr (by omega)) hsq
      (hM d h5 hsq) (hP d h5 hsq)) h1

/-! ### `HeckePrimePow` at the non-split primes -/

theorem unitOf_eq_zero_of_even {a b : ZMod 4} (h : (a.val + b.val) % 2 = 0) : unitOf (a, b) = 0 := by
  have hc : ∀ a b : ZMod 4, (a.val + b.val) % 2 = 0 →
      ¬ ((a, b) = (1, 0) ∨ (a, b) = (3, 2)) ∧ ¬ ((a, b) = (3, 0) ∨ (a, b) = (1, 2)) ∧
      ¬ ((a, b) = (0, 3) ∨ (a, b) = (2, 1)) ∧ ¬ ((a, b) = (0, 1) ∨ (a, b) = (2, 3)) := by decide
  obtain ⟨h1, h2, h3, h4⟩ := hc a b h
  simp only [unitOf, h1, h2, h3, h4, ite_false]

/-- `heckeCoeff d (2^m) = 0` for `m ≥ 1`: `(1 + i) ∣ α` when `N α` is even. -/
theorem heckeCoeff_two_pow (d : ℕ) {m : ℕ} (hm : 1 ≤ m) : heckeCoeff d (2 ^ m) = 0 := by
  rw [heckeCoeff]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  have h := mem_normFiber.mp hq
  have hev : Even (q.1 ^ 2 + q.2 ^ 2) := by
    rw [h]; push_cast
    exact (Int.even_pow.mpr ⟨even_two, by omega⟩)
  have hev2 : Even (q.1 + q.2) := by
    rw [Int.even_add] at hev ⊢
    simpa [Int.even_pow, two_ne_zero] using hev
  have hu : unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) = 0 := by
    apply unitOf_eq_zero_of_even
    have h1 := ZMod.val_intCast (n := 4) q.1
    have h2 := ZMod.val_intCast (n := 4) q.2
    obtain ⟨r, hr⟩ := hev2
    omega
  rw [hu]; ring

/-- `heckeCoeff d (p^m) = 0` for primes `p ∣ d`, `m ≥ 1`. -/
theorem heckeCoeff_pow_of_dvd {d p : ℕ} (hd : Odd d) (hp : p.Prime) (hpd : p ∣ d) {m : ℕ}
    (hm : 1 ≤ m) : heckeCoeff d (p ^ m) = 0 := by
  have : NeZero d := ⟨by rintro rfl; simp at hd⟩
  rw [heckeCoeff]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  rw [mem_normFiber.mp hq]
  have hJ : jacobiSym ((p ^ m : ℕ) : ℤ) d = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
    intro h
    have : p ∣ Nat.gcd (p ^ m) d := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpd
    rw [h] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hJ' : jacobiSym ((p : ℤ) ^ m) d = 0 := by exact_mod_cast hJ
  simp [hJ']

/-- A prime `p ≡ 3 (mod 4)` dividing `a² + b²` divides `a` and `b`. -/
theorem dvd_of_dvd_sq_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) {a b : ℤ}
    (h : (p : ℤ) ∣ a ^ 2 + b ^ 2) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((a ^ 2 + b ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  push_cast at h0
  have hb : (b : ZMod p) = 0 := by
    by_contra hb
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (a : ZMod p)) hb
      (by linear_combination h0) hp3
  have ha : (a : ZMod p) = 0 := by
    rw [hb] at h0; simpa using h0
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩

theorem normFiber_inert {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    normFiber (p ^ (k + 2)) =
      (normFiber (p ^ k)).image fun r : ℤ × ℤ => ((p : ℤ) * r.1, (p : ℤ) * r.2) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  ext q
  simp only [Finset.mem_image, mem_normFiber]
  constructor
  · intro h
    have hdvd : (p : ℤ) ∣ q.1 ^ 2 + q.2 ^ 2 := by
      rw [h]; push_cast; exact dvd_pow_self _ (by omega)
    obtain ⟨⟨r1, hr1⟩, ⟨r2, hr2⟩⟩ := dvd_of_dvd_sq_add_sq hp hp3 hdvd
    refine ⟨(r1, r2), ?_, ?_⟩
    · rw [hr1, hr2] at h
      push_cast at h
      have h2 : (p : ℤ) ^ 2 * (r1 ^ 2 + r2 ^ 2) = (p : ℤ) ^ 2 * (p : ℤ) ^ k := by
        linear_combination h
      have := mul_left_cancel₀ (pow_ne_zero 2 hp0) h2
      push_cast; exact this
    · ext <;> simp [hr1, hr2]
  · rintro ⟨r, hr, rfl⟩
    push_cast at hr ⊢
    linear_combination (p : ℤ) ^ 2 * hr

/-- **Inert primes**: `heckeCoeff d (p^(k+2)) = −p · heckeCoeff d (p^k)` for `p ≡ 3 (mod 4)`, `p ∤ d`. -/
theorem heckeCoeff_inert {d p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (hpd : ¬ p ∣ d) (k : ℕ) :
    heckeCoeff d (p ^ (k + 2)) = -(p : ℂ) * heckeCoeff d (p ^ k) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinj : Set.InjOn (fun r : ℤ × ℤ => ((p : ℤ) * r.1, (p : ℤ) * r.2))
      (normFiber (p ^ k) : Set (ℤ × ℤ)) := by
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    ext
    · exact mul_left_cancel₀ hp0 hxy.1
    · exact mul_left_cancel₀ hp0 hxy.2
  have hpsi : psi d ((p : ℤ), 0) = -(p : ℂ) := by
    have hJ : jacobiSym ((p : ℤ) ^ 2 + 0 ^ 2) d = 1 := by
      rw [zero_pow two_ne_zero, add_zero]
      apply jacobiSym.sq_one'
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
    have hu : unitOf (((p : ℤ) : ZMod 4), ((0 : ℤ) : ZMod 4)) = -1 := by
      have h3 : ((p : ℤ) : ZMod 4) = 3 := by
        rw [Int.cast_natCast, ← ZMod.natCast_mod, hp3]; rfl
      rw [h3]; simp [unitOf]; decide
    simp only [psi, hJ, hu, gz]
    push_cast; ring
  rw [heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi, normFiber_inert hp hp3,
    Finset.sum_image hinj, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hg : ((p : ℤ) * r.1, (p : ℤ) * r.2) = gmul ((p : ℤ), 0) r := by
    simp [gmul]
  rw [hg, psi_mul, hpsi]
  ring

/-- The prime-power recursion at the split primes only (`p ≡ 1 (mod 4)`, `p ∤ d`). -/
def HeckePrimePowSplit (d : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ¬ p ∣ d → ∀ k : ℕ,
    heckeCoeff d (p ^ (k + 2)) = heckeCoeff d p * heckeCoeff d (p ^ (k + 1)) -
      (p : ℂ) * heckeCoeff d (p ^ k)

theorem heckePrimePow_of_split {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (hS : HeckePrimePowSplit d) : HeckePrimePow d := by
  intro p hp k
  by_cases h2d : p ∣ 2 * d
  · simp only [h2d, ↓reduceIte, zero_mul, sub_zero]
    rw [heckeCoeff_prime_of_dvd hd hsq hp h2d, zero_mul]
    rcases (Nat.Prime.dvd_mul hp).mp h2d with h2 | hpd
    · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst this
      exact heckeCoeff_two_pow d (by omega)
    · exact heckeCoeff_pow_of_dvd hd hp hpd (by omega)
  · simp only [h2d, ↓reduceIte]
    have hpd : ¬ p ∣ d := fun h => h2d (dvd_mul_of_dvd_right h 2)
    have hp2 : p ≠ 2 := fun h => h2d (h ▸ dvd_mul_right 2 d)
    have : p % 4 = 1 ∨ p % 4 = 3 := by
      have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega
    rcases this with h1 | h3
    · exact hS p hp h1 hpd k
    · have hp0 : heckeCoeff d p = 0 := by
        rw [heckeCoeff, normFiber_eq_empty_of_mod_four_eq_three h3]; simp
      rw [heckeCoeff_inert hp h3 hpd k, hp0]
      ring

/-- **Final form**: the two literature Props from three statements: multiplicativity of
`heckeCoeff` and its recursion at split primes (both about `ℤ[i]`), and Gauss's point count. -/
theorem literature_hecke_fe_of_mult_split_gaussPointCount
    (hM : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeMult d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckePrimePowSplit d) (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_mult_primePow_gaussPointCount hM
    (fun d h5 hsq => heckePrimePow_of_split (Nat.odd_iff.mpr (by omega)) hsq (hS d h5 hsq)) h1

/-- **CR₃ (`CertifiedRankTYZClRk`) with the two textbook Props replaced by elementary statements**:
from TYZ reading A, Gross–Zagier, and the three statements about `ℤ[i]` and `𝔽_p`. With
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`
(`RouteK/RankVariants.lean`) this gives the headline without `HeckeContinuation` and
`FunctionalEquation5`. -/
theorem certifiedRankTYZClRk_of_elementary (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hG : ZInQ.Literature.GrossZagier)
    (hM : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckeMult d)
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckePrimePowSplit d) (h1 : GaussPointCount) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  obtain ⟨hC, hF⟩ := literature_hecke_fe_of_mult_split_gaussPointCount hM hS h1
  exact ZInQ.Literature.certifiedRankTYZClRk_of_literature (tyzRow5b_of_readingA_five hA hC)
    (ZInQ.Literature.rootNumberVanishing_of_functionalEquation hF) hG

/-! ### `HeckeMult`: multiplicativity of `heckeCoeff` (node B2a) -/

/-- `ℤ²` as `ℤ[i]`. -/
def toG (q : ℤ × ℤ) : GaussianInt := ⟨q.1, q.2⟩

theorem norm_toG (q : ℤ × ℤ) : (toG q).norm = q.1 ^ 2 + q.2 ^ 2 := by
  simp [toG, Zsqrtd.norm_def]; ring

theorem toG_gmul (q r : ℤ × ℤ) : toG (gmul q r) = toG q * toG r := by
  ext <;> simp [toG, gmul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

theorem toG_injective : Function.Injective toG := by
  intro x y h
  simp only [toG, Zsqrtd.mk.injEq] at h
  ext <;> simp [h.1, h.2]

theorem toG_surj (z : GaussianInt) : toG (z.re, z.im) = z := rfl

/-- Units of `ℤ[i]`: a norm-one element is `±1` or `±i`. -/
theorem norm_eq_one_cases {c : ℤ × ℤ} (h : c.1 ^ 2 + c.2 ^ 2 = 1) :
    c = (1, 0) ∨ c = (-1, 0) ∨ c = (0, 1) ∨ c = (0, -1) := by
  have h1 : c.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.2]
  have h2 : c.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.1]
  have hb1 : -1 ≤ c.1 ∧ c.1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (c.1 + 1), sq_nonneg (c.1 - 1)]
  have hb2 : -1 ≤ c.2 ∧ c.2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (c.2 + 1), sq_nonneg (c.2 - 1)]
  obtain ⟨a, b⟩ := c
  simp only at h hb1 hb2 ⊢
  have ha : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  have hb : b = -1 ∨ b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

/-- **Norm of `gcd(γ, m)`.** If `N γ = mn` with `m, n > 0` coprime, then `N(gcd(γ, m)) = m`. -/
theorem norm_gcd_eq {γ : GaussianInt} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    (hγ : γ.norm = (m * n : ℕ)) :
    (EuclideanDomain.gcd γ (m : GaussianInt)).norm = m := by
  set D := EuclideanDomain.gcd γ (m : GaussianInt)
  set E := EuclideanDomain.gcd γ (n : GaussianInt)
  have hnormdvd : ∀ {x y : GaussianInt}, x ∣ y → x.norm ∣ y.norm := fun {x y} ⟨c, hc⟩ =>
    ⟨c.norm, by rw [hc, Zsqrtd.norm_mul]⟩
  have hD1 : D.norm ∣ (m : ℤ) * m := by
    have := hnormdvd (EuclideanDomain.gcd_dvd_right γ (m : GaussianInt))
    rwa [Zsqrtd.norm_natCast] at this
  have hD2 : D.norm ∣ (m : ℤ) * n := by
    have := hnormdvd (EuclideanDomain.gcd_dvd_left γ (m : GaussianInt))
    rw [hγ] at this; exact_mod_cast this
  have hE1 : E.norm ∣ (n : ℤ) * n := by
    have := hnormdvd (EuclideanDomain.gcd_dvd_right γ (n : GaussianInt))
    rwa [Zsqrtd.norm_natCast] at this
  have hE2 : E.norm ∣ (m : ℤ) * n := by
    have := hnormdvd (EuclideanDomain.gcd_dvd_left γ (n : GaussianInt))
    rw [hγ] at this; exact_mod_cast this
  have hcop : Int.gcd (m : ℤ) n = 1 := by rw [Int.gcd_natCast_natCast]; exact hmn
  -- `N D ∣ m` and `N E ∣ n`
  have hcopZ : IsCoprime (m : ℤ) n := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hDm : D.norm ∣ (m : ℤ) :=
    ((hcopZ.mul_left hcopZ).of_isCoprime_of_dvd_left hD1).dvd_of_dvd_mul_right hD2
  have hEn : E.norm ∣ (n : ℤ) :=
    ((hcopZ.symm.mul_left hcopZ.symm).of_isCoprime_of_dvd_left hE1).dvd_of_dvd_mul_right
      (by rw [mul_comm]; exact hE2)
  -- `γ ∣ D E`
  have hγDE : γ ∣ D * E := by
    have hD := EuclideanDomain.gcd_eq_gcd_ab γ (m : GaussianInt)
    have hE := EuclideanDomain.gcd_eq_gcd_ab γ (n : GaussianInt)
    have hmn' : ((m : GaussianInt) * n) = γ * star γ := by
      rw [← Zsqrtd.norm_eq_mul_conj, hγ]; push_cast; ring
    refine ⟨EuclideanDomain.gcdA γ (m : GaussianInt) * (γ * EuclideanDomain.gcdA γ (n : GaussianInt) +
      (n : GaussianInt) * EuclideanDomain.gcdB γ (n : GaussianInt)) +
      (m : GaussianInt) * EuclideanDomain.gcdB γ (m : GaussianInt) * EuclideanDomain.gcdA γ (n : GaussianInt) +
      star γ * EuclideanDomain.gcdB γ (m : GaussianInt) * EuclideanDomain.gcdB γ (n : GaussianInt), ?_⟩
    rw [show D = _ from hD, show E = _ from hE]
    linear_combination (EuclideanDomain.gcdB γ (m : GaussianInt) *
      EuclideanDomain.gcdB γ (n : GaussianInt)) * hmn'
  have hmnDE : (m : ℤ) * n ∣ D.norm * E.norm := by
    have := hnormdvd hγDE
    rw [Zsqrtd.norm_mul, hγ] at this; exact_mod_cast this
  have hDpos : 0 ≤ D.norm := GaussianInt.norm_nonneg D
  have hEpos : 0 ≤ E.norm := GaussianInt.norm_nonneg E
  have hDle : D.norm ≤ m := Int.le_of_dvd (by exact_mod_cast hm) hDm
  have hEle : E.norm ≤ n := Int.le_of_dvd (by exact_mod_cast hn) hEn
  have hprod : D.norm * E.norm = m * n := by
    have h1 : D.norm * E.norm ∣ (m : ℤ) * n := mul_dvd_mul hDm hEn
    exact Int.dvd_antisymm (by positivity) (by positivity) h1 hmnDE
  by_contra hne
  have hlt : D.norm < m := lt_of_le_of_ne hDle hne
  have : D.norm * E.norm < (m : ℤ) * n := by
    calc D.norm * E.norm ≤ D.norm * n := mul_le_mul_of_nonneg_left hEle hDpos
      _ < m * n := mul_lt_mul_of_pos_right hlt (by exact_mod_cast hn)
  linarith

/-- The four units of `ℤ[i]` in `ℤ²`. -/
def unitsZ : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Conjugation `(a, b) ↦ (a, −b)` (the inverse on units). -/
def conjZ (e : ℤ × ℤ) : ℤ × ℤ := (e.1, -e.2)

theorem unitsZ_props {e : ℤ × ℤ} (he : e ∈ unitsZ) :
    toG e * toG (conjZ e) = 1 ∧ conjZ e ∈ unitsZ ∧ conjZ (conjZ e) = e ∧
      e.1 ^ 2 + e.2 ^ 2 = 1 := by
  simp only [unitsZ, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, by decide, by simp [conjZ], by norm_num⟩ <;>
    ext <;> simp [toG, conjZ, Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem toG_conjZ (e : ℤ × ℤ) : toG (conjZ e) = star (toG e) := by
  ext <;> simp [toG, conjZ]

/-- **The fibre of `(α, β) ↦ αβ` over `γ` has four elements.** -/
theorem card_mul_fiber {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    {y : ℤ × ℤ} (hy : y ∈ normFiber (m * n)) :
    ((normFiber m ×ˢ normFiber n).filter fun x => gmul x.1 x.2 = y).card = 4 := by
  set Y := toG y
  have hY : Y.norm = (m * n : ℕ) := by rw [norm_toG]; exact mem_normFiber.mp hy
  set D := EuclideanDomain.gcd Y (m : GaussianInt)
  have hD : D.norm = m := norm_gcd_eq hm hn hmn hY
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hD; simp at hD; omega
  have hDY : D ∣ Y := EuclideanDomain.gcd_dvd_left _ _
  set Q := Y / D
  have hYDQ : D * Q = Y := EuclideanDomain.mul_div_cancel' hD0 hDY
  have hQ : Q.norm = n := by
    have := congrArg Zsqrtd.norm hYDQ
    rw [Zsqrtd.norm_mul, hY, hD] at this
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast at this
    exact mul_left_cancel₀ hm0 this
  set α0 : ℤ × ℤ := (D.re, D.im)
  set β0 : ℤ × ℤ := (Q.re, Q.im)
  have hα0 : toG α0 = D := rfl
  have hβ0 : toG β0 = Q := rfl
  set F := fun e : ℤ × ℤ => (gmul e α0, gmul (conjZ e) β0)
  have hfib : ((normFiber m ×ˢ normFiber n).filter fun x => gmul x.1 x.2 = y) = unitsZ.image F := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_product, mem_normFiber, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hxy⟩
      set A := toG x.1
      set B := toG x.2
      have hA : A.norm = m := by rw [norm_toG]; exact ha
      have hAB : A * B = Y := by rw [← toG_gmul, hxy]
      have hAm : A ∣ (m : GaussianInt) := by
        refine ⟨star A, ?_⟩
        rw [← Zsqrtd.norm_eq_mul_conj, hA]; simp
      have hAD : A ∣ D := EuclideanDomain.dvd_gcd ⟨B, hAB.symm⟩ hAm
      obtain ⟨c, hc⟩ := hAD
      have hcn : c.norm = 1 := by
        have := congrArg Zsqrtd.norm hc
        rw [Zsqrtd.norm_mul, hA, hD] at this
        have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
        exact (mul_right_eq_self₀.mp this.symm).resolve_right hm0
      have hcU : (c.re, c.im) ∈ unitsZ := by
        have h1 : c.re ^ 2 + c.im ^ 2 = 1 := by
          have := Zsqrtd.norm_def c
          rw [hcn] at this
          linear_combination -this
        rcases norm_eq_one_cases (c := (c.re, c.im)) h1 with h | h | h | h <;>
          rw [h] <;> simp [unitsZ]
      have hcc : c * star c = 1 := by rw [← Zsqrtd.norm_eq_mul_conj, hcn]; simp
      refine ⟨conjZ (c.re, c.im), (unitsZ_props hcU).2.1, ?_⟩
      have hA' : A = D * star c := by
        calc A = A * (c * star c) := by rw [hcc, mul_one]
          _ = D * star c := by rw [hc]; ring
      have hB' : B = c * Q := by
        have h1 : D * (star c * B) = D * Q := by rw [hYDQ, ← hAB, hA']; ring
        have h2 := mul_left_cancel₀ hD0 h1
        calc B = (c * star c) * B := by rw [hcc, one_mul]
          _ = c * Q := by rw [mul_assoc, h2]
      simp only [F]
      refine Prod.ext (toG_injective ?_) (toG_injective ?_)
      · rw [toG_gmul, toG_conjZ, hα0]; exact (hA'.trans (mul_comm _ _)).symm
      · rw [toG_gmul, (unitsZ_props hcU).2.2.1, hβ0]; exact hB'.symm
    · rintro ⟨e, he, rfl⟩
      obtain ⟨hee, -, -, hen⟩ := unitsZ_props he
      have hen' : (toG e).norm = 1 := by rw [norm_toG]; exact hen
      have hcn' : (toG (conjZ e)).norm = 1 := by
        rw [toG_conjZ, Zsqrtd.norm_conj]; exact hen'
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← norm_toG, toG_gmul, Zsqrtd.norm_mul, hen', hα0, hD, one_mul]
      · rw [← norm_toG, toG_gmul, Zsqrtd.norm_mul, hcn', hβ0, hQ, one_mul]
      · apply toG_injective
        simp only [F]
        rw [toG_gmul, toG_gmul, toG_gmul, hα0, hβ0, show toG y = D * Q from hYDQ.symm]
        linear_combination (D * Q) * hee
  rw [hfib, Finset.card_image_of_injOn]
  · rfl
  · intro e1 he1 e2 he2 h
    simp only [F, Prod.mk.injEq] at h
    have h1 := congrArg toG h.1
    rw [toG_gmul, toG_gmul, hα0] at h1
    exact toG_injective (mul_right_cancel₀ hD0 h1)

theorem gmul_mem_normFiber {m n : ℕ} {a b : ℤ × ℤ} (ha : a ∈ normFiber m) (hb : b ∈ normFiber n) :
    gmul a b ∈ normFiber (m * n) := by
  rw [mem_normFiber] at ha hb ⊢
  have h := congrArg Zsqrtd.norm (toG_gmul a b)
  rw [Zsqrtd.norm_mul, norm_toG, norm_toG, norm_toG, ha, hb] at h
  rw [h]; push_cast; ring

theorem heckeCoeff_zero (d : ℕ) : heckeCoeff d 0 = 0 := by
  rw [heckeCoeff]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q hq => ?_)
  have h := mem_normFiber.mp hq
  push_cast at h
  have h1 : q.1 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])
  have h2 : q.2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])
  simp [gz, h1, h2]

/-- **`HeckeMult d` holds for every `d`.** -/
theorem heckeMult (d : ℕ) : HeckeMult d := by
  intro m n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn
    simp [heckeCoeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn
    simp [heckeCoeff_one]
  have key : 4 * ∑ y ∈ normFiber (m * n), psi d y =
      (∑ a ∈ normFiber m, psi d a) * (∑ b ∈ normFiber n, psi d b) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    simp_rw [← psi_mul]
    rw [← Finset.sum_fiberwise_of_maps_to' (s := normFiber m ×ˢ normFiber n)
      (t := normFiber (m * n)) (g := fun x : (ℤ × ℤ) × (ℤ × ℤ) => gmul x.1 x.2)
      (fun x hx => gmul_mem_normFiber (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2)
      (psi d), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.sum_const, card_mul_fiber hm hn hmn hy]
    simp
  rw [heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi]
  linear_combination (1 / 16) * key

/-- **Final form**: the two literature Props from the prime-power recursion of `heckeCoeff` at
split primes (a statement about `ℤ[i]`) and Gauss's point count on `y² = x³ − x`. -/
theorem literature_hecke_fe_of_split_gaussPointCount
    (hS : ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeckePrimePowSplit d) (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_mult_split_gaussPointCount (fun d _ _ => heckeMult d) hS h1

/-! ### `HeckePrimePowSplit` (node B2c) -/

theorem isUnit_of_norm_one {c : GaussianInt} (h : c.norm = 1) : IsUnit c :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) c).mp h

/-- An element of prime norm is a Gaussian prime. -/
theorem prime_of_norm_prime {x : GaussianInt} {p : ℕ} (hp : p.Prime) (hx : x.norm = p) :
    Prime x := by
  have hirr : Irreducible x := by
    refine ⟨fun hu => ?_, fun y z hyz => ?_⟩
    · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) x).mpr hu
      rw [hx] at this; exact hp.one_lt.ne' (by exact_mod_cast this)
    · have h := congrArg Zsqrtd.norm hyz
      rw [Zsqrtd.norm_mul, hx] at h
      have hy0 := GaussianInt.norm_nonneg y
      have hz0 := GaussianInt.norm_nonneg z
      have h' : (y.norm.toNat) * (z.norm.toNat) = p := by
        have : ((y.norm.toNat * z.norm.toNat : ℕ) : ℤ) = p := by
          push_cast; rw [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0]; exact h.symm
        exact_mod_cast this
      rw [← h'] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h1⟩
      · right; apply isUnit_of_norm_one; omega
      · left; apply isUnit_of_norm_one; omega
  exact hirr.prime

/-- `ψ_d(p) = p` for `p ≡ 1 (mod 4)`, `p ∤ d`. -/
theorem psi_split_prime {d p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hpd : ¬ p ∣ d) :
    psi d ((p : ℤ), 0) = (p : ℂ) := by
  have hJ : jacobiSym ((p : ℤ) ^ 2 + 0 ^ 2) d = 1 := by
    rw [zero_pow two_ne_zero, add_zero]
    apply jacobiSym.sq_one'
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hu : unitOf (((p : ℤ) : ZMod 4), ((0 : ℤ) : ZMod 4)) = 1 := by
    have h1 : ((p : ℤ) : ZMod 4) = 1 := by
      rw [Int.cast_natCast, ← ZMod.natCast_mod, hp1]; rfl
    rw [h1]; simp [unitOf]
  simp only [psi, hJ, hu, gz]
  push_cast; ring

open Classical in
/-- `Σ_{β ∈ A_{n}} f(zβ) = Σ_{γ ∈ A_{pn}, z ∣ γ} f(γ)` for `N z = p`. -/
theorem sum_mul_bij {z : ℤ × ℤ} {p n : ℕ} (hz : z.1 ^ 2 + z.2 ^ 2 = p) (hp : 0 < p) (f : ℤ × ℤ → ℂ) :
    ∑ β ∈ normFiber n, f (gmul z β) =
      ∑ γ ∈ (normFiber (p * n)).filter (fun γ => toG z ∣ toG γ), f γ := by
  have hz0 : toG z ≠ 0 := by
    intro h; have := congrArg Zsqrtd.norm h; rw [norm_toG, hz] at this; simp at this; omega
  refine Finset.sum_nbij' (fun β => gmul z β) (fun γ => ((toG γ / toG z).re, (toG γ / toG z).im))
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    rw [Finset.mem_filter]
    refine ⟨gmul_mem_normFiber (mem_normFiber.mpr hz) hβ, ⟨toG β, by rw [toG_gmul]⟩⟩
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨hγn, hdvd⟩ := hγ
    have hq : toG z * (toG γ / toG z) = toG γ := EuclideanDomain.mul_div_cancel' hz0 hdvd
    rw [mem_normFiber]
    have h := congrArg Zsqrtd.norm hq
    rw [Zsqrtd.norm_mul, norm_toG, norm_toG, hz, mem_normFiber.mp hγn] at h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have h2 : (toG γ / toG z).norm = n := by
      push_cast at h; exact mul_left_cancel₀ hp0 h
    rw [← h2, Zsqrtd.norm_def]; ring
  · intro β _
    apply toG_injective
    show toG ((toG (gmul z β) / toG z).re, (toG (gmul z β) / toG z).im) = toG β
    rw [toG_surj, toG_gmul, mul_div_cancel_left₀ _ hz0]
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    apply toG_injective
    rw [toG_gmul, toG_surj, EuclideanDomain.mul_div_cancel' hz0 hγ.2]
  · intro β _; rfl

theorem unit_mem_unitsZ {c : GaussianInt} (hcn : c.norm = 1) : (c.re, c.im) ∈ unitsZ := by
  have h1 : c.re ^ 2 + c.im ^ 2 = 1 := by
    have := Zsqrtd.norm_def c
    rw [hcn] at this
    linear_combination -this
  rcases norm_eq_one_cases (c := (c.re, c.im)) h1 with h | h | h | h <;> rw [h] <;> simp [unitsZ]

theorem norm_unitsZ {e : ℤ × ℤ} (he : e ∈ unitsZ) : (toG e).norm = 1 := by
  rw [norm_toG]; exact (unitsZ_props he).2.2.2

theorem psi_gmul_unit (d : ℕ) {e : ℤ × ℤ} (he : e ∈ unitsZ) (z : ℤ × ℤ) :
    psi d (gmul e z) = psi d z := by
  obtain ⟨h1, h2, h3, h4⟩ := psi_units d
  simp only [unitsZ, Finset.mem_insert, Finset.mem_singleton] at he
  rw [psi_mul]
  rcases he with rfl | rfl | rfl | rfl <;> simp [h1, h2, h3, h4]

section Split

variable {p : ℕ} {a b : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hab : a ^ 2 + b ^ 2 = p)
include hp hp1 hab

theorem split_ne : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  have hsq : ∀ c : ℕ, c ^ 2 ≠ p := by
    intro c hc
    have hdvd : c ∣ p := ⟨c, by rw [← hc]; ring⟩
    rcases hp.eq_one_or_self_of_dvd c hdvd with h | h
    · subst h; rw [one_pow] at hc; exact hp.one_lt.ne' hc.symm
    · subst h
      have : c * c = c * 1 := by nlinarith
      have := Nat.eq_of_mul_eq_mul_left hp.pos this
      exact hp.one_lt.ne' this
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h; exact hsq b (by simpa using hab)
  · subst h; exact hsq a (by simpa using hab)
  · subst h; omega

/-- `π = a + bi`. -/
def piZ (a b : ℕ) : ℤ × ℤ := ((a : ℤ), (b : ℤ))

theorem norm_piZ : (piZ a b).1 ^ 2 + (piZ a b).2 ^ 2 = p := by
  simp only [piZ]; exact_mod_cast hab

theorem norm_conj_piZ : (conjZ (piZ a b)).1 ^ 2 + (conjZ (piZ a b)).2 ^ 2 = p := by
  simp only [piZ, conjZ, neg_sq]; exact_mod_cast hab

/-- `π̄` does not divide `π` (they are not associate). -/
theorem not_conj_dvd : ¬ toG (conjZ (piZ a b)) ∣ toG (piZ a b) := by
  rintro ⟨c, hc⟩
  obtain ⟨ha0, hb0, hab'⟩ := split_ne hp hp1 hab
  have hcn : c.norm = 1 := by
    have h := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul, norm_toG, norm_toG, norm_piZ hp hp1 hab, norm_conj_piZ hp hp1 hab] at h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact ((mul_right_eq_self₀.mp h.symm).resolve_right hp0)
  have hcU := unit_mem_unitsZ hcn
  have hre := congrArg Zsqrtd.re hc
  have him := congrArg Zsqrtd.im hc
  simp only [toG, piZ, conjZ, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
  simp only [unitsZ, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcU
  rcases hcU with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hre him <;>
    simp at hre him <;> omega

theorem prime_piZ : Prime (toG (piZ a b)) :=
  prime_of_norm_prime hp (by rw [norm_toG]; exact norm_piZ hp hp1 hab)

theorem prime_conj_piZ : Prime (toG (conjZ (piZ a b))) :=
  prime_of_norm_prime hp (by rw [norm_toG]; exact norm_conj_piZ hp hp1 hab)

theorem p_eq_mul : (p : GaussianInt) = toG (piZ a b) * toG (conjZ (piZ a b)) := by
  rw [toG_conjZ, ← Zsqrtd.norm_eq_mul_conj, norm_toG, norm_piZ hp hp1 hab]; simp

/-- Every `γ` with `p ∣ N γ` is divisible by `π` or `π̄`; by both iff `p ∣ γ`. -/
theorem split_dvd {γ : GaussianInt} (hγ : (p : ℤ) ∣ γ.norm) :
    (toG (piZ a b) ∣ γ ∨ toG (conjZ (piZ a b)) ∣ γ) ∧
      (toG (piZ a b) ∣ γ ∧ toG (conjZ (piZ a b)) ∣ γ ↔ (p : GaussianInt) ∣ γ) := by
  have hπ := prime_piZ hp hp1 hab
  have hπ' := prime_conj_piZ hp hp1 hab
  have hP := p_eq_mul hp hp1 hab
  refine ⟨?_, ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩⟩
  · have h1 : toG (piZ a b) ∣ γ * star γ := by
      rw [← Zsqrtd.norm_eq_mul_conj]
      obtain ⟨k, hk⟩ := hγ
      rw [hk]; push_cast
      exact dvd_mul_of_dvd_left (hP ▸ dvd_mul_right _ _) _
    rcases hπ.dvd_or_dvd h1 with h | h
    · exact Or.inl h
    · right
      have := map_dvd (starRingEnd GaussianInt) h
      simpa [toG_conjZ, starRingEnd_apply, star_star] using this
  · obtain ⟨g1, hg1⟩ := h1
    have : toG (conjZ (piZ a b)) ∣ toG (piZ a b) * g1 := hg1 ▸ h2
    rcases hπ'.dvd_or_dvd this with h | h
    · exact absurd h (not_conj_dvd hp hp1 hab)
    · obtain ⟨g2, hg2⟩ := h
      exact ⟨g2, by rw [hg1, hg2, hP]; ring⟩
  · exact ⟨dvd_trans ⟨_, hP⟩ h, dvd_trans ⟨_, by rw [hP, mul_comm]⟩ h⟩

open Classical in
/-- `A_p = U·π ⊔ U·π̄`, as a sum. -/
theorem sum_normFiber_prime (f : ℤ × ℤ → ℂ) :
    ∑ x ∈ normFiber p, f x = ∑ e ∈ unitsZ, f (gmul e (piZ a b)) +
      ∑ e ∈ unitsZ, f (gmul e (conjZ (piZ a b))) := by
  have hπ0 : toG (piZ a b) ≠ 0 := (prime_piZ hp hp1 hab).ne_zero
  have hπ'0 : toG (conjZ (piZ a b)) ≠ 0 := (prime_conj_piZ hp hp1 hab).ne_zero
  have hP := p_eq_mul hp hp1 hab
  have hinj : ∀ z : ℤ × ℤ, toG z ≠ 0 → Set.InjOn (fun e => gmul e z) (unitsZ : Set (ℤ × ℤ)) :=
    fun z hz e1 _ e2 _ h => toG_injective (mul_right_cancel₀ hz (by
      have := congrArg toG h; simpa [toG_gmul] using this))
  have hset : normFiber p = unitsZ.image (fun e => gmul e (piZ a b)) ∪
      unitsZ.image (fun e => gmul e (conjZ (piZ a b))) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, mem_normFiber]
    constructor
    · intro hx
      have hX : (toG x).norm = p := by rw [norm_toG]; exact hx
      have hXp : Prime (toG x) := prime_of_norm_prime hp hX
      have hXdvd : toG x ∣ toG (piZ a b) * toG (conjZ (piZ a b)) := by
        rw [← hP]
        exact ⟨star (toG x), by rw [← Zsqrtd.norm_eq_mul_conj, hX]; simp⟩
      have key : ∀ z : ℤ × ℤ, (toG z).norm = p → toG x ∣ toG z →
          ∃ e ∈ unitsZ, gmul e z = x := by
        intro z hz ⟨c, hc⟩
        have hcn : c.norm = 1 := by
          have h := congrArg Zsqrtd.norm hc
          rw [Zsqrtd.norm_mul, hz, hX] at h
          have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
          exact (mul_right_eq_self₀.mp h.symm).resolve_right hp0
        have hcU := unit_mem_unitsZ hcn
        have hcc : c * star c = 1 := by rw [← Zsqrtd.norm_eq_mul_conj, hcn]; simp
        refine ⟨conjZ (c.re, c.im), (unitsZ_props hcU).2.1, toG_injective ?_⟩
        rw [toG_gmul, toG_conjZ, toG_surj, hc]
        calc star c * (toG x * c) = toG x * (c * star c) := by ring
          _ = toG x := by rw [hcc, mul_one]
      rcases hXp.dvd_or_dvd hXdvd with h | h
      · exact Or.inl (key _ (by rw [norm_toG]; exact norm_piZ hp hp1 hab) h)
      · exact Or.inr (key _ (by rw [norm_toG]; exact norm_conj_piZ hp hp1 hab) h)
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · rw [← norm_toG, toG_gmul, Zsqrtd.norm_mul, norm_unitsZ he, one_mul, norm_toG,
          norm_piZ hp hp1 hab]
      · rw [← norm_toG, toG_gmul, Zsqrtd.norm_mul, norm_unitsZ he, one_mul, norm_toG,
          norm_conj_piZ hp hp1 hab]
  have hdisj : Disjoint (unitsZ.image (fun e => gmul e (piZ a b)))
      (unitsZ.image (fun e => gmul e (conjZ (piZ a b)))) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨e1, he1, rfl⟩ := hx1
    obtain ⟨e2, he2, h2⟩ := hx2
    apply not_conj_dvd hp hp1 hab
    have h := congrArg toG h2
    rw [toG_gmul, toG_gmul] at h
    refine ⟨toG e2 * toG (conjZ e1), ?_⟩
    have hee := (unitsZ_props he1).1
    calc toG (piZ a b) = (toG e1 * toG (conjZ e1)) * toG (piZ a b) := by rw [hee, one_mul]
      _ = toG (conjZ e1) * (toG e1 * toG (piZ a b)) := by ring
      _ = toG (conjZ e1) * (toG e2 * toG (conjZ (piZ a b))) := by rw [h]
      _ = _ := by ring
  rw [hset, Finset.sum_union hdisj, Finset.sum_image (hinj _ hπ0), Finset.sum_image (hinj _ hπ'0)]

end Split

theorem card_unitsZ : unitsZ.card = 4 := by decide

open Classical in
/-- **`HeckePrimePowSplit d` holds for every `d`** (the Hecke relation at split primes). -/
theorem heckePrimePowSplit (d : ℕ) : HeckePrimePowSplit d := by
  intro p hp hp1 hpd k
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hpos : 0 < p := hp.pos
  -- the sum over `A_p`
  have hsplit : ∑ x ∈ normFiber p, psi d x = 4 * psi d (piZ a b) + 4 * psi d (conjZ (piZ a b)) := by
    rw [sum_normFiber_prime hp hp1 hab,
      Finset.sum_congr rfl fun e he => psi_gmul_unit d he (piZ a b),
      Finset.sum_congr rfl fun e he => psi_gmul_unit d he (conjZ (piZ a b)),
      Finset.sum_const, Finset.sum_const, card_unitsZ]
    simp
  -- multiplying by `π` and `π̄`
  have he1 : p * p ^ (k + 1) = p ^ (k + 2) := by ring
  have he2 : p ^ 2 * p ^ k = p ^ (k + 2) := by ring
  have hbij1 := sum_mul_bij (n := p ^ (k + 1)) (norm_piZ hp hp1 hab) hpos (psi d)
  have hbij2 := sum_mul_bij (n := p ^ (k + 1)) (norm_conj_piZ hp hp1 hab) hpos (psi d)
  rw [he1] at hbij1 hbij2
  have hpz : ((p : ℤ), (0 : ℤ)).1 ^ 2 + ((p : ℤ), (0 : ℤ)).2 ^ 2 = ((p ^ 2 : ℕ) : ℤ) := by
    push_cast; ring
  have hbij3 := sum_mul_bij (n := p ^ k) hpz (by positivity) (psi d)
  rw [he2] at hbij3
  have htoGp : toG ((p : ℤ), 0) = (p : GaussianInt) := by
    ext <;> simp [toG]
  -- inclusion–exclusion over `A_{p^{k+2}}`
  have hincl : (∑ γ ∈ (normFiber (p ^ (k + 2))).filter (fun γ => toG (piZ a b) ∣ toG γ), psi d γ) +
      (∑ γ ∈ (normFiber (p ^ (k + 2))).filter
        (fun γ => toG (conjZ (piZ a b)) ∣ toG γ), psi d γ) =
      (∑ γ ∈ normFiber (p ^ (k + 2)), psi d γ) +
      ∑ γ ∈ (normFiber (p ^ (k + 2))).filter (fun γ => toG ((p : ℤ), 0) ∣ toG γ), psi d γ := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hN : (p : ℤ) ∣ (toG γ).norm := by
      rw [norm_toG, mem_normFiber.mp hγ]; push_cast
      exact dvd_pow_self _ (by omega)
    obtain ⟨hor, hand⟩ := split_dvd hp hp1 hab hN
    rw [htoGp]
    by_cases h1 : toG (piZ a b) ∣ toG γ <;> by_cases h2 : toG (conjZ (piZ a b)) ∣ toG γ
    · rw [if_pos h1, if_pos h2, if_pos (hand.mp ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (hand.mpr h).2)]
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 (hand.mpr h).1)]; ring
    · exact absurd hor (by tauto)
  have hpsi_p : ∀ δ : ℤ × ℤ, psi d (gmul ((p : ℤ), 0) δ) = p * psi d δ := fun δ => by
    rw [psi_mul, psi_split_prime hp hp1 hpd]
  -- assemble
  have key : (∑ x ∈ normFiber p, psi d x) * (∑ β ∈ normFiber (p ^ (k + 1)), psi d β) =
      4 * ((∑ γ ∈ normFiber (p ^ (k + 2)), psi d γ) + p * ∑ δ ∈ normFiber (p ^ k), psi d δ) := by
    have hA : ∀ z : ℤ × ℤ, psi d z * (∑ β ∈ normFiber (p ^ (k + 1)), psi d β) =
        ∑ β ∈ normFiber (p ^ (k + 1)), psi d (gmul z β) := fun z => by
      rw [Finset.mul_sum]; simp_rw [psi_mul]
    have hB : ∑ δ ∈ normFiber (p ^ k), psi d (gmul ((p : ℤ), 0) δ) =
        p * ∑ δ ∈ normFiber (p ^ k), psi d δ := by
      simp_rw [hpsi_p]; rw [Finset.mul_sum]
    rw [hsplit]
    have := hA (piZ a b)
    have := hA (conjZ (piZ a b))
    linear_combination 4 * hA (piZ a b) + 4 * hA (conjZ (piZ a b)) + 4 * hbij1 + 4 * hbij2 +
      4 * hincl - 4 * hbij3 + 4 * hB
  rw [heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi, heckeCoeff_eq_sum_psi]
  linear_combination (-(1 : ℂ) / 16) * key

/-- **Final form**: the two literature Props from Gauss's point count on `y² = x³ − x` alone. -/
theorem literature_hecke_fe_of_gaussPointCount (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_split_gaussPointCount (fun d _ _ => heckePrimePowSplit d) h1

/-- **The Euler product of `L(ψ_d, s)`**, for odd squarefree `d`. -/
theorem heckeEuler_of_odd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : HeckeEuler d :=
  heckeEuler_of_mult_primePow hd hsq (heckeMult d)
    (heckePrimePow_of_split hd hsq (heckePrimePowSplit d))

/-- **Deuring's identity `L(C_d, s) = L(ψ_d, s)` from Gauss's point count**, for squarefree
`d ≡ 1 (mod 4)`. -/
theorem deuringCd_of_gaussPointCount {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d)
    (h1 : GaussPointCount) : DeuringCd d :=
  deuringCd_of_heckeEuler_gaussSplit (Nat.odd_iff.mpr (by omega)) hsq
    (heckeEuler_of_odd (Nat.odd_iff.mpr (by omega)) hsq)
    (gaussSplit_of_one hd4 hsq (gaussSplit_one_of_pointCount h1))

end BpHeckeFE
