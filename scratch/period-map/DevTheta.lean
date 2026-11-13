import PMLightBase

/-! ## period-map: `HauptmodulUnique` and `QMDenZeroCM3` from strictly smaller named Props

Task period-map, 2026-11-13. Statements above are verbatim copies; nothing above is changed.

* `hauptmodulUnique_of : ThetaOmegaAnalytic → S8Nonzero → SphereFactorAffine → HauptmodulUnique`.
  Proved here: `QMHauptmodul`'s `f` is holomorphic into `P¹(ℂ)` (`isHolP1At_of_hauptFn`, removable
  singularities and the identity theorem), the three CM points exist (`cm4_exists`, `cm3_exists`,
  `cm24_exists`: explicit `x ∈ 𝒪` and fixed points `√2 + i`, `i√3`, `i√(9+6√2)`), and an affine map
  fixing `0` and `−16/27` is the identity.
* `qmDenZeroCM3_of : ThetaOmegaAnalytic → S8Nonzero → S8Weight8 → S8OrderCM3 →
  ValenceBoundGammaStar → QMDenZeroCM3`. Proved here: `ι` is multiplicative (`iota_mul`), `Γ*` is
  closed under inverses, a point `Γ*`-equivalent to `i√3` is a fixed point of some `ι(x')`,
  `x' ∈ 𝒪`, `x'² − x' + 1 = 0` (conjugation by the normalizer), and the counting argument. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply ofComplex_apply_of_im_pos num denom denom_ne_zero)
open HSyn.G0Split.FibreQM

/-- The open upper half-plane as a subset of `ℂ`. -/
def U : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_U : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected

/-! ### Named Props (glue) shared by both reductions -/

/-- **GLUE (holomorphy of the theta constants along the modular embedding).** `Σ_{m even} θ_m⁸ ∘ Ω`
and `∏_{m even} θ_m² ∘ Ω` are holomorphic on the upper half-plane.

Why true: each `θ_m` is a holomorphic function on the Siegel upper half-space `𝔥₂` (the series
converges normally on the compact subsets of `𝔥₂`: `|exp(πi vᵀΩv)| = exp(−π vᵀ(Im Ω)v)`; Igusa,
*Theta functions*, 1972, Ch. I, or Mumford, *Tata lectures on theta I*, §II.1, UNVERIFIED locators);
`Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` is a rational function of `τ` whose denominator
`det F₀(τ) ∝ (τ − 3)(τ + 1)` (`QMLattice.det_Fp`) does not vanish on `ℍ`, and `Ω(ℍ) ⊆ 𝔥₂`
(pkg-I1 §4, VERIFIED numerically there). Size: small-medium (Mathlib has the one-variable
`jacobiTheta₂` analyticity proof to imitate: `differentiableOn_tsum_of_summable_norm`). -/
def ThetaOmegaAnalytic : Prop :=
  AnalyticOnNhd ℂ (fun z => PkgI1.thetaSum8 (PkgI1.Omega z)) U ∧
    AnalyticOnNhd ℂ (fun z => PkgI1.thetaProd2 (PkgI1.Omega z)) U

/-- **GLUE (a numerical value).** `Σ_{m even} θ_m⁸(Ω(√2 + i)) ≠ 0`. Numerically
`Σθ_m⁸(Ω(√2 + i)) = −33.9079295761…` (VERIFIED: `py/al_weight.py`, mpmath 40 digits, theta series
truncated at `|n_k| ≤ 12`). A certified bound on the tail of the theta series would prove it.
Size: small. -/
def S8Nonzero : Prop := PkgI1.thetaSum8 (PkgI1.Omega ((√2 : ℂ) + Complex.I)) ≠ 0

theorem mem_U_s2I : ((√2 : ℂ) + Complex.I) ∈ U := by simp [U]

theorem jNum_analytic (hT : ThetaOmegaAnalytic) :
    AnalyticOnNhd ℂ (fun z => PkgI1.jNum (PkgI1.Omega z)) U :=
  fun z hz => analyticAt_const.mul ((hT.2 z hz).pow 2)

theorem jDen_analytic (hT : ThetaOmegaAnalytic) :
    AnalyticOnNhd ℂ (fun z => PkgI1.jDen (PkgI1.Omega z)) U :=
  fun z hz => (hT.1 z hz).pow 5

/-! ### `QMHauptmodul`'s `f` is holomorphic into `P¹(ℂ)` (proved) -/

theorem isHolP1At_of_hauptFn (hT : ThetaOmegaAnalytic) (hS : S8Nonzero)
    {f : UpperHalfPlane → OnePoint ℂ} (hf : QMHauptmodulFn f) (τ : UpperHalfPlane) :
    IsHolP1At f τ := by
  classical
  set N : ℂ → ℂ := fun z => PkgI1.jNum (PkgI1.Omega z) with hNdef
  set D : ℂ → ℂ := fun z => PkgI1.jDen (PkgI1.Omega z) with hDdef
  have hN : AnalyticOnNhd ℂ N U := jNum_analytic hT
  have hD : AnalyticOnNhd ℂ D U := jDen_analytic hT
  have hτU : (τ : ℂ) ∈ U := τ.im_pos
  have hUn : U ∈ 𝓝 (τ : ℂ) := isOpen_U.mem_nhds hτU
  have hfval : ∀ z (hz : 0 < z.im), D z ≠ 0 → f ⟨z, hz⟩ = ((N z / D z : ℂ) : OnePoint ℂ) :=
    fun z hz h => hf.2.1 ⟨z, hz⟩ h
  -- `D` has no zeros in a punctured neighbourhood of `τ` (identity theorem)
  have hDev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), D z ≠ 0 := by
    rcases (hD τ hτU).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have h0 := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_U hτU h
      apply hS
      have := h0 mem_U_s2I
      simpa [D, PkgI1.jDen] using this
    · exact h
  -- `f ∘ ofComplex` is continuous at `τ`
  have hFc : Tendsto (fun z : ℂ => f (ofComplex z)) (𝓝 (τ : ℂ)) (𝓝 (f τ)) := by
    rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, tendsto_map'_iff]
    simp only [Function.comp_def, ofComplex_apply]
    exact hf.1.tendsto τ
  have hF_eq : ∀ᶠ z in 𝓝[≠] (τ : ℂ), f (ofComplex z : UpperHalfPlane) = ((N z / D z : ℂ) : OnePoint ℂ) := by
    filter_upwards [hDev, nhdsWithin_le_nhds hUn] with z hz hzU
    rw [ofComplex_apply_of_im_pos hzU]
    exact hfval z hzU hz
  have hlim : Tendsto (fun z => ((N z / D z : ℂ) : OnePoint ℂ)) (𝓝[≠] (τ : ℂ)) (𝓝 (f τ)) :=
    Tendsto.congr' hF_eq (hFc.mono_left nhdsWithin_le_nhds)
  have hevU : ∀ᶠ z in 𝓝 (τ : ℂ), z ≠ (τ : ℂ) → D z ≠ 0 := eventually_nhdsWithin_iff.mp hDev
  have hτeq : ∀ z (hz : 0 < z.im), z = (τ : ℂ) → (⟨z, hz⟩ : UpperHalfPlane) = τ :=
    fun z hz h => UpperHalfPlane.ext h
  by_cases hinf : f τ = OnePoint.infty
  · -- a pole: `1/f = D/N` extends analytically by `0`
    right
    rw [hinf] at hlim
    have hq : Tendsto (fun z => N z / D z) (𝓝[≠] (τ : ℂ)) (Bornology.cobounded ℂ) := by
      have := (tendsto_comap_iff (g := ((↑) : ℂ → OnePoint ℂ)) (f := fun z => N z / D z)).mpr hlim
      rwa [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact,
        ← Metric.cobounded_eq_cocompact] at this
    have hinv : Tendsto (fun z => (N z / D z)⁻¹) (𝓝[≠] (τ : ℂ)) (𝓝 0) :=
      tendsto_inv₀_cobounded.comp hq
    have hne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), N z / D z ≠ 0 := by
      have h1 : ∀ᶠ w in Bornology.cobounded ℂ, w ≠ 0 := by
        have := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually (eventually_gt_atTop 0)
        filter_upwards [this] with w hw
        exact norm_pos_iff.mp hw
      exact hq.eventually h1
    set g : ℂ → ℂ := Function.update (fun z => (N z / D z)⁻¹) (τ : ℂ) 0 with hg
    have hgτ : g τ = 0 := by simp [g]
    have hgc : ContinuousAt g (τ : ℂ) := by
      rw [hg, continuousAt_update_same]
      exact hinv
    have hgd : ∀ᶠ z in 𝓝[≠] (τ : ℂ), DifferentiableAt ℂ g z := by
      filter_upwards [hDev, hne, nhdsWithin_le_nhds hUn, self_mem_nhdsWithin] with z hDz hqz hzU hzτ
      have hd : DifferentiableAt ℂ (fun z => (N z / D z)⁻¹) z :=
        ((hN z hzU).differentiableAt.div (hD z hzU).differentiableAt hDz).inv hqz
      exact hd.congr_of_eventuallyEq
        ((eventually_ne_nhds hzτ).mono fun w hw => Function.update_of_ne hw _ _)
    have hga : AnalyticAt ℂ g (τ : ℂ) :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
    refine ⟨g, hga, hgτ, ?_⟩
    filter_upwards [hevU, eventually_nhdsWithin_iff.mp hne] with z hz1 hz2
    intro hz
    by_cases hzτ : z = τ
    · rw [hτeq z hz hzτ, hinf, hzτ, hgτ, if_pos rfl]
    · have hgz : g z = (N z / D z)⁻¹ := Function.update_of_ne hzτ _ _
      rw [hgz, if_neg (inv_ne_zero (hz2 hzτ)), inv_inv]
      exact hfval z hz (hz1 hzτ)
  · -- a finite value: `f = N/D` extends analytically
    left
    obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← hc] at hlim
    have hq : Tendsto (fun z => N z / D z) (𝓝[≠] (τ : ℂ)) (𝓝 c) :=
      (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).mpr hlim
    set g : ℂ → ℂ := Function.update (fun z => N z / D z) (τ : ℂ) c with hg
    have hgτ : g τ = c := by simp [g]
    have hgc : ContinuousAt g (τ : ℂ) := by
      rw [hg, continuousAt_update_same]
      exact hq
    have hgd : ∀ᶠ z in 𝓝[≠] (τ : ℂ), DifferentiableAt ℂ g z := by
      filter_upwards [hDev, nhdsWithin_le_nhds hUn, self_mem_nhdsWithin] with z hDz hzU hzτ
      have hd : DifferentiableAt ℂ (fun z => N z / D z) z :=
        (hN z hzU).differentiableAt.div (hD z hzU).differentiableAt hDz
      exact hd.congr_of_eventuallyEq
        ((eventually_ne_nhds hzτ).mono fun w hw => Function.update_of_ne hw _ _)
    have hga : AnalyticAt ℂ g (τ : ℂ) :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
    refine ⟨g, hga, ?_⟩
    filter_upwards [hevU] with z hz1
    intro hz
    by_cases hzτ : z = τ
    · rw [hτeq z hz hzτ, ← hc, hzτ, hgτ]
    · have hgz : g z = N z / D z := Function.update_of_ne hzτ _ _
      rw [hgz]
      exact hfval z hz (hz1 hzτ)

/-! ### The three CM points (proved) -/

/-- A fixed-point criterion for `g ∈ GL₂(ℝ)` of positive determinant. -/
theorem smul_eq_self_of {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (τ : UpperHalfPlane)
    (h : ((g 1 0 : ℝ) : ℂ) * (τ : ℂ) ^ 2 + (((g 1 1 : ℝ) : ℂ) - (g 0 0 : ℝ)) * τ
      - (g 0 1 : ℝ) = 0) : g • τ = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg), div_eq_iff (denom_ne_zero g τ)]
  simp only [num, denom]
  linear_combination -h

theorem sqrt2_sq : (√2 : ℂ) * √2 = 2 := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `x = i + j`, `x² = −1`. -/
def x4 : PkgI1.B := ⟨0, 1, 1, 0⟩
/-- `x = (1 + j)/2`, `x² − x + 1 = 0`. -/
def x3 : PkgI1.B := ⟨1/2, 0, 1/2, 0⟩
/-- `x = 2j + ij = μ`, `x² = −6`. -/
def x24 : PkgI1.B := ⟨0, 0, 2, 1⟩

theorem inO_x4 : PkgI1.InO x4 :=
  ⟨![-1, 1, 2, 0], by ext <;> simp [x4, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩
theorem inO_x3 : PkgI1.InO x3 :=
  ⟨![0, 0, 1, 0], by ext <;> simp [x3, PkgI1.oBasis, Fin.sum_univ_four]⟩
theorem inO_x24 : PkgI1.InO x24 :=
  ⟨![-2, -1, 4, 2], by ext <;> simp [x24, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

theorem x4_sq : x4 * x4 = -1 := by ext <;> simp [x4] <;> norm_num
theorem x3_sq : x3 * x3 - x3 + 1 = 0 := by ext <;> simp [x3] <;> norm_num
theorem x24_sq : x24 * x24 = -6 := by
  ext <;> simp [x24, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_iota (x : PkgI1.B) : (PkgI1.iota x).det =
    (x.re : ℝ) ^ 2 - 2 * (x.imI : ℝ) ^ 2 + 3 * (x.imJ : ℝ) ^ 2 - 6 * (x.imK : ℝ) ^ 2 := by
  rw [iota_apply, Matrix.det_fin_two_of]
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

/-- The element of `GL₂(ℝ)` given by `ι(x)` when `nrd(x) ≠ 0`. -/
def glOf (x : PkgI1.B) (h : (PkgI1.iota x).det ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota x) h

theorem coe_glOf (x : PkgI1.B) (h : (PkgI1.iota x).det ≠ 0) :
    (glOf x h : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl

theorem det_x4 : (PkgI1.iota x4).det = 1 := by rw [det_iota]; simp [x4]; norm_num
theorem det_x3 : (PkgI1.iota x3).det = 1 := by rw [det_iota]; simp [x3]; norm_num
theorem det_x24 : (PkgI1.iota x24).det = 6 := by rw [det_iota]; simp [x24]; norm_num

/-- `√2 + i`. -/
def tau4 : UpperHalfPlane := ⟨(√2 : ℂ) + Complex.I, by simp⟩
/-- `i√3`. -/
def tau3 : UpperHalfPlane := ⟨(√3 : ℂ) * Complex.I, by simp⟩
/-- `i√(9 + 6√2)`. -/
def tau24 : UpperHalfPlane := ⟨(√(9 + 6 * √2) : ℂ) * Complex.I, by
  simp only [mul_im, ofReal_re, Complex.I_im, mul_one, ofReal_im, Complex.I_re, mul_zero, add_zero]
  positivity⟩

theorem cm4_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x = -1 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ := by
  refine ⟨x4, inO_x4, x4_sq, glOf x4 (by rw [det_x4]; norm_num), rfl, tau4, ?_⟩
  apply smul_eq_self_of (by rw [coe_glOf, det_x4]; norm_num)
  simp only [coe_glOf, iota_apply, x4, tau4]
  simp
  linear_combination (-1 : ℂ) * sqrt2_sq + Complex.I_sq

theorem cm3_tau3 : glOf x3 (by rw [det_x3]; norm_num) • tau3 = tau3 := by
  apply smul_eq_self_of (by rw [coe_glOf, det_x3]; norm_num)
  simp only [coe_glOf, iota_apply, x3, tau3]
  simp
  have h3 : (√3 : ℂ) * √3 = 3 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  linear_combination (-(1 : ℂ) / 2) * h3 + (1 / 2 : ℂ) * (√3 : ℂ) ^ 2 * Complex.I_sq

theorem cm3_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ :=
  ⟨x3, inO_x3, x3_sq, _, rfl, tau3, cm3_tau3⟩

theorem cm24_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x = -6 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ := by
  refine ⟨x24, inO_x24, x24_sq, glOf x24 (by rw [det_x24]; norm_num), rfl, tau24, ?_⟩
  apply smul_eq_self_of (by rw [coe_glOf, det_x24]; norm_num)
  simp only [coe_glOf, iota_apply, x24, tau24]
  simp
  have h0 : (0 : ℝ) ≤ 9 + 6 * √2 := by positivity
  have h1 : (√(9 + 6 * √2) : ℂ) * √(9 + 6 * √2) = 9 + 6 * √2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt h0]; push_cast; ring
  linear_combination (-(2 : ℂ) + √2) * h1 + (6 : ℂ) * sqrt2_sq
    + (2 - (√2 : ℂ)) * (√(9 + 6 * √2) : ℂ) ^ 2 * Complex.I_sq

/-! ### `HauptmodulUnique` -/

/-- **TEXTBOOK (complex analysis on the Riemann sphere; GLUE as a combination).** Let
`f, h : ℍ → P¹(ℂ)` be holomorphic into `P¹(ℂ)` (`IsHolP1At` at every point), `f` surjective, with
the same fibres, and with a common point mapped to `∞` by both. Then `h = A ∘ f` for an affine map
`A(z) = az + b`, `a ≠ 0`.

Why true (textbook): `φ(f(τ)) := h(τ)` is a well-defined injection `P¹ → P¹` (same fibres, `f`
onto) with `φ(∞) = ∞`. It is holomorphic at every point `f(τ₀)`: in charts `f` is `w ↦ w^m`
near `τ₀` (`f` is not locally constant: a surjective holomorphic map on the connected `ℍ`), and
`h = φ ∘ f` is holomorphic and invariant under `w ↦ ζw` (`ζ^m = 1`), hence a holomorphic function
of `w^m` (Ahlfors, *Complex Analysis*, Ch. 4, §3.3 local mapping; UNVERIFIED locator). An injective
holomorphic `φ : P¹ → P¹` with `φ(∞) = ∞` restricts to an injective entire function with a pole at
`∞`, i.e. a polynomial of degree one (Ahlfors Ch. 4 §3.2 Casorati–Weierstrass, or Conway, *Functions
of One Complex Variable*, Ch. V, UNVERIFIED locators). Size: medium (local normal form of a
holomorphic map, removable singularities on `P¹`, injective polynomials have degree one). -/
def SphereFactorAffine : Prop :=
  ∀ f h : UpperHalfPlane → OnePoint ℂ, (∀ τ, IsHolP1At f τ) → (∀ τ, IsHolP1At h τ) →
    Function.Surjective f → (∀ τ τ', f τ = f τ' ↔ h τ = h τ') →
    (∃ τ, f τ = OnePoint.infty ∧ h τ = OnePoint.infty) →
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ τ, h τ = OnePoint.map (fun z => a * z + b) (f τ)

/-- **`HauptmodulUnique` from strictly smaller named Props (proved).** -/
theorem hauptmodulUnique_of (hT : ThetaOmegaAnalytic) (hS : S8Nonzero)
    (hSF : SphereFactorAffine) : HauptmodulUnique := by
  intro f h hf hh
  have hfib : ∀ τ τ', f τ = f τ' ↔ h τ = h τ' :=
    fun τ τ' => (hf.2.2.1 τ τ').trans (hh.2.2.1 τ τ').symm
  obtain ⟨y3, hy3O, hy3, g3, hg3, τ3, hτ3⟩ := cm3_exists
  obtain ⟨a, b, ha, hab⟩ := hSF f h (isHolP1At_of_hauptFn hT hS hf) hh.2.1 hf.2.2.2.1 hfib
    ⟨τ3, hf.2.2.2.2.2.1 y3 hy3O hy3 g3 hg3 τ3 hτ3, hh.2.2.2.2.1 y3 hy3O hy3 g3 hg3 τ3 hτ3⟩
  obtain ⟨y4, hy4O, hy4, g4, hg4, τ4, hτ4⟩ := cm4_exists
  obtain ⟨y24, hy24O, hy24, g24, hg24, τ24, hτ24⟩ := cm24_exists
  have hb : b = 0 := by
    have := hab τ4
    rw [hf.2.2.2.2.1 y4 hy4O hy4 g4 hg4 τ4 hτ4, hh.2.2.2.1 y4 hy4O hy4 g4 hg4 τ4 hτ4,
      OnePoint.map_some] at this
    have := OnePoint.coe_injective this
    simpa using this.symm
  have ha1 : a = 1 := by
    have := hab τ24
    rw [hf.2.2.2.2.2.2 y24 hy24O hy24 g24 hg24 τ24 hτ24,
      hh.2.2.2.2.2 y24 hy24O hy24 g24 hg24 τ24 hτ24, OnePoint.map_some, hb] at this
    have := OnePoint.coe_injective this
    have h' : (a - 1) * (-16 / 27 : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · norm_num at h''
  funext τ
  have hid : (fun z : ℂ => a * z + b) = id := by funext z; simp [ha1, hb]
  rw [hab τ, hid, OnePoint.map_id]
  rfl

/-! ### `QMDenZeroCM3` -/

/-- `S/dF⁴ = Σθ_m⁸(Ω(τ)) / ((τ − 3)(τ + 1))⁴`, the weight-8 automorphic form of `Γ*`
(`dF(τ) = (τ − 3)(τ + 1)` is proportional to `det F₀(τ)`, `QMLattice.det_Fp`; it has no zero on
`ℍ`). -/
def G8 (z : ℂ) : ℂ := PkgI1.thetaSum8 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 4

/-- **GLUE (the weight of `Σθ⁸ ∘ Ω` under `Γ*`).** For `γ ∈ Γ*` and `τ ∈ ℍ`,
`|G8(γτ)| · det(γ)⁴ = |cτ + d|⁸ |G8(τ)|`, i.e. `G8` has weight 8 for the automorphy factor
`(cτ + d)/√det γ`, in absolute value.

Numerically VERIFIED (`py/al_weight.py`, `al_weight_out.txt`; and fibre-qm-period's
`psi4_zeros_out.txt`, the `detF'^(-4)` rows): ratio `1.0` to 10 digits for `γ = ι(x)` with
`x = (1+j)/2, i+j, 3+2i` (reduced norm 1) and the Atkin–Lehner elements `x = j` (norm 3),
`2+i` (norm 2), `2j+ij` (norm 6), `1+j` (norm 4), each at two points. (fibre-qm-period's report
calls this form `S·dF⁴`; its printed formula `|S(γτ)/S(τ)| = |cτ+d|⁸|dF(τ)/dF(γτ)|⁴` is the
correct one and gives `S/dF⁴`.) Why true: for `γ ∈ Γ*` the QM surfaces at `τ` and `γτ` are
isomorphic as principally polarized abelian surfaces (the principal polarization of a QM surface
of discriminant 6 is unique up to `Aut`; Rotger), so `Ω(γτ) = M·Ω(τ)` for some `M ∈ Sp₄(ℤ)`, and
Igusa's `ThetaModularity` (pkg-I1 leaf) gives `Σθ⁸(Ω(γτ)) = det(CΩ + D)⁴ Σθ⁸(Ω(τ))`, with
`det(CΩ(τ) + D) = ±(cτ + d)² dF(γτ)/(det γ · dF(τ))` from the explicit `Ω` (SPECULATIVE in this
generality; the Sp₄(ℤ) matrix for each generator of `Γ*` is a finite computation). Size: medium. -/
def S8Weight8 : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
    ‖G8 ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ 4 =
      ‖denom γ z‖ ^ 8 * ‖G8 (z : ℂ)‖

/-- **GLUE (a vanishing order).** `S/dF⁴` (equivalently `Σθ_m⁸ ∘ Ω`, since `dF(i√3) ≠ 0`) vanishes
to order at least 2 at `i√3`, the fixed point of `ι((1+j)/2)`.

Numerically VERIFIED: order `1.99992` (fibre-qm-period, `psi4_zeros_out.txt`) and `|S(Ω(i√3))| ≈
4·10⁻⁴⁰` at 40 digits. Why true: `ι((1+j)/2)` fixes `i√3`, with `cτ + d = e^{iπ/3}` there; the
automorphy of `S8Weight8` with its unitary multiplier forces a zero whose order is fixed mod 6
(the usual argument at an elliptic point), and Lin–Yang's divisor of `ψ₄` on `X₆/W` puts a double
zero (in the local parameter of `ℍ`) at `P₋₃` (Lin–Yang 2020, Example 29, UNVERIFIED reading). A
certified numerical proof needs `S(Ω(i√3)) = 0` exactly (which follows from the multiplier if it
is trivial on the stabilizer) and one derivative. Size: small-medium. -/
def S8OrderCM3 : Prop := 2 ≤ analyticOrderAt G8 (tau3 : ℂ)

/-- **LEAF (valence formula for the cocompact group `Γ*`, inequality consequence).** Let `F` be
holomorphic on `ℍ`, not identically zero, with `|F(γτ)| det(γ)^m = |cτ + d|^{2m} |F(τ)|` for all
`γ ∈ Γ*` (weight `2m`, any unitary multiplier). Then for every finite set `T` of pairwise
`Γ*`-inequivalent points, `2 Σ_{τ ∈ T} ord_τ F ≤ m`.

Source: the valence formula for a Fuchsian group of the first kind,
`Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/2)(2g − 2 + Σ_j (1 − 1/e_j))` (Shimura, *Introduction to the
arithmetic theory of automorphic functions*, 1971, §2.4, Prop. 2.16 / Thm. 2.20; Rankin, *Modular
forms and functions*, 1977, Thm. 4.1.4, for general unitary multiplier systems; UNVERIFIED locators),
and the signature `(0; 2, 4, 6)` of `Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` for the quaternion algebra of
discriminant 6 (`X₆/W ≅ P¹` is the `(2, 4, 6)` triangle quotient: Elkies, *Shimura curve
computations*, ANTS 1998, §3; Baba–Granath 2008, §3.1, as quoted in pkg-I1; UNVERIFIED locators).
With `k = 2m` the right side is `m · (−2 + 1/2 + 3/4 + 5/6) = m/12`; since `e_P ≤ 6`,
`Σ_{T} ord ≤ 6 · m/12 = m/2`. A consequence of the published statements (weaker: an inequality,
and only the bound `e_P ≤ 6`). The absolute-value hypothesis gives a unitary multiplier
(`F(γτ)/(j(γ,τ)^k F(τ))` is holomorphic of modulus one off the zeros, hence constant). -/
def ValenceBoundGammaStar : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) →
      2 * ∑ z ∈ T, analyticOrderAt F (z : ℂ) ≤ (m : ℕ∞)

/-! #### `ι` is multiplicative; `Γ*` is closed under inverses; conjugation (proved) -/

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

theorem iota_one : PkgI1.iota 1 = 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem gammaStar_inv {γ : GL (Fin 2) ℝ} (hγ : γ ∈ PkgI1.GammaStar) : γ⁻¹ ∈ PkgI1.GammaStar := by
  obtain ⟨x, ⟨y, hxy, hyx, hcl⟩, hγx, hdet⟩ := hγ
  have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota y = 1 := by
    rw [hγx, ← iota_mul, hxy, iota_one]
  refine ⟨y, ⟨x, hyx, hxy, fun z hz => ⟨(hcl z hz).2, (hcl z hz).1⟩⟩, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_right_inv h1
  · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_eq_right_inv h1]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    rcases lt_or_ge 0 (PkgI1.iota y).det with h | h
    · exact h
    · nlinarith

/-- A point `Γ*`-equivalent to `i√3` is a fixed point of `ι(x')` for some `x' ∈ 𝒪` with
`x'² − x' + 1 = 0` (conjugation by the normalizer). -/
theorem cm3_of_equiv {γ : GL (Fin 2) ℝ} (hγ : γ ∈ PkgI1.GammaStar) {τ : UpperHalfPlane}
    (hτ : γ • tau3 = τ) :
    ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ g • τ = τ := by
  obtain ⟨u, ⟨v, huv, hvu, hcl⟩, hγu, -⟩ := hγ
  have hγinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota v := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota v = 1 := by
      rw [hγu, ← iota_mul, huv, iota_one]
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_right_inv h1
  refine ⟨u * x3 * v, (hcl x3 inO_x3).1, ?_, γ * glOf x3 (by rw [det_x3]; norm_num) * γ⁻¹, ?_, ?_⟩
  · have e1 : u * x3 * v * (u * x3 * v) = u * (x3 * x3) * v := by
      rw [show u * x3 * v * (u * x3 * v) = u * x3 * (v * u) * x3 * v by noncomm_ring, hvu]
      noncomm_ring
    calc u * x3 * v * (u * x3 * v) - u * x3 * v + 1
        = u * (x3 * x3) * v - u * x3 * v + u * v := by rw [e1, huv]
      _ = u * (x3 * x3 - x3 + 1) * v := by noncomm_ring
      _ = 0 := by rw [x3_sq]; simp
  · simp only [Matrix.GeneralLinearGroup.coe_mul, hγinv, hγu, coe_glOf, iota_mul]
  · rw [← hτ, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul, cm3_tau3]

/-- **`QMDenZeroCM3` from strictly smaller named Props (proved).** -/
theorem qmDenZeroCM3_of (hT : ThetaOmegaAnalytic) (hS : S8Nonzero) (hW : S8Weight8)
    (hO : S8OrderCM3) (hV : ValenceBoundGammaStar) : QMDenZeroCM3 := by
  classical
  intro τ hτ
  have hdF : ∀ z ∈ U, ((z - 3) * (z + 1)) ^ 4 ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    have hz' : (0 : ℝ) < z.im := hz
    apply mul_ne_zero <;> intro h0 <;> have := congrArg Complex.im h0 <;> simp at this <;>
      exact hz'.ne' this
  have hGa : AnalyticOnNhd ℂ G8 U := by
    intro z hz
    exact (hT.1 z hz).div ((((analyticAt_id.sub analyticAt_const).mul
      (analyticAt_id.add analyticAt_const))).pow 4) (hdF z hz)
  have hGne : ∃ z ∈ U, G8 z ≠ 0 :=
    ⟨_, mem_U_s2I, div_ne_zero hS (hdF _ mem_U_s2I)⟩
  have hGτ : G8 (τ : ℂ) = 0 := by
    have : PkgI1.thetaSum8 (PkgI1.Omega τ) = 0 := pow_eq_zero_iff (n := 5) (by norm_num) |>.mp hτ
    simp [G8, this]
  by_cases heq : ∃ γ ∈ PkgI1.GammaStar, γ • tau3 = τ
  · obtain ⟨γ, hγ, hγτ⟩ := heq
    obtain ⟨x, hxO, hx, g, hg, hgτ⟩ := cm3_of_equiv hγ hγτ
    exact ⟨x, hxO, hx, g, hg, hgτ⟩
  · exfalso
    push Not at heq
    have hne : tau3 ≠ τ := by
      intro h
      apply heq 1 ⟨1, ⟨1, by simp, by simp, fun z hz => by simp only [one_mul, mul_one]; exact ⟨hz, hz⟩⟩,
        by simp [iota_one], by simp⟩
      simpa using h
    have hpair : ((({tau3, τ} : Finset UpperHalfPlane)) : Set UpperHalfPlane).Pairwise
        (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) := by
      intro a ha b hb hab γ hγ
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact heq γ hγ
      · intro h
        apply heq γ⁻¹ (gammaStar_inv hγ)
        rw [← h, inv_smul_smul]
      · exact absurd rfl hab
    have hval := hV 4 G8 hGa hGne (fun γ hγ z => hW γ hγ z) {tau3, τ} hpair
    rw [Finset.sum_pair hne] at hval
    have h1 : 1 ≤ analyticOrderAt G8 (τ : ℂ) := by
      have : analyticOrderAt G8 (τ : ℂ) ≠ 0 :=
        analyticOrderAt_ne_zero.mpr ⟨hGa _ τ.im_pos, hGτ⟩
      exact Order.one_le_iff_ne_zero.mpr this
    have h3 : (3 : ℕ∞) ≤ analyticOrderAt G8 (tau3 : ℂ) + analyticOrderAt G8 (τ : ℂ) :=
      calc (3 : ℕ∞) = 2 + 1 := by norm_num
        _ ≤ _ := add_le_add hO h1
    have h6 : (2 : ℕ∞) * 3 ≤ 2 * (analyticOrderAt G8 (tau3 : ℂ) + analyticOrderAt G8 (τ : ℂ)) := by
      gcongr
    have := h6.trans hval
    norm_num at this

end HSyn.G0Split.FibreQM.PeriodMap

end

/-! ### Axiom checks -/

#print axioms HSyn.G0Split.FibreQM.PeriodMap.isHolP1At_of_hauptFn
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm4_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm3_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm24_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.hauptmodulUnique_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.iota_mul
#print axioms HSyn.G0Split.FibreQM.PeriodMap.gammaStar_inv
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm3_of_equiv
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of

/-! ## period-map: `ThetaOmegaAnalytic` from `OmegaSiegel` (the theta series converge locally uniformly)

`thetaOmegaAnalytic_of : OmegaSiegel → ThetaOmegaAnalytic`. `OmegaSiegel` (`Ω(τ) ∈ 𝔥₂` for `τ ∈ ℍ`)
is a closed-form computation (VERIFIED with sympy, `py/omega_sym.py`). The proof: the entries of
`Ω` are holomorphic on `ℍ` (adjugate formula; `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2`); near `τ₀` the form
`w ↦ wᵀ Im Ω(τ) w` is bounded below by `c|w|²` uniformly (`(p+r)Q(w) − (pr−q²)|w|² =
(pw₀+qw₁)² + (qw₀+rw₁)²`, continuity); so each theta term is bounded by a summable Gaussian
(Mathlib's Jacobi-theta bound) and the series is holomorphic (`differentiableOn_tsum_of_summable_norm`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology Matrix

/-- **GLUE (computational).** For `τ ∈ ℍ`, `Ω(τ)` lies in the Siegel upper half-space `𝔥₂`
(pkg-I1's `SiegelH2`: symmetric with positive definite imaginary part).

VERIFIED symbolically (`py/omega_sym.py`, sympy; output `omega_sym_out.txt`): `Ω(τ)` is symmetric,
and with `τ = x + iy`, `det Im Ω = 12y²/(|τ − 3|²|τ + 1|²)` and
`(Im Ω)₁₁ = 2y((4 − √2)|τ|² − 6√2x + 12 + 3√2)/(|τ − 3|²|τ + 1|²)`, positive for `y > 0` (the
quadratic in `x` has discriminant `72 − 168 < 0`). Conceptually: `Ω(τ)` is the period matrix of
the principally polarized QM surface `ℂ²/Λ_τ` in a symplectic basis (Riemann's relations). A Lean
proof is a finite computation with the explicit rational entries. Size: small-medium. -/
def OmegaSiegel : Prop := ∀ τ : ℂ, 0 < τ.im → PkgI1.Omega τ ∈ PkgI1.SiegelH2

theorem latVec_apply (x : PkgI1.B) (τ : ℂ) (r : Fin 2) :
    PkgI1.latVec x τ r = (PkgI1.iota x r 0 : ℂ) * τ + (PkgI1.iota x r 1 : ℂ) := by
  simp [PkgI1.latVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem differentiable_F0P (i j : Fin 2) :
    Differentiable ℂ (fun τ => (PkgI1.F0mat τ * PkgI1.Pinv) i j) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [latVec_apply] <;> fun_prop

theorem differentiable_E (i j : Fin 2) : Differentiable ℂ (fun τ => PkgI1.Emat τ i j) := by
  simp only [PkgI1.Emat, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [latVec_apply] <;> fun_prop

theorem det_F0P (τ : ℂ) :
    (PkgI1.F0mat τ * PkgI1.Pinv).det = -(√2 : ℂ) * (τ - 3) * (τ + 1) / 2 := by
  rw [Matrix.det_mul, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [PkgI1.F0mat, PkgI1.Pinv, latVec_apply, PkgI1.iota, PkgI1.Mi, PkgI1.Mj, PkgI1.oBasis,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem det_F0P_ne {τ : ℂ} (hτ : τ.im ≠ 0) : (PkgI1.F0mat τ * PkgI1.Pinv).det ≠ 0 := by
  rw [det_F0P]
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have hs : (√2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact Real.sqrt_ne_zero'.mpr two_pos
  have : -(√2 : ℂ) * (τ - 3) * (τ + 1) ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs) h3) h1
  exact div_ne_zero this two_ne_zero

theorem differentiableAt_inv_mul {A E : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {τ : ℂ}
    (hA : ∀ i j, DifferentiableAt ℂ (fun σ => A σ i j) τ)
    (hE : ∀ i j, DifferentiableAt ℂ (fun σ => E σ i j) τ) (hd : (A τ).det ≠ 0) (i j : Fin 2) :
    DifferentiableAt ℂ (fun σ => ((A σ)⁻¹ * E σ) i j) τ := by
  have h1 : ∀ σ, ((A σ)⁻¹ * E σ) i j =
      ((A σ).det)⁻¹ * ∑ k, adjugate (A σ) i k * E σ k j := by
    intro σ
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
      Matrix.mul_apply]
  simp_rw [h1]
  have hdet : DifferentiableAt ℂ (fun σ => (A σ).det) τ := by
    simp_rw [Matrix.det_fin_two]
    exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  refine (hdet.inv hd).mul ?_
  have hadj : ∀ i k, DifferentiableAt ℂ (fun σ => adjugate (A σ) i k) τ := by
    intro i k
    simp_rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases k <;> simp <;> first | exact hA _ _ | exact (hA _ _).neg
  exact DifferentiableAt.fun_sum (fun k _ => (hadj i k).mul (hE k j))

theorem differentiableAt_omega {τ : ℂ} (hτ : τ.im ≠ 0) (i j : Fin 2) :
    DifferentiableAt ℂ (fun σ => PkgI1.Omega σ i j) τ :=
  differentiableAt_inv_mul (A := fun σ => PkgI1.F0mat σ * PkgI1.Pinv) (E := PkgI1.Emat)
    (fun i j => (differentiable_F0P i j) τ) (fun i j => (differentiable_E i j) τ)
    (det_F0P_ne hτ) i j

/-- The summand of `thetaConst m (Ω τ)`. -/
def thTerm (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ) : ℂ :=
  let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
  Complex.exp (Real.pi * I * (v ⬝ᵥ (PkgI1.Omega τ *ᵥ v)) +
    Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

theorem thetaConst_omega (m : PkgI1.Char2) (τ : ℂ) :
    PkgI1.thetaConst m (PkgI1.Omega τ) = ∑' n, thTerm m n τ := rfl

/-- The real vector `n + a/2`. -/
def wv (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) : ℝ := (n k : ℝ) + ((m.1 k : ℕ) : ℝ) / 2

/-- `wᵀ Im Ω(τ) w`. -/
def qf (τ : ℂ) (w : Fin 2 → ℝ) : ℝ :=
  w 0 ^ 2 * (PkgI1.Omega τ 0 0).im +
    w 0 * w 1 * ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) +
    w 1 ^ 2 * (PkgI1.Omega τ 1 1).im

theorem norm_thTerm (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ) :
    ‖thTerm m n τ‖ = Real.exp (-Real.pi * qf τ (wv m n)) := by
  rw [thTerm, Complex.norm_exp]
  congr 1
  simp [qf, wv, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

theorem quad_lower (p q r w0 w1 : ℝ) (h : 0 < p + r) :
    (p * r - q ^ 2) / (p + r) * (w0 ^ 2 + w1 ^ 2) ≤
      w0 ^ 2 * p + w0 * w1 * (2 * q) + w1 ^ 2 * r := by
  rw [div_mul_eq_mul_div, div_le_iff₀ h]
  nlinarith [sq_nonneg (p * w0 + q * w1), sq_nonneg (q * w0 + r * w1)]

theorem wv_sq_ge (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) :
    (n k : ℝ) ^ 2 - |(n k : ℝ)| ≤ wv m n k ^ 2 := by
  have h0 : (0 : ℝ) ≤ ((m.1 k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((m.1 k : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp (m.1 k).isLt
  rw [wv]
  have ha : -|(n k : ℝ)| ≤ (n k : ℝ) * ((m.1 k : ℕ) : ℝ) := by
    rcases le_total 0 (n k : ℝ) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; nlinarith
  nlinarith [sq_nonneg (((m.1 k : ℕ) : ℝ) / 2)]

/-- The Gaussian bound (Mathlib's Jacobi-theta bound with `T = c`, `S = c/2`). -/
def gb (c : ℝ) (k : ℤ) : ℝ := Real.exp (-Real.pi * (c * (k : ℝ) ^ 2 - 2 * (c / 2) * |(k : ℝ)|))

theorem summable_gb2 {c : ℝ} (hc : 0 < c) :
    Summable (fun n : Fin 2 → ℤ => gb c (n 0) * gb c (n 1)) := by
  have h1 : Summable (gb c) := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound (c / 2) hc 0).congr fun k => ?_
    simp only [gb, pow_zero, one_mul, Int.cast_abs]
  have h2 : Summable (fun p : ℤ × ℤ => gb c p.1 * gb c p.2) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  exact (finTwoArrowEquiv ℤ).summable_iff.mpr h2

theorem norm_thTerm_le {c : ℝ} (hc : 0 < c) (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ)
    (hq : ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w) :
    ‖thTerm m n τ‖ ≤ gb c (n 0) * gb c (n 1) := by
  rw [norm_thTerm, gb, gb, ← Real.exp_add, Real.exp_le_exp]
  have h := hq (wv m n)
  have h0 := wv_sq_ge m n 0
  have h1 := wv_sq_ge m n 1
  have hp := Real.pi_pos
  have h2 : c * (((n 0 : ℝ) ^ 2 - |(n 0 : ℝ)|) + ((n 1 : ℝ) ^ 2 - |(n 1 : ℝ)|)) ≤ qf τ (wv m n) :=
    le_trans (mul_le_mul_of_nonneg_left (add_le_add h0 h1) hc.le) h
  have h3 := mul_le_mul_of_nonneg_left h2 hp.le
  nlinarith [h3]

/-- **`ThetaOmegaAnalytic` from `OmegaSiegel` (proved).** -/
theorem thetaOmegaAnalytic_of (hS : OmegaSiegel) : ThetaOmegaAnalytic := by
  -- each theta constant along `Ω` is analytic at every `τ₀ ∈ ℍ`
  have hθ : ∀ τ₀ ∈ U, ∀ m : PkgI1.Char2,
      AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
    intro τ₀ hτ₀ m
    have hτ₀' : (0 : ℝ) < τ₀.im := hτ₀
    obtain ⟨hsym, hpd⟩ := hS τ₀ hτ₀'
    set p : ℂ → ℝ := fun τ => (PkgI1.Omega τ 0 0).im with hp
    set q : ℂ → ℝ := fun τ => ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) / 2 with hq
    set r : ℂ → ℝ := fun τ => (PkgI1.Omega τ 1 1).im with hr
    have hcont : ∀ i j, ContinuousAt (fun τ => (PkgI1.Omega τ i j).im) τ₀ := fun i j =>
      Complex.continuous_im.continuousAt.comp (differentiableAt_omega hτ₀'.ne' i j).continuousAt
    have hp0 : 0 < p τ₀ := by
      have := hpd.diag_pos (i := 0); simpa [hp] using this
    have hr0 : 0 < r τ₀ := by
      have := hpd.diag_pos (i := 1); simpa [hr] using this
    have hsym01 : PkgI1.Omega τ₀ 1 0 = PkgI1.Omega τ₀ 0 1 := by
      have := congrFun (congrFun hsym 0) 1; simpa using this
    have hdet0 : 0 < p τ₀ * r τ₀ - q τ₀ ^ 2 := by
      have := hpd.det_pos
      rw [Matrix.det_fin_two] at this
      simp only [Matrix.map_apply] at this
      rw [hsym01] at this
      simp only [hp, hq, hr, hsym01]
      nlinarith [this]
    set g : ℂ → ℝ := fun τ => (p τ * r τ - q τ ^ 2) / (p τ + r τ) with hg
    have hg0 : 0 < g τ₀ := div_pos hdet0 (add_pos hp0 hr0)
    have hpc : ContinuousAt p τ₀ := hcont 0 0
    have hrc : ContinuousAt r τ₀ := hcont 1 1
    have hqc : ContinuousAt q τ₀ := ((hcont 0 1).add (hcont 1 0)).div_const 2
    have hgc : ContinuousAt g τ₀ :=
      ((hpc.mul hrc).sub (hqc.pow 2)).div (hpc.add hrc) (add_pos hp0 hr0).ne'
    have hev : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U ∧ 0 < p τ + r τ ∧ g τ₀ / 2 < g τ := by
      refine (show ∀ᶠ τ in 𝓝 τ₀, τ ∈ U from isOpen_U.mem_nhds hτ₀).and ((?_ : ∀ᶠ τ in 𝓝 τ₀, 0 < p τ + r τ).and ?_)
      · exact (hpc.add hrc).eventually (lt_mem_nhds (add_pos hp0 hr0))
      · exact hgc.eventually (lt_mem_nhds (half_lt_self hg0))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set c := g τ₀ / 2 with hcdef
    have hc : 0 < c := half_pos hg0
    have hq_ball : ∀ τ ∈ Metric.ball τ₀ ε, ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w := by
      intro τ hτ w
      obtain ⟨-, hpr, hgt⟩ := hball τ hτ
      have hl := quad_lower (p τ) (q τ) (r τ) (w 0) (w 1) hpr
      have hw : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
      calc c * (w 0 ^ 2 + w 1 ^ 2) ≤ g τ * (w 0 ^ 2 + w 1 ^ 2) :=
            mul_le_mul_of_nonneg_right hgt.le hw
        _ ≤ _ := by
          refine hl.trans (le_of_eq ?_)
          simp only [qf, hp, hq, hr]
          ring
    have hdiff : ∀ n, DifferentiableOn ℂ (thTerm m n) (Metric.ball τ₀ ε) := by
      intro n σ hσ
      have hσU : (0 : ℝ) < σ.im := (hball σ hσ).1
      have hΩ := fun i j => differentiableAt_omega hσU.ne' i j
      apply DifferentiableAt.differentiableWithinAt
      set V : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2 with hV
      set Bv : Fin 2 → ℂ := fun k => ((m.2 k : ℕ) : ℂ) with hBv
      have key : thTerm m n = fun τ => Complex.exp (Real.pi * I * (V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) +
          Real.pi * I * (V ⬝ᵥ Bv)) := rfl
      have hq : DifferentiableAt ℂ (fun τ => V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) σ := by
        simp only [dotProduct, Matrix.mulVec]
        refine DifferentiableAt.fun_sum fun i _ => ?_
        refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j _ => ?_) _
        exact (hΩ i j).mul_const _
      rw [key]
      exact ((hq.const_mul _).add_const _).cexp
    have hdon : DifferentiableOn ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ))
        (Metric.ball τ₀ ε) :=
      differentiableOn_tsum_of_summable_norm (summable_gb2 hc) hdiff Metric.isOpen_ball
        (fun n τ hτ => norm_thTerm_le hc m n τ (hq_ball τ hτ))
    exact hdon.analyticAt (Metric.ball_mem_nhds τ₀ hε)
  refine ⟨fun τ₀ hτ₀ => ?_, fun τ₀ hτ₀ => ?_⟩
  · show AnalyticAt ℂ (fun τ => ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) τ₀
    exact Finset.analyticAt_fun_sum _ (fun m _ => (hθ τ₀ hτ₀ m).pow 8)
  · show AnalyticAt ℂ (fun τ => ∏ m ∈ PkgI1.evenChars, PkgI1.thetaConst m (PkgI1.Omega τ) ^ 2) τ₀
    exact Finset.analyticAt_fun_prod _ (fun m _ => (hθ τ₀ hτ₀ m).pow 2)

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.thetaOmegaAnalytic_of
