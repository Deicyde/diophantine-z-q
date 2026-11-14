import ZInQKernel.OneProof.H.TailI

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_c90_periodglue
-- (leaf-fold4) mk_periodglue.py: period-map parts light/theta/siegel/order/heavy and period-glue BCU, QMTwist,
-- PiTwist, S8, W8, SFA, final_part (import/#print lines dropped; declarations already in the chain dropped)
/-! ## leaf-fold4: scratch/period-map/part_light.lean (declarations already in the chain dropped) -/


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
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply ofComplex_apply_of_im_pos num denom denom_ne_zero)
open HSyn.G0Split.FibreQM

/-- The open upper half-plane as a subset of `ℂ`. -/
def U : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_U : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected

/-! ### Named Props (glue) shared by both reductions -/

/-- **Holomorphy of the theta constants along the modular embedding** (stated as glue here; PROVED
below, `thetaOmegaAnalytic_proof` in the section on `OmegaSiegel`). `Σ_{m even} θ_m⁸ ∘ Ω`
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

/-- **The weight of `Σθ⁸ ∘ Ω` under `Γ*`** (absolute-value form; derived below from the exact form
`S8WeightExact`, `s8Weight8_of`). For `γ ∈ Γ*` and `τ ∈ ℍ`,
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

/-- **A vanishing order** (derived below from `S8WeightExact` and holomorphy, `s8OrderCM3_of`). `S/dF⁴` (equivalently `Σθ_m⁸ ∘ Ω`, since `dF(i√3) ≠ 0`) vanishes
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



/-! ## leaf-fold4: scratch/period-map/part_theta.lean (declarations already in the chain dropped) -/


/-! ## period-map: `ThetaOmegaAnalytic` from `OmegaSiegel` (the theta series converge locally uniformly)

`thetaOmegaAnalytic_of : OmegaSiegel → ThetaOmegaAnalytic`. `OmegaSiegel` (`Ω(τ) ∈ 𝔥₂` for `τ ∈ ℍ`)
is a closed-form computation (VERIFIED with sympy, `py/omega_sym.py`). The proof: the entries of
`Ω` are holomorphic on `ℍ` (adjugate formula; `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2`); near `τ₀` the form
`w ↦ wᵀ Im Ω(τ) w` is bounded below by `c|w|²` uniformly (`(p+r)Q(w) − (pr−q²)|w|² =
(pw₀+qw₁)² + (qw₀+rw₁)²`, continuity); so each theta term is bounded by a summable Gaussian
(Mathlib's Jacobi-theta bound) and the series is holomorphic (`differentiableOn_tsum_of_summable_norm`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

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



/-! ## leaf-fold4: scratch/period-map/part_siegel.lean (declarations already in the chain dropped) -/


/-! ## period-map: `OmegaSiegel` proved (closed form of `Ω(τ)`)

`Ω(τ) = adj(F₀P⁻¹)E / det(F₀P⁻¹)` with `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2` and the adjugate product `Nf`
computed by `py/omega_lean.py` (entries reduced mod `√2² = 2`; the `linear_combination` coefficients
are the quotients printed there). With `τ = x + iy`, `Im Ω_ij = A_ij/|d|²` where
`A₀₀ = (y/2)((4−√2)(x²+y²) − 6√2x + 12 + 3√2)`, `A₁₁ = 2A₀₀`, and
`A₀₀A₁₁ − A₀₁² = 3y²|τ−3|²|τ+1|²`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex Matrix

/-- `det(F₀(τ)P⁻¹)`. -/
def dF (τ : ℂ) : ℂ := -(√2 : ℂ) * (τ - 3) * (τ + 1) / 2

/-- `adj(F₀(τ)P⁻¹)·E(τ)`, entries reduced mod `√2² = 2`. -/
def Nf (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(√2 : ℂ) * (τ ^ 2 / 2 + τ - 3 / 2) - τ ^ 2 / 2 - 3 / 2,
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3;
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3,
     (√2 : ℂ) * (τ ^ 2 + 2 * τ - 3) - τ ^ 2 - 3]

theorem adjE_eq (τ : ℂ) : adjugate (PkgI1.F0mat τ * PkgI1.Pinv) * PkgI1.Emat τ = Nf τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, PkgI1.Pinv,
      PkgI1.Emat, latVec_apply, PkgI1.iota, PkgI1.Mi, PkgI1.Mj, PkgI1.oBasis, Nf]
  · ring
  · linear_combination (τ ^ 2 / 2 + 3 / 2) * sqrt2_sq
  · ring
  · linear_combination (-τ ^ 2 / 2 - 3 / 2) * sqrt2_sq

theorem omega_eq (τ : ℂ) (i j : Fin 2) : PkgI1.Omega τ i j = Nf τ i j / dF τ := by
  have h : PkgI1.Omega τ = (PkgI1.F0mat τ * PkgI1.Pinv)⁻¹ * PkgI1.Emat τ := rfl
  rw [h, Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    adjE_eq, det_F0P, dF]
  ring

/-- `A₀₀/(y/2)`. -/
def Qf (x y : ℝ) : ℝ := (4 - √2) * (x ^ 2 + y ^ 2) - 6 * √2 * x + 12 + 3 * √2

theorem Qf_pos (x y : ℝ) : 0 < Qf x y := by
  have hs := sqrt2_sq'
  have h4 : 0 < 4 - √2 := by
    have : √2 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hid : (4 - √2) * Qf x y = ((4 - √2) * x - 3 * √2) ^ 2 + ((4 - √2) * y) ^ 2 + 24 := by
    unfold Qf; linear_combination (-12 : ℝ) * hs
  have : 0 < (4 - √2) * Qf x y := by rw [hid]; positivity
  exact pos_of_mul_pos_right this h4.le

theorem A00_eq (τ : ℂ) :
    (Nf τ 0 0).im * (dF τ).re - (Nf τ 0 0).re * (dF τ).im = τ.im / 2 * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (τ.re ^ 2 * τ.im + τ.im ^ 3 + 3 * τ.im) * sqrt2_sq'

theorem A01_eq (τ : ℂ) : (Nf τ 0 1).im * (dF τ).re - (Nf τ 0 1).re * (dF τ).im =
    τ.im * (√2 * τ.re ^ 2 + 6 * √2 * τ.re + √2 * τ.im ^ 2 - 3 * √2 - 2 * τ.re ^ 2 -
      2 * τ.im ^ 2 - 6) := by
  simp [Nf, dF, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (-τ.re ^ 2 * τ.im - τ.im ^ 3 - 3 * τ.im) * sqrt2_sq'

theorem A11_eq (τ : ℂ) :
    (Nf τ 1 1).im * (dF τ).re - (Nf τ 1 1).re * (dF τ).im = τ.im * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (2 * τ.re ^ 2 * τ.im + 2 * τ.im ^ 3 + 6 * τ.im) * sqrt2_sq'

theorem det_A (x y : ℝ) :
    y / 2 * Qf x y * (y * Qf x y) - y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6) * (y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6)) =
      3 * y ^ 2 * ((x - 3) ^ 2 + y ^ 2) * ((x + 1) ^ 2 + y ^ 2) := by
  unfold Qf
  linear_combination (-x ^ 4 * y ^ 2 / 2 - 6 * x ^ 3 * y ^ 2 - x ^ 2 * y ^ 4 - 15 * x ^ 2 * y ^ 2 -
    6 * x * y ^ 4 + 18 * x * y ^ 2 - y ^ 6 / 2 + 3 * y ^ 4 - 9 * y ^ 2 / 2) * sqrt2_sq'

/-- A real symmetric `2 × 2` matrix with `M₀₀ > 0` and `det M > 0` is positive definite. -/
theorem posDef_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} (hs : M 1 0 = M 0 1) (h0 : 0 < M 0 0)
    (hd : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hs]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [hs] at hd ⊢
    by_cases h1 : v 1 = 0
    · have h0' : v 0 ≠ 0 := by
        intro h; apply hv; funext i; fin_cases i <;> simp [h, h1]
      rw [h1]
      have : 0 < v 0 * v 0 := mul_self_pos.mpr h0'
      nlinarith
    · have : 0 < v 1 * v 1 := mul_self_pos.mpr h1
      have key : M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) =
          (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 0 1) * (v 1 * v 1) := by ring
      have hpos : 0 < M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) +
          v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) := by
        rw [key]; positivity
      exact pos_of_mul_pos_right hpos h0.le

/-- **`OmegaSiegel` (proved).** -/
theorem omegaSiegel_proof : OmegaSiegel := by
  intro τ hτ
  have hne : dF τ ≠ 0 := by
    have := det_F0P_ne hτ.ne'
    rwa [det_F0P] at this
  have hn : 0 < Complex.normSq (dF τ) := Complex.normSq_pos.mpr hne
  have him : ∀ i j, (PkgI1.Omega τ i j).im =
      ((Nf τ i j).im * (dF τ).re - (Nf τ i j).re * (dF τ).im) / Complex.normSq (dF τ) := by
    intro i j
    rw [omega_eq, Complex.div_im]
    ring
  have hsym : PkgI1.Omega τ 1 0 = PkgI1.Omega τ 0 1 := by
    rw [omega_eq, omega_eq]; rfl
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hsym]
  · apply posDef_fin_two
    · simp only [Matrix.map_apply, hsym]
    · simp only [Matrix.map_apply]
      rw [him, A00_eq]
      exact div_pos (mul_pos (half_pos hτ) (Qf_pos _ _)) hn
    · simp only [Matrix.map_apply]
      rw [hsym, him 0 0, him 1 1, him 0 1, A00_eq, A11_eq, A01_eq]
      rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, det_A]
      apply div_pos _ (mul_pos hn hn)
      have h3 : 0 < (τ.re - 3) ^ 2 + τ.im ^ 2 := by positivity
      have h1 : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by positivity
      positivity

/-- **`ThetaOmegaAnalytic` (proved).** -/
theorem thetaOmegaAnalytic_proof : ThetaOmegaAnalytic := thetaOmegaAnalytic_of omegaSiegel_proof

/-- **`HauptmodulUnique` from `S8Nonzero` and `SphereFactorAffine` (proved).** -/
theorem hauptmodulUnique_of' (hS : S8Nonzero) (hSF : SphereFactorAffine) : HauptmodulUnique :=
  hauptmodulUnique_of thetaOmegaAnalytic_proof hS hSF

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8Weight8`, `S8OrderCM3` and `ValenceBoundGammaStar`
(proved).** -/
theorem qmDenZeroCM3_of' (hS : S8Nonzero) (hW : S8Weight8) (hO : S8OrderCM3)
    (hV : ValenceBoundGammaStar) : QMDenZeroCM3 :=
  qmDenZeroCM3_of thetaOmegaAnalytic_proof hS hW hO hV

end HSyn.G0Split.FibreQM.PeriodMap

end



/-! ## leaf-fold4: scratch/period-map/part_order.lean (declarations already in the chain dropped) -/


/-! ## period-map: `S8Weight8` and `S8OrderCM3` from the exact automorphy `S8WeightExact`

`S8WeightExact` (`G8(γτ)·det γ⁴ = (cτ + d)⁸ G8(τ)` on `Γ*`, trivial multiplier; VERIFIED
numerically, `py/multiplier.py`) implies the absolute-value form `S8Weight8` (`s8Weight8_of`) and,
at the elliptic element `γ₃ = ι((1+j)/2)` fixing `i√3` with `cτ₃ + d = w = e^{iπ/3}`, the vanishing
order `S8OrderCM3` (`s8OrderCM3_of`): `G8(τ₃) = w⁸G8(τ₃)` with `w⁸ ≠ 1` gives `G8(τ₃) = 0`;
differentiating `G8 ∘ γ₃ = (cτ + d)⁸ G8` at `τ₃` gives `G8'(τ₃)(1 − w¹⁰) = 0` with `w¹⁰ = −w ≠ 1`;
so `ord_{τ₃} G8 ≥ 2`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex Filter Topology
open UpperHalfPlane (num denom denom_ne_zero)

/-- **GLUE (exact automorphy of `G8 = Σθ⁸∘Ω/((τ−3)(τ+1))⁴` under `Γ*`, trivial multiplier).**
For `γ ∈ Γ*` and `τ ∈ ℍ`, `G8(γτ)·det(γ)⁴ = (cτ + d)⁸ G8(τ)`.

VERIFIED numerically (`py/multiplier.py`, `multiplier_out.txt`, mpmath 40 digits): the ratio
`G8(γτ) det γ⁴/((cτ+d)⁸ G8(τ))` is `1` (to 9-40 digits) for `γ = ι(x)`, `x = (1+j)/2, j, i+j, 3+2i,
2j+ij, 1+i+j, 2+i`, at two points each; these include the elliptic generators of orders 2, 4, 6
(`py/gen_check.py`) and the Atkin–Lehner elements of norms 2, 3, 6. Why true: for `γ ∈ Γ*` the
principally polarized QM surfaces at `τ` and `γτ` are isomorphic, so `Ω(γτ) = M_γ·Ω(τ)` with
`M_γ ∈ Sp₄(ℤ)`; Igusa's `ThetaModularity` (pkg-I1 leaf) gives
`Σθ⁸(Ω(γτ)) = det(CΩ + D)⁴ Σθ⁸(Ω(τ))`, and `det(CΩ(τ) + D) = ±(cτ + d)² dF(γτ)/(det γ · dF(τ))`
from the explicit `Ω` (finite computation per generator of `Γ*`; that the tested elements generate
`Γ*` is the presentation of the `(2,4,6)` triangle group, not checked here). Size: medium. -/
def S8WeightExact : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
    G8 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ z ^ 8 * G8 (z : ℂ)

/-- **`S8Weight8` from `S8WeightExact` (proved).** -/
theorem s8Weight8_of (h : S8WeightExact) : S8Weight8 := by
  intro γ hγ z
  have ⟨_, _, _, hdet⟩ := hγ
  have e := congrArg norm (h γ hγ z)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
  exact e

theorem G8_analytic (hT : ThetaOmegaAnalytic) : AnalyticOnNhd ℂ G8 U := by
  intro z hz
  have hz' : (0 : ℝ) < z.im := hz
  have hdF : ((z - 3) * (z + 1)) ^ 4 ≠ 0 := by
    apply pow_ne_zero
    apply mul_ne_zero <;> intro h0 <;> have := congrArg Complex.im h0 <;> simp at this <;>
      exact hz'.ne' this
  exact (hT.1 z hz).div ((((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.add analyticAt_const))).pow 4) hdF

/-- `𝒪` is closed under multiplication (pkg-I1's membership; the coordinates of a product are
LeafQM's `mulCoord`). -/
theorem inO_mul {a b : PkgI1.B} (ha : PkgI1.InO a) (hb : PkgI1.InO b) : PkgI1.InO (a * b) := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  refine ⟨![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0], ?_⟩
  ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- `(1 − j)/2 = x₃⁻¹`. -/
def x3inv : PkgI1.B := ⟨1/2, 0, -1/2, 0⟩

theorem inO_x3inv : PkgI1.InO x3inv :=
  ⟨![1, 0, -1, 0], by ext <;> simp [x3inv, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

theorem x3_mem_gammaStar :
    glOf x3 (by rw [det_x3]; norm_num) ∈ PkgI1.GammaStar := by
  refine ⟨x3, ⟨x3inv, ?_, ?_, fun z hz => ⟨inO_mul (inO_mul inO_x3 hz) inO_x3inv,
    inO_mul (inO_mul inO_x3inv hz) inO_x3⟩⟩, rfl, ?_⟩
  · ext <;> simp [x3, x3inv] <;> norm_num
  · ext <;> simp [x3, x3inv] <;> norm_num
  · rw [coe_glOf, det_x3]; norm_num

/-- **`S8OrderCM3` from the holomorphy of the theta constants and `S8WeightExact` (proved).** -/
theorem s8OrderCM3_of (hT : ThetaOmegaAnalytic) (h : S8WeightExact) : S8OrderCM3 := by
  have hGa := G8_analytic hT
  set g := glOf x3 (by rw [det_x3]; norm_num) with hg
  have hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![1/2, -3/2; 1/2, 1/2] := by
    rw [hg, coe_glOf, iota_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [x3] <;> norm_num
  have hdetg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by rw [hg, coe_glOf, det_x3]
  set dz : ℂ → ℂ := fun z => z / 2 + 1 / 2 with hdz
  set mz : ℂ → ℂ := fun z => (z / 2 - 3 / 2) / (z / 2 + 1 / 2) with hmz
  have hden : ∀ z : UpperHalfPlane, denom g z = dz z := by
    intro z; simp only [UpperHalfPlane.denom, hgm, hdz]; simp; ring
  have hsmul : ∀ z : UpperHalfPlane, ((g • z : UpperHalfPlane) : ℂ) = mz z := by
    intro z
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdetg]; norm_num)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hgm, hmz]
    simp
    ring_nf
  -- the functional equation on `ℍ`
  have hFE : ∀ z : ℂ, 0 < z.im → G8 (mz z) = dz z ^ 8 * G8 z := by
    intro z hz
    have e := h g x3_mem_gammaStar ⟨z, hz⟩
    rw [hsmul, hden, hdetg] at e
    simpa using e
  set τ₃ : ℂ := (tau3 : ℂ) with hτ₃
  have hτ₃U : τ₃ ∈ U := tau3.im_pos
  have hτ₃im : (0 : ℝ) < τ₃.im := tau3.im_pos
  have hmτ : mz τ₃ = τ₃ := by
    have := hsmul tau3
    rw [cm3_tau3] at this
    exact this.symm
  set w : ℂ := dz τ₃ with hw
  have h3 : (√3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hwv : w = 1 / 2 + (√3 : ℂ) / 2 * I := by
    simp only [hw, hdz, hτ₃, tau3]; push_cast; ring
  have hw3 : w ^ 3 = -1 := by
    rw [hwv]
    linear_combination ((√3 : ℂ) ^ 2 * (I * √3 + 3) / 8) * I_sq + (-(I * √3 + 3) / 8) * h3
  have hw2 : w ^ 2 = -1 / 2 + (√3 : ℂ) / 2 * I := by
    rw [hwv]; linear_combination ((√3 : ℂ) ^ 2 / 4) * I_sq + (-1 / 4 : ℂ) * h3
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0] at hw3; norm_num at hw3
  -- `G8(τ₃) = 0`
  have hG0 : G8 τ₃ = 0 := by
    have e := hFE τ₃ hτ₃im
    rw [hmτ] at e
    have hw8 : w ^ 8 = w ^ 2 := by
      rw [show w ^ 8 = w ^ 2 * (w ^ 3) ^ 2 by ring, hw3]; ring
    have hne : w ^ 8 - 1 ≠ 0 := by
      rw [hw8, hw2]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    have : (w ^ 8 - 1) * G8 τ₃ = 0 := by
      simp only [hw] at e ⊢; linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left hne
  -- `G8'(τ₃) = 0`
  have hGd : DifferentiableAt ℂ G8 τ₃ := (hGa τ₃ hτ₃U).differentiableAt
  have hdzd : ∀ z, HasDerivAt dz (1 / 2) z := by
    intro z
    show HasDerivAt (fun z : ℂ => z / 2 + 1 / 2) (1 / 2) z
    exact ((hasDerivAt_id' z).div_const 2).add_const (1 / 2 : ℂ)
  have hnumd : HasDerivAt (fun z : ℂ => z / 2 - 3 / 2) (1 / 2) τ₃ := by
    exact ((hasDerivAt_id' τ₃).div_const 2).sub_const (3 / 2 : ℂ)
  have hmzd : HasDerivAt mz ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) / dz τ₃ ^ 2) τ₃ :=
    hnumd.div (hdzd τ₃) hw0
  have hL : HasDerivAt (G8 ∘ mz) (deriv G8 τ₃ * ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) /
      dz τ₃ ^ 2)) τ₃ := by
    have hG' : HasDerivAt G8 (deriv G8 τ₃) (mz τ₃) := by rw [hmτ]; exact hGd.hasDerivAt
    exact hG'.comp τ₃ hmzd
  have hR : HasDerivAt (fun z => dz z ^ 8 * G8 z)
      ((8 : ℕ) * dz τ₃ ^ (8 - 1) * (1 / 2) * G8 τ₃ + dz τ₃ ^ 8 * deriv G8 τ₃) τ₃ :=
    ((hdzd τ₃).pow 8).mul hGd.hasDerivAt
  have hEq : (G8 ∘ mz) =ᶠ[𝓝 τ₃] (fun z => dz z ^ 8 * G8 z) := by
    filter_upwards [isOpen_U.mem_nhds hτ₃U] with z hz
    exact hFE z hz
  have hL' := hL.congr_of_eventuallyEq hEq.symm
  have huniq := hL'.unique hR
  rw [hG0, mul_zero, zero_add] at huniq
  have hnum1 : (1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) = 1 := by simp only [hdz]; ring
  rw [hnum1] at huniq
  have hD0 : deriv G8 τ₃ = 0 := by
    have hw10 : w ^ 10 = -w := by
      rw [show w ^ 10 = w * (w ^ 3) ^ 3 by ring, hw3]; ring
    have e2 : deriv G8 τ₃ * (1 - w ^ 10) = 0 := by
      have : deriv G8 τ₃ = w ^ 10 * deriv G8 τ₃ := by
        have hw2ne : dz τ₃ ^ 2 ≠ 0 := pow_ne_zero 2 hw0
        calc deriv G8 τ₃
            = deriv G8 τ₃ * (1 / dz τ₃ ^ 2) * dz τ₃ ^ 2 := by
              rw [mul_assoc, one_div_mul_cancel hw2ne, mul_one]
          _ = dz τ₃ ^ 8 * deriv G8 τ₃ * dz τ₃ ^ 2 := by rw [huniq]
          _ = w ^ 10 * deriv G8 τ₃ := by simp only [hw]; ring
      linear_combination this
    rw [hw10] at e2
    have hne : (1 - -w) ≠ 0 := by
      rw [hwv]; intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    exact (mul_eq_zero.mp e2).resolve_right hne
  -- order at least 2
  show 2 ≤ analyticOrderAt G8 τ₃
  by_contra hlt
  push Not at hlt
  have hA := hGa τ₃ hτ₃U
  have hne0 : analyticOrderAt G8 τ₃ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hA, hG0⟩
  have h1 : analyticOrderAt G8 τ₃ = 1 := by
    have h1' : analyticOrderAt G8 τ₃ ≤ 1 := by simpa using hlt
    exact le_antisymm h1' (Order.one_le_iff_ne_zero.mpr hne0)
  obtain ⟨φ, hφ, hφ0, hφe⟩ := (hA.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  have hd1 : HasDerivAt (fun z => (z - τ₃) ^ 1 • φ z) (φ τ₃) τ₃ := by
    have := ((hasDerivAt_id' τ₃).sub_const τ₃).mul hφ.differentiableAt.hasDerivAt
    simp only [pow_one, smul_eq_mul]
    convert this using 1
    ring
  have hd2 : HasDerivAt G8 (φ τ₃) τ₃ := hd1.congr_of_eventuallyEq hφe
  exact hφ0 (hd2.deriv.symm.trans hD0)

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8WeightExact` and `ValenceBoundGammaStar` (proved).** -/
theorem qmDenZeroCM3_of'' (hS : S8Nonzero) (hW : S8WeightExact) (hV : ValenceBoundGammaStar) :
    QMDenZeroCM3 :=
  qmDenZeroCM3_of' hS (s8Weight8_of hW) (s8OrderCM3_of thetaOmegaAnalytic_proof hW) hV

end HSyn.G0Split.FibreQM.PeriodMap

end



/-! ## leaf-fold4: scratch/period-map/part_heavy.lean (declarations already in the chain dropped) -/


/-! ## period-map (heavy part): `PeriodMapGlue` from strictly smaller named Props

Task period-map, 2026-11-13. `PeriodMapGlue Y Φ π` (fibre-qm-period, above, unchanged) is proved
from `R1fpProps Y Φ` (its naturality clause only) and five named Props
(`periodMapGlue_of`); at the leaf's own triple the clause list comes from the bundle
(`periodMapGlue_own`). One of the five, `CMFixedHasCM`, is proved from the textbook leaf T11a
(`cmFixedHasCM_of`), so four glue Props remain. The main
theorem `fibreQMPeriod_periodMap` restates fibre-qm-period's `fibreQMPeriod_main` with
`PeriodMapGlue`, `HauptmodulUnique` and `QMDenZeroCM3` replaced by their named pieces. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

/-- `Q/ℂ` has an `ι`-compatible analytic uniformization with kernel exactly `Λ_τ = ι(𝒪)(τ, 1)ᵀ`
(the hypothesis shape shared by `QMPeriodMap`, `IsR1bFamily` and `PeriodMapGlue`). -/
def HasQMPeriod (Q : QML3 ℂ) (τ : UpperHalfPlane) : Prop :=
  ∃ Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible Q Φu

/-- **GLUE (uniqueness of base change up to isomorphism).** Two base changes of `P/ℚ̄` along the
same `ι : ℚ̄ → ℂ` (`IsBaseChangeOf`) have the same class in `M3 ℂ`.

Why true: both squares are pullbacks of `P.A → Spec ℚ̄` along `Spec ι`, so there is a unique
isomorphism `Q.A ≅ Q'.A` over `Spec ℂ` commuting with the maps to `P.A`; uniqueness of maps into a
pullback makes it commute with `ι(a)` and carry `η(a)` to `η'(a)`; it carries the identity section
`η(0)` to `η'(0)`, so it is a homomorphism (rigidity: Mumford, *Abelian Varieties*, §4 Cor. 1,
UNVERIFIED number). Size: medium (pullback bookkeeping; rigidity is not in Mathlib). -/
def BaseChangeClassUnique : Prop :=
  ∀ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q Q' : QML3 ℂ),
    IsBaseChangeOf ιe P Q → IsBaseChangeOf ιe P Q' → M3.mk Q = M3.mk Q'

/-- **GLUE (R2fp's fibre clause on `ℂ`-points).** Two `ℂ`-points of `Y` have the same `π`-value iff
the underlying QM pairs of their objects are `Aut(𝒪)`-twists of each other (as `R2fpProps` states
for `ℚ̄`-points).

Why true for the genuine `Y₃`: `π` is `Y₃ → X₆ → X₆/W ≅ P¹` (R2, Baba–Granath), `X₆(ℂ)` is the set
of isomorphism classes of QM pairs over `ℂ` (coarse moduli space: bijective on points over
algebraically closed fields; Shimura 1967, Deligne 1971; locators UNVERIFIED) and `W ≅ Aut(𝒪)`
acts by twists. For another triple satisfying the repaired clause lists it follows by qm-pin's
comparison (`Y' ≅ Y₃` compatibly with `Φ` and `π`). It does not follow from `R2fpProps` alone,
which speaks of `ℚ̄`-points: one needs that the two relations are algebraic, or the coarse moduli
property over `ℂ`. Size: medium-large. -/
def PiTwistC (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
    (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔
      ∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q))

/-- **GLUE (Shimura's description of QM tori up to twist).** If `Q, Q'/ℂ` are `ι`-compatibly
`ℂ²/Λ_τ` and `ℂ²/Λ_τ'`, then their QM pairs are `Aut(𝒪)`-twists of each other iff `τ' ∈ Γ*τ`.

Why true (model argument): by GAGA and the `Hom` form of T11a (Mumford §1-2; Birkenhake–Lange
Prop. 1.2.1, UNVERIFIED numbers), an isomorphism `Q.q.twist α ≅ Q'.q` is a linear `T` with
`TΛ_τ = Λ_τ'` and `Tι(α(a)) = ι(a)T`. By Skolem–Noether `α = u⁻¹(·)u` with `u ∈ N_B(𝒪)`, so
`Tι(u)⁻¹` commutes with `ι(B)`, hence is a scalar `c`, and `Λ_τ' = c ι(u)Λ_τ = c ι(𝒪)ι(u)v_τ`. If
`nrd(u) > 0` this says `τ' = ι(u)·τ` (`ι(𝒪)w` determines the line of `w` up to `ι(𝒪^×)`... more
precisely `ι(𝒪)(τ',1)ᵀ = ι(𝒪)(ι(u)τ, 1)ᵀ` iff `τ' ∈ ι(𝒪¹)ι(u)τ`); if `nrd(u) < 0` replace `u` by
`(1+i)u` (`1 + i ∈ 𝒪^×`, reduced norm `−1`, `ι(𝒪)(1+i) = ι(𝒪)`). Conversely `g = ι(u) ∈ Γ*` gives
`T = (cτ + d)⁻¹ ι(u)` and `α = u⁻¹(·)u`. Inputs: the `Hom` version of T11a (the kernel has only the
`End` version) and Skolem–Noether over `ℚ` (the kernel's `TSkolemKW`). Size: medium. -/
def QMTwistLattice : Prop :=
  ∀ (Q Q' : QML3 ℂ) (τ τ' : UpperHalfPlane), HasQMPeriod Q τ → HasQMPeriod Q' τ' →
    ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ')

/-- **GLUE (R2fp's CM clauses on `ℂ`-points).** At a `ℂ`-point whose object has CM by `ℤ[i]`
(resp. `ℤ[ζ₃]`, `ℤ[√−6]`), `π` takes the value `0` (resp. `∞`, `−16/27`).

Why true: a QM abelian surface over `ℂ` with CM is isomorphic (with `ι`) to the base change of one
over `ℚ̄` (CM abelian varieties are defined over `ℚ̄`: Shimura–Taniyama; or: the CM points of `X₆`
are algebraic, Shimura 1967), so with `PiTwistC`, R1fp's naturality and `ToP1.val_comp` the value
is `ι(π(y₀))` for a `ℚ̄`-point `y₀` with CM, which `R2fpProps` gives. Size: medium. -/
def PiCMC (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y : fieldPt ℂ ⟶ Y) (Q : QML3 ℂ), Φ ℂ y = M3.mk Q →
    (HasCM4 Q.q → π.val (K := ℂ) y.left = OnePoint.some 0) ∧
    (HasCM3 Q.q → π.val (K := ℂ) y.left = OnePoint.infty) ∧
    (HasCM24 Q.q → π.val (K := ℂ) y.left = OnePoint.some (-16 / 27))

/-- **GLUE (the CM points of `ℍ`; proved below from T11a, `cmFixedHasCM_of`).** If `Q/ℂ` is
`ι`-compatibly `ℂ²/Λ_τ` and `τ` is fixed by `ι(x)`, `x ∈ 𝒪`, with `x² = −1` (resp.
`x² − x + 1 = 0`, `x² = −6`), then `Q` has CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`).

Why true: `ι(x)v_τ = λv_τ` with `λ = cτ + d`, so `z ↦ λz` preserves `Λ_τ`
(`λι(a)v_τ = ι(ax)v_τ`) and commutes with `ι(𝒪)`; by T11a it is an endomorphism `φ` in the
centralizer of `ι(𝒪)` with `φ² = −1` (resp. ...), since `λ` satisfies the equation of `x`. -/
def CMFixedHasCM : Prop :=
  ∀ (Q : QML3 ℂ) (τ : UpperHalfPlane), HasQMPeriod Q τ →
    ∀ (x : PkgI1.B) (g : GL (Fin 2) ℝ), PkgI1.InO x →
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → g • τ = τ →
      (x * x = -1 → HasCM4 Q.q) ∧ (x * x - x + 1 = 0 → HasCM3 Q.q) ∧
        (x * x = -6 → HasCM24 Q.q)

theorem one_mem_gammaStar : (1 : GL (Fin 2) ℝ) ∈ PkgI1.GammaStar :=
  ⟨1, ⟨1, by simp, by simp, fun z hz => ⟨by rwa [_root_.one_mul, _root_.mul_one], by rwa [_root_.one_mul, _root_.mul_one]⟩⟩,
    by simp [PeriodMap.iota_one], by simp⟩

/-! ### `CMFixedHasCM` from T11a (proved) -/

theorem mem_O_of_inO {x : PkgI1.B} (hx : PkgI1.InO x) : (x : LeafQM.B) ∈ LeafQM.O := by
  obtain ⟨n, rfl⟩ := hx
  show LeafQM.InO _
  exact ⟨n, by ext <;> simp [LeafQM.ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring⟩

theorem oBasis_mem (k : Fin 4) : BPAnalytic.QM.oBasis k ∈ LeafQM.O := by
  show LeafQM.InO _
  fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 1, 0], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩
  · exact ⟨![0, 0, 0, 1], by ext <;> simp [BPAnalytic.QM.oBasis, LeafQM.ofInt]⟩

/-- N5's basis element `b_k` as an element of `𝒪`. -/
def bO (k : Fin 4) : LeafQM.O := ⟨BPAnalytic.QM.oBasis k, oBasis_mem k⟩

/-- An element with `x² = −1`, `x² − x + 1 = 0` or `x² = −6` has positive reduced norm. -/
theorem det_iota_pos (x : PkgI1.B) (h : x * x = -1 ∨ x * x - x + 1 = 0 ∨ x * x = -6) :
    0 < (PkgI1.iota x).det := by
  rw [PeriodMap.det_iota]
  have key : (0 : ℚ) < x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    rcases h with h | h | h
    · have e := congrArg QuaternionAlgebra.re h
      simp at e
      nlinarith [sq_nonneg x.re]
    · have e := congrArg QuaternionAlgebra.re h
      simp at e
      nlinarith [sq_nonneg (x.re - 1 / 4)]
    · have e := congrArg QuaternionAlgebra.re h
      simp [QuaternionAlgebra.re_ofNat] at e
      nlinarith [sq_nonneg x.re]
  exact_mod_cast key

/-- **`CMFixedHasCM` from the textbook leaf T11a (proved).** With `ρ` the analytic representation
(`unif_ring_hom`), `ρ(ι(a))` is the matrix `ι(a)` (`IotaCompatible`), `λ = cτ + d` is the eigenvalue
of `ι(x)` on `(τ, 1)ᵀ`, `z ↦ λz` preserves `Λ_τ` and lifts to `φ ∈ End(A)` (T11a), `φ` commutes with
`ι(𝒪)` and satisfies the equation of `x` because `ρ` is injective (T11a's uniqueness). -/
theorem cmFixedHasCM_of (hR : T11aRiemannEnd) : CMFixedHasCM := by
  intro Q τ ⟨Φu, hU, hc⟩ x g hx hg hgτ
  haveI : DiscreteTopology (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR Q.A Q.surface (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu hU
  have hρι : ∀ a : LeafQM.O, ρ (Q.q.iota a) = Matrix.toLin' (qmMat a) := fun a =>
    lift_unique hU fun z => by rw [hρ, Matrix.toLin'_apply, hc]
  have hinj : ∀ e e', ρ e = ρ e' → e = e' := by
    intro e e' hee
    obtain ⟨f, -, huniq⟩ := (hR Q.A 2 (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu Q.surface hU).1 (ρ e) (hpres e)
    have h1 := huniq e (hρ e)
    have h2 := huniq e' (fun z => by rw [hee]; exact hρ e' z)
    exact h1.trans h2.symm
  set xO : LeafQM.O := ⟨x, mem_O_of_inO hx⟩ with hxO
  set v : Fin 2 → ℂ := ![(τ : ℂ), 1] with hv
  set lam : ℂ := UpperHalfPlane.denom g τ with hlam
  have hΛ : (BPAnalytic.QM.qmLattice τ.im_pos.ne') = Submodule.span ℤ (Set.range (BPAnalytic.QM.qmVec τ)) :=
    BPAnalytic.QM.qmLattice_eq _
  have hvΛ : v ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    rw [hΛ]
    exact Submodule.subset_span ⟨0, BPAnalytic.QM.latVec0 τ⟩
  -- the CM point: `ι(x)(τ, 1)ᵀ = λ(τ, 1)ᵀ`
  have hcases : ∀ hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det,
      ∃ φ ∈ com Q.q, ρ φ = lam • 1 ∧ ρ (Q.q.iota xO) v = lam • v := by
    intro hdet
    have hfix : UpperHalfPlane.num g τ = (τ : ℂ) * UpperHalfPlane.denom g τ := by
      have := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hgτ
      rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet),
        div_eq_iff (UpperHalfPlane.denom_ne_zero g τ)] at this
      exact this
    have hxv : ρ (Q.q.iota xO) v = lam • v := by
      rw [hρι, Matrix.toLin'_apply]
      have hqm : qmMat xO = (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) := by
        rw [hg]; rfl
      rw [hqm]
      ext i; fin_cases i
      · simp only [UpperHalfPlane.num, UpperHalfPlane.denom] at hfix
        simp [hv, hlam, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]
        linear_combination hfix
      · simp [hv, hlam, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]
    have hpresM : ∀ z ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne'), (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) z ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
      have hle : (BPAnalytic.QM.qmLattice τ.im_pos.ne') ≤ (BPAnalytic.QM.qmLattice τ.im_pos.ne').comap ((lam • (1 : Module.End ℂ (Fin 2 → ℂ))).restrictScalars ℤ) := by
        rw [hΛ, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        rw [← hΛ]
        show (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) (BPAnalytic.QM.qmVec τ k) ∈ (BPAnalytic.QM.qmLattice τ.im_pos.ne')
        have h1 : BPAnalytic.QM.qmVec τ k = ρ (Q.q.iota (bO k)) v := by
          rw [hρι, Matrix.toLin'_apply]; rfl
        have h2 : (lam • (1 : Module.End ℂ (Fin 2 → ℂ))) (BPAnalytic.QM.qmVec τ k) =
            ρ (Q.q.iota (bO k * xO)) v := by
          rw [map_mul, map_mul, Module.End.mul_apply, hxv, map_smul, ← h1]
          rfl
        rw [h2]
        exact hpres _ v hvΛ
      exact fun z hz => hle hz
    obtain ⟨φ, hφ, -⟩ := (hR Q.A 2 (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu Q.surface hU).1 _ hpresM
    have hρφ : ρ φ = lam • 1 := lift_unique hU fun z => by rw [hρ]; exact (hφ z).symm
    refine ⟨φ, ?_, hρφ, hxv⟩
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply hinj
    rw [map_mul, map_mul, hρφ, mul_smul_comm, smul_mul_assoc, _root_.mul_one, _root_.one_mul]
  -- the equation satisfied by `λ`
  have hsq : ρ (Q.q.iota xO) v = lam • v → ρ (Q.q.iota (xO * xO)) v = (lam * lam) • v := by
    intro hxv
    rw [map_mul, map_mul, Module.End.mul_apply, hxv, map_smul, hxv, smul_smul]
  have hcoord : ∀ c c' : ℂ, c • v = c' • v → c = c' := by
    intro c c' h
    have := congrFun h 1
    simpa [hv] using this
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨φ, hφc, hρφ, hxv⟩ := hcases (by rw [hg]; exact det_iota_pos x (Or.inl h))
    have hx2 : xO * xO = -1 := Subtype.ext (by simpa using h)
    have hl : lam * lam = -1 := by
      apply hcoord
      rw [← hsq hxv, hx2, map_neg, map_one, map_neg, map_one]
      simp
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_mul, hρφ, map_neg, map_one, smul_mul_smul_comm, _root_.mul_one, hl]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.smul_apply, LinearMap.neg_apply, Module.End.one_apply]
    ext i; simp
  · obtain ⟨φ, hφc, hρφ, hxv⟩ := hcases (by rw [hg]; exact det_iota_pos x (Or.inr (Or.inl h)))
    have hx2 : xO * xO - xO + 1 = 0 := Subtype.ext (by simpa using h)
    have hl : lam * lam - lam + 1 = 0 := by
      have e : ρ (Q.q.iota (xO * xO - xO + 1)) v = (lam * lam - lam + 1) • v := by
        rw [map_add, map_sub, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
          hsq hxv, hxv, map_one, map_one, Module.End.one_apply, add_smul, sub_smul, one_smul]
      rw [hx2, map_zero, map_zero, LinearMap.zero_apply] at e
      apply hcoord
      rw [← e, zero_smul]
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_add, map_sub, map_mul, hρφ, map_one, map_zero, smul_mul_smul_comm, _root_.mul_one]
    rw [show (lam * lam) • (1 : Module.End ℂ (Fin 2 → ℂ)) - lam • 1 + 1 =
      (lam * lam - lam + 1) • 1 by rw [add_smul, sub_smul, one_smul], hl, zero_smul]
  · obtain ⟨φ, hφc, hρφ, hxv⟩ :=
      hcases (by rw [hg]; exact det_iota_pos x (Or.inr (Or.inr h)))
    have hx2 : xO * xO = -6 := Subtype.ext (by push_cast; exact h)
    have e : ρ (Q.q.iota (xO * xO)) v = (-6 : ℂ) • v := by
      rw [hx2, map_neg, map_ofNat, map_neg, map_ofNat, LinearMap.neg_apply, Module.End.ofNat_apply]
      ext i; simp
    have hl : lam * lam = -6 := hcoord _ _ ((hsq hxv).symm.trans e)
    refine ⟨φ, hφc, hinj _ _ ?_⟩
    rw [map_mul, hρφ, smul_mul_smul_comm, _root_.mul_one, hl, map_neg, map_ofNat]
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.smul_apply, LinearMap.neg_apply, Module.End.ofNat_apply, Module.End.one_apply]
    ext i; simp

/-- **`PeriodMapGlue` from strictly smaller named Props (proved).** Only the naturality clause of
`R1fpProps` is used. -/
theorem periodMapGlue_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hBC : BaseChangeClassUnique) (hPT : PiTwistC Y Φ π)
    (hTL : QMTwistLattice) (hCM : PiCMC Y Φ π) (hCF : CMFixedHasCM) :
    PeriodMapGlue Y Φ π := by
  intro yτ hfam
  have hobj : ∀ τ, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧ HasQMPeriod P τ := fun τ => by
    obtain ⟨P, hP, Φu, hU, hc⟩ := hfam.1 τ
    exact ⟨P, hP, Φu, hU, hc⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro τ τ'
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    obtain ⟨P', hP', hPτ'⟩ := hobj τ'
    exact (hPT _ _ P P' hP hP').trans (hTL P P' τ τ' hPτ hPτ')
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).1 ((hCF P τ hPτ x g hx hg hgτ).1 hxx)
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).2.1 ((hCF P τ hPτ x g hx hg hgτ).2.1 hxx)
  · intro x hx hxx g hg τ hgτ
    obtain ⟨P, hP, hPτ⟩ := hobj τ
    exact (hCM _ P hP).2.2 ((hCF P τ hPτ x g hx hg hgτ).2.2 hxx)
  · intro y P hP ιe Q hQ τ Φu hΦu hc
    obtain ⟨Pτ, hPτ, hPer⟩ := hobj τ
    obtain ⟨Q', hQ', hBC'⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y P hP
    have hQQ : M3.mk Q' = M3.mk Q := hBC ιe P Q' Q hBC' hQ
    have hval := ToP1.val_comp π ιe y.left
    have hleft : (fieldMap ιe.toRatAlgHom ≫ y).left =
        Spec.map (CommRingCat.ofHom ιe) ≫ y.left := rfl
    rw [← hval, ← hleft]
    apply (hPT (yτ τ) (fieldMap ιe.toRatAlgHom ≫ y) Pτ Q hPτ (hQ'.trans hQQ)).mpr
    exact (hTL Pτ Q τ τ hPer ⟨Φu, hΦu, hc⟩).mpr ⟨1, one_mem_gammaStar, one_smul _ _⟩


/-! ### `PiCMC` from `PiTwistC`, R1fp, R2fp and the descent of CM objects (proved) -/

/-- **LEAF candidate (QM abelian surfaces with CM are defined over `ℚ̄`).** A level-3 QM surface
`Q/ℂ` with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) is, as a QM pair, isomorphic to the base change
along some `ι : ℚ̄ → ℂ` of a level-3 QM surface `P/ℚ̄` with the same CM.

Sources: Shimura–Taniyama, *Complex multiplication of abelian varieties* (1961), and Shimura 1967:
abelian varieties with CM are defined over `ℚ̄` (a CM point of `X₆` is algebraic; its fibre has a
model over the field of moduli); the CM descends because endomorphisms of `P_ℂ` come from `P`
(the kernel's textbook leaf T11b, `Hom_ℚ̄ = Hom_ℂ`); the level structure also descends because
`A[3] ⊆ A(ℚ̄)` (locators UNVERIFIED). A consequence of those published statements; size of the glue
around them: small-medium. -/
def CMDescends : Prop :=
  ∀ Q : QML3 ℂ,
    (HasCM4 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM4 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM3 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM3 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM24 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM24 P.q ∧ Nonempty (QMIso Q.q Q'.q))

/-- A QM isomorphism is one for the trivial twist. -/
def qmIsoTwistRefl {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (e : QMIso q q') :
    QMIso (q.twist (RingEquiv.refl LeafQM.O)) q' where
  φ := e.φ
  ψ := e.ψ
  left := e.left
  right := e.right
  equivariant a := e.equivariant a

/-- The value of `π` at a `ℂ`-point whose QM pair comes from a `ℚ̄`-point (proved). -/
theorem pi_of_descends (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hBC : BaseChangeClassUnique) (hPT : PiTwistC Y Φ π)
    (y : fieldPt ℂ ⟶ Y) (Q : QML3 ℂ) (hQ : Φ ℂ y = M3.mk Q) (ιe : Qbar →+* ℂ) (P : QML3 Qbar)
    (Q' : QML3 ℂ) (hBCQ : IsBaseChangeOf ιe P Q') (hiso : Nonempty (QMIso Q.q Q'.q)) :
    π.val (K := ℂ) y.left = (π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P)).left).map ιe := by
  set y₀ := (Φ Qbar).symm (M3.mk P) with hy₀
  have hP : Φ Qbar y₀ = M3.mk P := by rw [hy₀, Equiv.apply_symm_apply]
  obtain ⟨Q'', hQ'', hBC''⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y₀ P hP
  have hQQ : M3.mk Q'' = M3.mk Q' := hBC ιe P Q'' Q' hBC'' hBCQ
  have hval := ToP1.val_comp π ιe y₀.left
  have hleft : (fieldMap ιe.toRatAlgHom ≫ y₀).left =
      Spec.map (CommRingCat.ofHom ιe) ≫ y₀.left := rfl
  rw [← hval, ← hleft]
  obtain ⟨e⟩ := hiso
  exact (hPT y (fieldMap ιe.toRatAlgHom ≫ y₀) Q Q' hQ (hQ''.trans hQQ)).mpr
    ⟨RingEquiv.refl LeafQM.O, ⟨qmIsoTwistRefl e⟩⟩

/-- **`PiCMC` from `PiTwistC`, R1fp naturality, R2fp's CM clauses, `BaseChangeClassUnique` and
`CMDescends` (proved).** -/
theorem piCMC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC Y Φ π) (hD : CMDescends) : PiCMC Y Φ π := by
  intro y Q hQ
  have hP : ∀ P : QML3 Qbar, Φ Qbar ((Φ Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => Equiv.apply_symm_apply _ _
  refine ⟨fun hcm => ?_, fun hcm => ?_, fun hcm => ?_⟩
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).1 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.1 hPcm]
    simp
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).2.1 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.2.1 hPcm]
    rfl
  · obtain ⟨ιe, P, Q', hB, hPcm, hiso⟩ := (hD Q).2.2 hcm
    rw [pi_of_descends Y Φ π h1 hBC hPT y Q hQ ιe P Q' hB hiso,
      (h2 _ _ P P (hP P) (hP P)).2.2.2 hPcm]
    simp [map_ofNat]

/-- **`PeriodMapGlue` at the leaf's own triple (proved).** -/
theorem periodMapGlue_own (h : R1R2fp) (hBC : BaseChangeClassUnique)
    (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h)) (hTL : QMTwistLattice)
    (hCM : PiCMC (ownY h) (ownΦ h) (ownπ h)) (hCF : CMFixedHasCM) :
    PeriodMapGlue (ownY h) (ownΦ h) (ownπ h) :=
  periodMapGlue_of _ _ _ (own_spec h).1 hBC hPT hTL hCM hCF

/-- **`FibreQMPeriod` with the three targets replaced by their named pieces (proved).** Leaves:
`R1R2fp`, `PkgI1.QMHauptmodul`, T35, T11a, `QMClassNumberOne`, `R1bFamily`,
`ValenceBoundGammaStar`, `CMDescends` (leaf candidate). Glue: `Pin.MobiusGlue` (proved by
mobius-glue), `BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`, `S8Nonzero`,
`SphereFactorAffine`, `S8WeightExact`, `CPtsTransport`. -/
theorem fibreQMPeriod_periodMap (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hBC : BaseChangeClassUnique) (hPT : PiTwistC (ownY h) (ownΦ h) (ownπ h))
    (hTL : QMTwistLattice) (hD : CMDescends)
    (hS : PeriodMap.S8Nonzero)
    (hSF : PeriodMap.SphereFactorAffine) (hW : PeriodMap.S8WeightExact)
    (hV : PeriodMap.ValenceBoundGammaStar)
    (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main h hM hH hE hR11 hCN hR
    (periodMapGlue_own h hBC hPT hTL
      (piCMC_of _ _ _ (own_spec h).1 (own_spec h).2.2 hBC hPT hD) (cmFixedHasCM_of hR11))
    (PeriodMap.hauptmodulUnique_of' hS hSF) (PeriodMap.qmDenZeroCM3_of'' hS hW hV) hCP

end HSyn.G0Split.FibreQM.PeriodMapH

end



/-! ## leaf-fold4: scratch/period-glue/BCU.lean (declarations already in the chain dropped) -/

/-! # period-glue: `BaseChangeClassUnique` proved

Task period-glue, 2026-11-13. `PGBase` contains, verbatim, period-map's statement
`HSyn.G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique` (from `scratch/period-map/part_heavy.lean`)
and everything it depends on (fibre-qm-period's `QML3`, `IsBaseChangeOf`, `M3`). This file proves
it from Mathlib only. The one non-formal input named in period-map's docstring, rigidity (a pointed
morphism of abelian varieties is a homomorphism, Mumford §4 Cor. 1), is proved from Mathlib in
mul-rigidity (`scratch/mul-rigidity/Rigidity.lean`, copied verbatim below as `MulRigidity`).

Proof. Both base changes `Q, Q'` of `P` along `ι` are pullbacks of `P.A → Spec ℚ̄` along
`Spec ι`, so the pullback property of `Q'` gives `θ : Q.A → Q'.A` over `Spec ℂ` with
`θ ≫ g' = g`; the same for `θ'`. Every compatibility is an equality of maps into the pullback
`Q'.A`, checked after composing with `g'` (`eq_of_comp`). Level clause at `a = 0` gives that `θ`
keeps the identity section, so rigidity makes `θ` a homomorphism. -/

/-! ## Rigidity (copied verbatim from `scratch/mul-rigidity/Rigidity.lean`, namespace renamed
`PeriodGlue.MulRigidity`) -/

noncomputable section

namespace PeriodGlue.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm


end PeriodGlue.MulRigidity

/-! ## `BaseChangeClassUnique` -/

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

section BC

variable {ιe : Qbar →+* ℂ} {P : QML3 Qbar} {Q Q' : QML3 ℂ}

/-- Maps into a base change are determined by their composite with the map to `P.A`. -/
theorem eq_of_comp {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    {T : Over (Spec (CommRingCat.of ℂ))} {u v : T ⟶ Q'.A.X} (h : u.left ≫ g' = v.left ≫ g') :
    u = v := by
  ext1
  exact hg'.hom_ext h (by rw [Over.w u, Over.w v])

/-- The comparison morphism `Q.A → Q'.A` over `Spec ℂ`. -/
def cmp {g : Q.A.X.left ⟶ P.A.X.left} {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg : IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe))) :
    Q.A.X ⟶ Q'.A.X :=
  Over.homMk (hg'.lift g Q.A.X.hom hg.w) (hg'.lift_snd _ _ _)

theorem cmp_left_comp {g : Q.A.X.left ⟶ P.A.X.left} {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg : IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe))) :
    (cmp hg hg').left ≫ g' = g :=
  hg'.lift_fst _ _ _

/-- `Spec ℂ → Spec ℂ` of `algebraMap ℂ ℂ` is the identity. -/
theorem ptObj_hom_self : (PkgI3.AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem ptObj_hom_self' : (PkgI3.AbVar.ptObj (K := Qbar) Qbar).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap Qbar Qbar)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The identity section of `Q` composed with `g` (from the level clause at `a = 0`). -/
theorem eta_comp {g : Q.A.X.left ⟶ P.A.X.left}
    (hl : ∀ a : LeafQM.O, (Additive.toMul (Q.e.eta a)).left ≫ g =
        Spec.map (CommRingCat.ofHom ιe) ≫ (Additive.toMul (P.e.eta a)).left) :
    η[Q.A.X].left ≫ g = Spec.map (CommRingCat.ofHom ιe) ≫ η[P.A.X].left := by
  have h0 := hl 0
  rw [Q.e.eta.map_zero, P.e.eta.map_zero] at h0
  change ((1 : PkgI3.AbVar.Pt ℂ Q.A)).left ≫ g =
    Spec.map (CommRingCat.ofHom ιe) ≫ ((1 : PkgI3.AbVar.Pt Qbar P.A)).left at h0
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ptObj_hom_self, ptObj_hom_self'] at h0
  erw [Category.id_comp, Category.id_comp] at h0
  exact h0

end BC

theorem baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique := by
  intro ιe P Q Q' ⟨g, hg, hι, hl⟩ ⟨g', hg', hι', hl'⟩
  set θ := cmp hg hg' with hθ
  set θ' := cmp hg' hg with hθ'
  have hθg : θ.left ≫ g' = g := cmp_left_comp hg hg'
  have hθg' : θ'.left ≫ g = g' := cmp_left_comp hg' hg
  -- `θ` and `θ'` keep the identity section
  have hη : η[Q.A.X] ≫ θ = η[Q'.A.X] := eq_of_comp hg' (by
    rw [Over.comp_left, Category.assoc, hθg, eta_comp hl, eta_comp hl'])
  have hη' : η[Q'.A.X] ≫ θ' = η[Q.A.X] := eq_of_comp hg (by
    rw [Over.comp_left, Category.assoc, hθg', eta_comp hl, eta_comp hl'])
  have : IsMonHom θ :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q.A.X Q'.A.X θ hη
  have : IsMonHom θ' :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X Q.A.X θ' hη'
  refine Quotient.sound ⟨{
    φ := PkgI3.AbVar.Hom.mk' θ
    ψ := PkgI3.AbVar.Hom.mk' θ'
    left := ?_
    right := ?_
    equivariant := ?_
    level := ?_ }⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg (by rw [Over.comp_left, Category.assoc, hθg', hθg, Over.id_left,
      Category.id_comp])
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg' (by rw [Over.comp_left, Category.assoc, hθg, hθg', Over.id_left,
      Category.id_comp])
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hθg, hι' a,
        ← Category.assoc, hθg, hι a])
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    have hx : Additive.toMul (Q.e.eta a) ≫ θ = Additive.toMul (Q'.e.eta a) :=
      eq_of_comp hg' (by rw [Over.comp_left, Category.assoc, hθg, hl a, hl' a])
    rw [hx]; rfl

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/QMTwist.lean (declarations already in the chain dropped) -/

/-! # period-glue: `QMTwistLattice` from the `Hom` form of T11a and a lattice statement

Task period-glue, 2026-11-13. `QMTwistLattice` (period-map, `PGBase`, unchanged) is proved from
* `T11aRiemannHom` (**LEAF**, textbook: the `Hom` form of T11a), and
* `QMLatticeTwistAlg` (**GLUE**, pure linear algebra over `ℚ`/`ℂ`: the twist relation on lattices
  is the `Γ*`-relation on `ℍ`),
by `qmTwistLattice_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **LEAF (T11a, `Hom` form; textbook).** For abelian varieties `A, A'/ℂ` of dimension `g` with
analytic uniformizations `Φ : ℂ^g → A(ℂ)`, `Φ' : ℂ^g → A'(ℂ)` with kernels `Λ, Λ'`: every
`ℂ`-linear `M` with `MΛ ⊆ Λ'` is the analytic representation of exactly one homomorphism
`f : A → A'` (`Φ'(Mz) = f(Φ z)`), and every homomorphism has an analytic representation.

Sources: for complex tori, `Hom(ℂ^g/Λ, ℂ^g/Λ') = {M : MΛ ⊆ Λ'}` (Mumford, *Abelian Varieties*,
§1, the analytic description of homomorphisms; Birkenhake–Lange, *Complex Abelian Varieties*,
Prop. 1.2.1; locators UNVERIFIED), and every holomorphic homomorphism of abelian varieties is
algebraic (GAGA: Serre, *Géométrie algébrique et géométrie analytique*, 1956, Thm. 3 / Cor.;
Mumford §1 / §4; UNVERIFIED). The kernel's `T11aRiemannEnd` is the case `A = A'`, `Φ = Φ'`
(this statement is the same text with `Hom A A'` in place of `End A`). -/
def T11aRiemannHom : Prop :=
  ∀ (A A' : PkgI3.AbVar ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (Φ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → A'.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) Λ Φ → IsUniformization (RingHom.id ℂ) Λ' Φ' →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ') →
      ∃! f : PkgI3.AbVar.Hom A A', ∀ z, Φ' (M z) = Φ z ≫ f.hom) ∧
    (∀ f : PkgI3.AbVar.Hom A A', ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ z, Φ' (M z) = Φ z ≫ f.hom)

/-- `T11aRiemannEnd` is the special case `A = A'` of `T11aRiemannHom` (proved). -/
theorem t11aRiemannEnd_of_hom (h : T11aRiemannHom) : T11aRiemannEnd :=
  fun A g Λ Φ hA hU => h A A g Λ Λ Φ Φ hA hA hU hU

/-- **GLUE (pure algebra: twists of QM lattices).** For `τ, τ' ∈ ℍ`: there are `α ∈ Aut(𝒪)` and
a `ℂ`-linear automorphism `M` of `ℂ²` with `MΛ_τ = Λ_τ'` and `M ∘ ι(α(a)) = ι(a) ∘ M` for all
`a ∈ 𝒪` iff `τ' ∈ Γ*τ`.

Why true (model argument, Shimura 1967 §1-2 for the general statement):
(⇐) `g = ι(u) ∈ Γ*` with `u ∈ N_B(𝒪)`, `nrd u > 0`: take `M = (cτ + d)⁻¹ι(u)` and
`α(a) = u⁻¹au` (in `Aut(𝒪)` because `u` normalizes `𝒪`); then
`MΛ_τ = (cτ+d)⁻¹ι(u𝒪u⁻¹)ι(u)v_τ = ι(𝒪)v_τ' = Λ_τ'`.
(⇒) `α` extends to a `ℚ`-algebra automorphism of `B = 𝒪 ⊗ ℚ`, inner by Skolem–Noether (the
kernel's `TSkolemKW.leafSkolemNoether`): `α(a) = u⁻¹au`, `u ∈ N_B(𝒪)`. Then `M ι(u)⁻¹`
commutes with `ι(B)`, which spans `M₂(ℂ)`, so `M = c ι(u)`, `c ∈ ℂ^×`. From `MΛ_τ = Λ_τ'`:
`v_τ' = c ι(x)v_τ` for some `x ∈ 𝒪u`, and `ι(𝒪)ι(x)v_τ = ι(𝒪)ι(u)v_τ`; `b ↦ ι(b)v_τ` is
injective on `B` (`ι(b)` is invertible for `b ≠ 0`, `B` a division algebra, and `v_τ ≠ 0`), so
`𝒪x = 𝒪u`, `x = eu` with `e ∈ 𝒪^×`, so `x ∈ N_B(𝒪)`; `ι(x)τ = τ' ∈ ℍ` forces
`det ι(x) = nrd x > 0`, so `g = ι(x) ∈ Γ*` and `gτ = τ'`. Size: medium (Skolem–Noether is
proved in the kernel; the rest is `2 × 2` linear algebra over `ℚ(√2)`). -/
def QMLatticeTwistAlg : Prop :=
  ∀ τ τ' : UpperHalfPlane,
    ((∃ α : LeafQM.O ≃+* LeafQM.O, ∃ M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
        (∀ z, z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
          M z ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne') ∧
        ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z)) ↔
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ')

/-- A homomorphism keeps the identity point. -/
theorem one_comp_hom {A A' : PkgI3.AbVar ℂ} (f : PkgI3.AbVar.Hom A A') :
    (1 : CPts A (RingHom.id ℂ)) ≫ f.hom = 1 := MonObj.one_comp f.hom

/-- Points of the kernel: a map `M` lifting a homomorphism sends `Λ` into `Λ'`. -/
theorem lift_maps_lattice {A A' : PkgI3.AbVar ℂ} {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)}
    {Φ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)} {Φ' : (Fin 2 → ℂ) → CPts A' (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (hU' : IsUniformization (RingHom.id ℂ) Λ' Φ')
    {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} {f : PkgI3.AbVar.Hom A A'}
    (hM : ∀ z, Φ' (M z) = Φ z ≫ f.hom) : ∀ z ∈ Λ, M z ∈ Λ' := by
  intro z hz
  rw [← hU'.2.1, hM, (hU.2.1 z).mpr hz, one_comp_hom]

theorem qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice := by
  intro Q Q' τ τ' ⟨Φ, hU, hc⟩ ⟨Φ', hU', hc'⟩
  set Λ := BPAnalytic.QM.qmLattice τ.im_pos.ne' with hΛ
  set Λ' := BPAnalytic.QM.qmLattice τ'.im_pos.ne' with hΛ'
  have : DiscreteTopology Λ := by rw [hΛ]; unfold BPAnalytic.QM.qmLattice; infer_instance
  have : DiscreteTopology Λ' := by rw [hΛ']; unfold BPAnalytic.QM.qmLattice; infer_instance
  have H := hH Q.A Q'.A 2 Λ Λ' Φ Φ' Q.surface Q'.surface hU hU'
  have H' := hH Q'.A Q.A 2 Λ' Λ Φ' Φ Q'.surface Q.surface hU' hU
  have HQ := hH Q.A Q.A 2 Λ Λ Φ Φ Q.surface Q.surface hU hU
  have HQ' := hH Q'.A Q'.A 2 Λ' Λ' Φ' Φ' Q'.surface Q'.surface hU' hU'
  rw [← hA τ τ']
  constructor
  · rintro ⟨α, ⟨e⟩⟩
    obtain ⟨M, hM⟩ := H.2 e.φ
    obtain ⟨N, hN⟩ := H'.2 e.ψ
    have hNM : N ∘ₗ M = LinearMap.id := lift_unique hU fun z => by
      rw [LinearMap.comp_apply, hN, hM, Category.assoc, e.left, Category.comp_id,
        LinearMap.id_apply]
    have hMN : M ∘ₗ N = LinearMap.id := lift_unique hU' fun z => by
      rw [LinearMap.comp_apply, hM, hN, Category.assoc, e.right, Category.comp_id,
        LinearMap.id_apply]
    refine ⟨α, LinearEquiv.ofLinearMap M N hMN hNM, fun z => ⟨fun hz => ?_, fun hz => ?_⟩,
      fun a z => ?_⟩
    · exact lift_maps_lattice hU hU' hM z hz
    · have := lift_maps_lattice hU' hU hN _ hz
      simpa [LinearEquiv.coe_ofLinearMap, ← LinearMap.comp_apply, hNM] using this
    · show M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z)
      have key : M ∘ₗ Matrix.toLin' (qmMat (α a)) = Matrix.toLin' (qmMat a) ∘ₗ M :=
        lift_unique hU' fun w => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
            Matrix.toLin'_apply, hM, hc, hc', hM, Category.assoc, Category.assoc]
          congr 1
          exact e.equivariant a
      have := LinearMap.congr_fun key z
      simpa [Matrix.toLin'_apply] using this
  · rintro ⟨α, M, hML, hMeq⟩
    have hMΛ : ∀ z ∈ Λ, (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ Λ' :=
      fun z hz => (hML z).mp hz
    have hNΛ : ∀ z ∈ Λ', (M.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ Λ := fun z hz => by
      rw [hML]; simpa using hz
    obtain ⟨φ, hφ, -⟩ := H.1 M hMΛ
    obtain ⟨ψ, hψ, -⟩ := H'.1 M.symm hNΛ
    have hφ' : ∀ z, Φ' (M z) = Φ z ≫ φ.hom := hφ
    -- uniqueness of the endomorphism lifting `id`
    obtain ⟨one, -, hone⟩ := HQ.1 LinearMap.id (fun z hz => hz)
    obtain ⟨one', -, hone'⟩ := HQ'.1 LinearMap.id (fun z hz => hz)
    have hleft : φ.hom ≫ ψ.hom = 𝟙 _ := by
      have h1 := hone (PkgI3.AbVar.Hom.mk' (φ.hom ≫ ψ.hom)) fun z => by
        rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hφ, ← hψ]; simp
      have h2 := hone 1 fun z => by
        change Φ z = Φ z ≫ 𝟙 _
        rw [Category.comp_id]
      exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
    have hright : ψ.hom ≫ φ.hom = 𝟙 _ := by
      have h1 := hone' (PkgI3.AbVar.Hom.mk' (ψ.hom ≫ φ.hom)) fun z => by
        rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hψ, ← hφ]; simp
      have h2 := hone' 1 fun z => by
        change Φ' z = Φ' z ≫ 𝟙 _
        rw [Category.comp_id]
      exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
    refine ⟨α, ⟨{ φ := φ, ψ := ψ, left := hleft, right := hright, equivariant := ?_ }⟩⟩
    intro a
    -- both sides lift `M ∘ ι(α a) = ι(a) ∘ M`
    have hlat : ∀ z ∈ Λ, (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
        ((qmMat (α a)).mulVec z) ∈ Λ' := by
      intro z hz
      apply hMΛ
      have := lift_maps_lattice hU hU (f := Q.q.iota (α a))
        (M := Matrix.toLin' (qmMat (α a))) (fun w => by rw [Matrix.toLin'_apply, hc]) z hz
      simpa [Matrix.toLin'_apply] using this
    obtain ⟨f, -, hf⟩ := H.1 ((M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) ∘ₗ
      Matrix.toLin' (qmMat (α a))) (fun z hz => by simpa [Matrix.toLin'_apply] using hlat z hz)
    have e1 := hf (PkgI3.AbVar.Hom.mk' ((Q.q.iota (α a)).hom ≫ φ.hom)) fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, Matrix.toLin'_apply, hφ, hc,
        Category.assoc]
    have e2 := hf (PkgI3.AbVar.Hom.mk' (φ.hom ≫ (Q'.q.iota a).hom)) fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, Matrix.toLin'_apply]
      change Φ' (M ((qmMat (α a)).mulVec z)) = _
      rw [hMeq, hc', hφ', Category.assoc]
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)

/-! ## `QMLatticeTwistAlg`, direction `τ' ∈ Γ*τ ⇒ twist` (proved) -/

open scoped Matrix

/-- `ι(x)` as a complex matrix. -/
def cM (x : LeafQM.B) : Matrix (Fin 2) (Fin 2) ℂ := (BPAnalytic.QM.iota x).map (fun r : ℝ => (r : ℂ))

theorem qmMat_eq (a : LeafQM.O) : qmMat a = cM a := rfl

theorem cM_mul (x y : LeafQM.B) : cM (x * y) = cM x * cM y := by
  unfold cM
  have : BPAnalytic.QM.iota (x * y) = BPAnalytic.QM.iota x * BPAnalytic.QM.iota y :=
    PeriodMap.iota_mul x y
  rw [this]
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem cM_one : cM 1 = 1 := by
  unfold cM
  have : BPAnalytic.QM.iota 1 = 1 := PeriodMap.iota_one
  rw [this]
  exact Matrix.map_one _ (by simp) (by simp)

theorem latVec_eq (b : LeafQM.B) (τ : ℂ) : BPAnalytic.QM.latVec b τ = cM b *ᵥ ![τ, 1] := rfl

theorem latVec_mul (x y : LeafQM.B) (τ : ℂ) :
    BPAnalytic.QM.latVec (x * y) τ = cM x *ᵥ BPAnalytic.QM.latVec y τ := by
  rw [latVec_eq, latVec_eq, cM_mul, Matrix.mulVec_mulVec]

theorem latVec_ofInt (c : Fin 4 → ℤ) (τ : ℂ) :
    ∑ i, c i • BPAnalytic.QM.qmVec τ i = BPAnalytic.QM.latVec (LeafQM.ofInt c) τ := by
  ext k
  fin_cases k <;>
    simp [BPAnalytic.QM.qmVec, BPAnalytic.QM.latVec, BPAnalytic.QM.iota, BPAnalytic.QM.oBasis,
      LeafQM.ofInt, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Fin.sum_univ_four, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] <;> ring

theorem mem_qmLattice_iff {τ : ℂ} (hτ : τ.im ≠ 0) (z : Fin 2 → ℂ) :
    z ∈ BPAnalytic.QM.qmLattice hτ ↔ ∃ b : LeafQM.B, b ∈ LeafQM.O ∧ z = BPAnalytic.QM.latVec b τ := by
  rw [BPAnalytic.QM.qmLattice_eq, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨LeafQM.ofInt c, ⟨c, rfl⟩, by rw [← hc, latVec_ofInt]⟩
  · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, latVec_ofInt c τ⟩

theorem inO_iff (x : LeafQM.B) : PkgI1.InO x ↔ x ∈ LeafQM.O := by
  refine ⟨fun h => mem_O_of_inO h, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn]
  ext <;> simp [LeafQM.ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- **`QMLatticeTwistAlg`, (⇐) (proved).** -/
theorem qmLatticeTwistAlg_mpr (τ τ' : UpperHalfPlane) (hg : ∃ g ∈ PkgI1.GammaStar, g • τ = τ') :
    ∃ α : LeafQM.O ≃+* LeafQM.O, ∃ M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ z, z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
        M z ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne') ∧
      ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z) := by
  obtain ⟨g, ⟨x, ⟨y, hxy, hyx, hN⟩, hgx, hdet⟩, hgτ⟩ := hg
  have hN' : ∀ a : LeafQM.B, a ∈ LeafQM.O → y * a * x ∈ LeafQM.O ∧ x * a * y ∈ LeafQM.O := by
    intro a ha
    obtain ⟨h1, h2⟩ := hN a ((inO_iff a).mpr ha)
    exact ⟨(inO_iff _).mp h2, (inO_iff _).mp h1⟩
  have key1 : ∀ a : LeafQM.B, x * (y * a * x) * y = a := fun a => by
    calc x * (y * a * x) * y = (x * y) * a * (x * y) := by noncomm_ring
      _ = a := by rw [hxy, _root_.one_mul, _root_.mul_one]
  have key2 : ∀ a : LeafQM.B, y * (x * a * y) * x = a := fun a => by
    calc y * (x * a * y) * x = (y * x) * a * (y * x) := by noncomm_ring
      _ = a := by rw [hyx, _root_.one_mul, _root_.mul_one]
  let α : LeafQM.O ≃+* LeafQM.O :=
    { toFun := fun a => ⟨y * a * x, (hN' a a.2).1⟩
      invFun := fun a => ⟨x * a * y, (hN' a a.2).2⟩
      left_inv := fun a => Subtype.ext (key1 a)
      right_inv := fun a => Subtype.ext (key2 a)
      map_mul' := fun a b => Subtype.ext (by
        change y * ((a : LeafQM.B) * b) * x = (y * a * x) * (y * b * x)
        calc y * ((a : LeafQM.B) * b) * x = y * a * 1 * b * x := by noncomm_ring
          _ = y * a * (x * y) * b * x := by rw [hxy]
          _ = (y * a * x) * (y * b * x) := by noncomm_ring)
      map_add' := fun a b => Subtype.ext (by
        change y * ((a : LeafQM.B) + b) * x = y * a * x + y * b * x
        noncomm_ring) }
  have hα : ∀ a : LeafQM.O, ((α a : LeafQM.O) : LeafQM.B) = y * a * x := fun a => rfl
  have hgM : (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) = cM x := by
    rw [hgx]; rfl
  set c := UpperHalfPlane.denom g τ with hc
  have hc0 : c ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  have hXY : cM x * cM y = 1 := by rw [← cM_mul, hxy, cM_one]
  have hYX : cM y * cM x = 1 := by rw [← cM_mul, hyx, cM_one]
  let Mf : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := c⁻¹ • Matrix.toLin' (cM x)
  let Mg : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := c • Matrix.toLin' (cM y)
  have h1 : Mf ∘ₗ Mg = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    simp only [Mf, Mg, LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Mg ∘ₗ Mf = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    simp only [Mf, Mg, LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec,
      smul_smul, mul_inv_cancel₀ hc0, one_smul]
  let M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) := LinearEquiv.ofLinearMap Mf Mg h1 h2
  have hM : ∀ z, M z = c⁻¹ • (cM x *ᵥ z) := fun z => rfl
  -- `ι(x)(τ, 1)ᵀ = c (τ', 1)ᵀ`
  have hτ' : ((τ' : UpperHalfPlane) : ℂ) = UpperHalfPlane.num g τ / c := by
    rw [← hgτ]
    exact UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet) τ
  have hv : cM x *ᵥ ![(τ : ℂ), 1] = c • ![((τ' : UpperHalfPlane) : ℂ), 1] := by
    rw [← hgM, hτ']
    ext k
    fin_cases k
    · have hc0' : (τ : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) +
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
        have : ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * τ +
            ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := hc0
        rwa [mul_comm] at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.num, hc,
        UpperHalfPlane.denom]
      field_simp
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, UpperHalfPlane.denom]
  have hlat : ∀ b : LeafQM.B, M (BPAnalytic.QM.latVec b τ) =
      BPAnalytic.QM.latVec (x * b * y) τ' := by
    intro b
    rw [hM, ← latVec_mul]
    have : x * b = (x * b * y) * x := by
      calc x * b = x * b * 1 := (_root_.mul_one _).symm
        _ = x * b * (y * x) := by rw [hyx]
        _ = (x * b * y) * x := by noncomm_ring
    conv_lhs => rw [this]
    rw [latVec_mul, latVec_eq x, hv, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0,
      one_smul, ← latVec_eq]
  refine ⟨α, M, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun a z => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := (mem_qmLattice_iff _ z).mp hz
    rw [hlat]
    exact (mem_qmLattice_iff _ _).mpr ⟨_, (hN' b hb).2, rfl⟩
  · obtain ⟨b', hb', hzb⟩ := (mem_qmLattice_iff _ _).mp hz
    have : z = BPAnalytic.QM.latVec (y * b' * x) τ := by
      apply M.injective
      rw [hzb, hlat, key1]
    rw [this]
    exact (mem_qmLattice_iff _ _).mpr ⟨_, (hN' b' hb').1, rfl⟩
  · have e : x * (y * (a : LeafQM.B) * x) = a * x := by
      calc x * (y * (a : LeafQM.B) * x) = (x * y) * a * x := by noncomm_ring
        _ = a * x := by rw [hxy, _root_.one_mul]
    rw [hM, hM, qmMat_eq, qmMat_eq, hα, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← cM_mul, ← cM_mul, e]

end HSyn.G0Split.FibreQM.PeriodGlue

/-! ## Extension of `α ∈ Aut 𝒪` to `B` (copied verbatim from mobius-glue,
`scratch/mobius-glue/MobiusGlue.lean` §7, namespace `PeriodGlue.AutOExt`) -/

namespace PeriodGlue.AutOExt

open LeafQM

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-- **Every automorphism of `𝒪` is inner (proved from Skolem–Noether).** `LeafSkolemNoether` is
the kernel's `GlueDescent.LeafSkolemNoether` (copied verbatim in `PGBase`), which the kernel proves
(`TSkolemKW.leafSkolemNoether`, `ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`; it cannot be
imported next to the scratch copy). -/
theorem autO_inner (hSN : GlueDescent.LeafSkolemNoether) (α : O ≃+* O) :
    ∃ u : Bˣ, ∀ a : O, ((α a : O) : B) = u * a * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner hSN (extAlgEquiv α)
  exact ⟨u, fun a => by rw [← extFun_coe α a]; exact hu a⟩

end PeriodGlue.AutOExt

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open scoped Matrix
open _root_.ZInQ ZInQ LeafQM.AV HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

theorem cM_apply (x : LeafQM.B) : cM x =
    !![((x.re : ℝ) : ℂ) + (x.imI : ℝ) * (√2 : ℝ), -3 * ((x.imJ : ℝ) : ℂ) - 3 * (√2 : ℝ) * (x.imK : ℝ);
       ((x.imJ : ℝ) : ℂ) - (√2 : ℝ) * (x.imK : ℝ), ((x.re : ℝ) : ℂ) - (x.imI : ℝ) * (√2 : ℝ)] := by
  unfold cM
  have : BPAnalytic.QM.iota x = PkgI1.iota x := rfl
  rw [this, PeriodMap.iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `b ↦ ι(b)(τ, 1)ᵀ` is injective on `B` for `τ ∉ ℝ`. -/
theorem latVec_eq_zero {c : LeafQM.B} {τ : ℂ} (hτ : τ.im ≠ 0)
    (h : BPAnalytic.QM.latVec c τ = 0) : c = 0 := by
  rw [latVec_eq, cM_apply] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have h0r := congrArg Complex.re h0
  have h0i := congrArg Complex.im h0
  have h1r := congrArg Complex.re h1
  have h1i := congrArg Complex.im h1
  simp at h0r h0i h1r h1i
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have a1 : (c.re : ℝ) + c.imI * √2 = 0 := by
    rcases h0i with h | h
    · exact h
    · exact absurd h hτ
  have a2 : (c.imJ : ℝ) - √2 * c.imK = 0 := by
    rcases h1i with h | h
    · exact h
    · exact absurd h hτ
  have b1 : -3 * (c.imJ : ℝ) - 3 * √2 * c.imK = 0 := by
    have := h0r; rw [a1] at this; linarith
  have b2 : (c.re : ℝ) - c.imI * √2 = 0 := by
    have := h1r; rw [a2] at this; linarith
  have e0 : (c.re : ℝ) = 0 := by linarith
  have e1 : (c.imI : ℝ) = 0 := by
    have : (c.imI : ℝ) * √2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hs.ne'
  have e3 : (c.imK : ℝ) = 0 := by
    have : √2 * (c.imK : ℝ) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hs.ne'
  have e2 : (c.imJ : ℝ) = 0 := by linarith
  ext
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-- A linear map commuting with `ι(i)` and `ι(j)` is a scalar. -/
theorem scalar_of_commute (N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hi : ∀ z, N (cM ⟨0, 1, 0, 0⟩ *ᵥ z) = cM ⟨0, 1, 0, 0⟩ *ᵥ N z)
    (hj : ∀ z, N (cM ⟨0, 0, 1, 0⟩ *ᵥ z) = cM ⟨0, 0, 1, 0⟩ *ᵥ N z) :
    ∃ p : ℂ, ∀ z, N z = p • z := by
  have hs : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  set A := LinearMap.toMatrix' N with hA
  have hN : ∀ z, N z = A *ᵥ z := fun z => by
    rw [hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have comm : ∀ x : LeafQM.B, (∀ z, N (cM x *ᵥ z) = cM x *ᵥ N z) → A * cM x = cM x * A := by
    intro x hx
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← hN, ← hN, hx]
  have hAi := comm _ hi
  have hAj := comm _ hj
  rw [cM_apply] at hAi hAj
  have i01 := congrFun (congrFun hAi 0) 1
  have i10 := congrFun (congrFun hAi 1) 0
  have j01 := congrFun (congrFun hAj 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at i01 i10 j01
  have a01 : A 0 1 = 0 := by
    have : 2 * ((√2 : ℝ) : ℂ) * A 0 1 = 0 := by linear_combination -i01
    simpa [hs] using this
  have a10 : A 1 0 = 0 := by
    have : 2 * ((√2 : ℝ) : ℂ) * A 1 0 = 0 := by linear_combination i10
    simpa [hs] using this
  have a11 : A 1 1 = A 0 0 := by
    linear_combination (-1/3 : ℂ) * j01
  refine ⟨A 0 0, fun z => ?_⟩
  rw [hN]
  ext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, a01, a10, a11]

theorem cM_sub (a b : LeafQM.B) : cM (a - b) = cM a - cM b := by
  rw [cM_apply, cM_apply, cM_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem latVec_sub (a b : LeafQM.B) (τ : ℂ) :
    BPAnalytic.QM.latVec (a - b) τ = BPAnalytic.QM.latVec a τ - BPAnalytic.QM.latVec b τ := by
  rw [latVec_eq, latVec_eq, latVec_eq, cM_sub, Matrix.sub_mulVec]

theorem cM_injective {a b : LeafQM.B} (h : cM a = cM b) : a = b := by
  have h0 : BPAnalytic.QM.latVec (a - b) Complex.I = 0 := by
    rw [latVec_sub, latVec_eq, latVec_eq, h, sub_self]
  exact sub_eq_zero.mp (latVec_eq_zero (by simp) h0)

/-- **`QMLatticeTwistAlg`, (⇒) (proved from Skolem–Noether).** -/
theorem qmLatticeTwistAlg_mp (hSN : GlueDescent.LeafSkolemNoether) (τ τ' : UpperHalfPlane)
    (h : ∃ α : LeafQM.O ≃+* LeafQM.O, ∃ M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ z, z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
        M z ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne') ∧
      ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z)) :
    ∃ g ∈ PkgI1.GammaStar, g • τ = τ' := by
  obtain ⟨α, M, hML, hMeq⟩ := h
  obtain ⟨w, hw⟩ := PeriodGlue.AutOExt.autO_inner hSN α
  set wv : LeafQM.B := (w : LeafQM.B) with hwvdef
  set u : LeafQM.B := ((w⁻¹ : LeafQM.Bˣ) : LeafQM.B) with hudef
  have hwu : wv * u = 1 := w.mul_inv
  have huw : u * wv = 1 := w.inv_mul
  have hα : ∀ a : LeafQM.O, ((α a : LeafQM.O) : LeafQM.B) = wv * a * u := hw
  have hαs : ∀ c : LeafQM.O, ((α.symm c : LeafQM.O) : LeafQM.B) = u * c * wv := by
    intro c
    have h1 := hα (α.symm c)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1]
    calc ((α.symm c : LeafQM.O) : LeafQM.B) = (u * wv) * (α.symm c : LeafQM.B) * (u * wv) := by
          rw [huw, _root_.one_mul, _root_.mul_one]
      _ = u * (wv * (α.symm c : LeafQM.B) * u) * wv := by noncomm_ring
  -- `N = M ∘ ι(w)` commutes with `ι(𝒪)`
  let N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) ∘ₗ Matrix.toLin' (cM wv)
  have hN : ∀ z, N z = M (cM wv *ᵥ z) := fun z => rfl
  have hNa : ∀ a : LeafQM.O, ∀ z, N (cM a *ᵥ z) = cM a *ᵥ N z := by
    intro a z
    rw [hN, hN]
    have e : wv * a = (wv * a * u) * wv := by
      calc wv * (a : LeafQM.B) = wv * a * 1 := (_root_.mul_one _).symm
        _ = wv * a * (u * wv) := by rw [huw]
        _ = (wv * a * u) * wv := by noncomm_ring
    rw [Matrix.mulVec_mulVec, ← cM_mul, e, cM_mul, ← Matrix.mulVec_mulVec, ← hα, ← qmMat_eq,
      hMeq, qmMat_eq]
  have qi_mem : (⟨0, 1, 0, 0⟩ : LeafQM.B) ∈ LeafQM.O :=
    ⟨![0, 1, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩
  have qj_mem : (⟨0, 0, 1, 0⟩ : LeafQM.B) ∈ LeafQM.O :=
    ⟨![-1, 0, 2, 0], by ext <;> simp [LeafQM.ofInt]⟩
  obtain ⟨p, hp⟩ := scalar_of_commute N (hNa ⟨_, qi_mem⟩) (hNa ⟨_, qj_mem⟩)
  have hMz : ∀ z, M z = p • (cM u *ᵥ z) := by
    intro z
    have hz : z = cM wv *ᵥ (cM u *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, ← cM_mul, hwu, cM_one, Matrix.one_mulVec]
    calc M z = M (cM wv *ᵥ (cM u *ᵥ z)) := by rw [← hz]
      _ = N (cM u *ᵥ z) := (hN _).symm
      _ = p • (cM u *ᵥ z) := hp _
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : M ![1, 0] = M 0 := by rw [hMz, h0, zero_smul, map_zero]
    have := congrFun (M.injective h1) 0
    simp at this
  have hτ : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  -- `(τ', 1)ᵀ = p ι(x) (τ, 1)ᵀ` with `x = u b₁`
  have hv1 : BPAnalytic.QM.latVec 1 τ' ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne' :=
    (mem_qmLattice_iff _ _).mpr ⟨1, LeafQM.O.one_mem, rfl⟩
  obtain ⟨b1, hb1, hz1⟩ := (mem_qmLattice_iff _ _).mp
    ((hML (M.symm (BPAnalytic.QM.latVec 1 τ'))).mpr (by rw [M.apply_symm_apply]; exact hv1))
  set x := u * b1 with hxdef
  have hvx : BPAnalytic.QM.latVec 1 τ' = p • BPAnalytic.QM.latVec x τ := by
    have h1 := congrArg M hz1
    rw [M.apply_symm_apply] at h1
    rw [h1, hMz, hxdef, latVec_mul]
  have hv1' : BPAnalytic.QM.latVec 1 τ' = ![((τ' : UpperHalfPlane) : ℂ), 1] := by
    rw [latVec_eq, cM_one, Matrix.one_mulVec]
  have hlat' : ∀ b', BPAnalytic.QM.latVec b' τ' = p • BPAnalytic.QM.latVec (b' * x) τ := by
    intro b'
    rw [latVec_eq, ← hv1', hvx, Matrix.mulVec_smul, latVec_mul b' x]
  -- `u 𝒪 ⊆ 𝒪 x`
  have hA : ∀ b ∈ LeafQM.O, ∃ b' ∈ LeafQM.O, u * b = b' * x := by
    intro b hb
    have hm : M (BPAnalytic.QM.latVec b τ) ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne' :=
      (hML _).mp ((mem_qmLattice_iff _ _).mpr ⟨b, hb, rfl⟩)
    obtain ⟨b', hb', hbe⟩ := (mem_qmLattice_iff _ _).mp hm
    refine ⟨b', hb', ?_⟩
    rw [hMz, ← latVec_mul, hlat'] at hbe
    have h2 : BPAnalytic.QM.latVec (u * b) τ = BPAnalytic.QM.latVec (b' * x) τ :=
      smul_right_injective _ hp0 hbe
    have h3 : BPAnalytic.QM.latVec (u * b - b' * x) τ = 0 := by rw [latVec_sub, h2, sub_self]
    exact sub_eq_zero.mp (latVec_eq_zero hτ h3)
  -- `b₁` is a unit of `𝒪`
  obtain ⟨b', hb', hb'e⟩ := hA 1 LeafQM.O.one_mem
  set e := wv * b' * u with hedef
  have he : e ∈ LeafQM.O := by
    have := (α ⟨b', hb'⟩).2
    rwa [hα] at this
  have heb1 : e * b1 = 1 := by
    calc e * b1 = wv * (b' * (u * b1)) := by rw [hedef]; noncomm_ring
      _ = wv * (u * 1) := by rw [← hxdef, ← hb'e]
      _ = 1 := by rw [_root_.mul_one, hwu]
  have hb1e : b1 * e = 1 := by
    apply cM_injective
    rw [cM_mul, cM_one]
    have : cM e * cM b1 = 1 := by rw [← cM_mul, heb1, cM_one]
    exact mul_eq_one_comm.mp this
  set y := e * wv with hydef
  have hxy : x * y = 1 := by
    calc x * y = u * (b1 * e) * wv := by rw [hxdef, hydef]; noncomm_ring
      _ = 1 := by rw [hb1e, _root_.mul_one, huw]
  have hyx : y * x = 1 := by
    calc y * x = e * (wv * u) * b1 := by rw [hxdef, hydef]; noncomm_ring
      _ = 1 := by rw [hwu, _root_.mul_one, heb1]
  have hnorm : ∀ z : PkgI1.B, PkgI1.InO z → PkgI1.InO (x * z * y) ∧ PkgI1.InO (y * z * x) := by
    intro z hz
    have hz' := (inO_iff z).mp hz
    constructor
    · rw [inO_iff]
      have hc : b1 * z * e ∈ LeafQM.O :=
        LeafQM.O.mul_mem (LeafQM.O.mul_mem hb1 hz') he
      have := (α.symm ⟨_, hc⟩).2
      rw [hαs] at this
      have eq : x * z * y = u * (b1 * z * e) * wv := by rw [hxdef, hydef]; noncomm_ring
      rw [eq]; exact this
    · rw [inO_iff]
      have hc := (α ⟨z, hz'⟩).2
      rw [hα] at hc
      have eq : y * z * x = e * (wv * z * u) * b1 := by rw [hxdef, hydef]; noncomm_ring
      rw [eq]
      exact LeafQM.O.mul_mem (LeafQM.O.mul_mem he hc) hb1
  -- the element of `GL₂(ℝ)`
  have hI1 : PkgI1.iota x * PkgI1.iota y = 1 := by
    rw [← PeriodMap.iota_mul, hxy, PeriodMap.iota_one]
  have hI2 : PkgI1.iota y * PkgI1.iota x = 1 := by
    rw [← PeriodMap.iota_mul, hyx, PeriodMap.iota_one]
  let g : GL (Fin 2) ℝ := ⟨PkgI1.iota x, PkgI1.iota y, hI1, hI2⟩
  have hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl
  have hgc : cM x = (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) := rfl
  -- `τ' = gτ`
  have hcomp := hvx
  rw [hv1', latVec_eq, hgc] at hcomp
  have c0 := congrFun hcomp 0
  have c1 := congrFun hcomp 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at c0 c1
  have hden : UpperHalfPlane.denom g τ = p⁻¹ := by
    have h1 : p * UpperHalfPlane.denom g τ = 1 := by
      simp only [UpperHalfPlane.denom]; rw [c1]
    rw [← mul_right_inj' hp0, h1, mul_inv_cancel₀ hp0]
  have hnum : ((τ' : UpperHalfPlane) : ℂ) = UpperHalfPlane.num g τ / UpperHalfPlane.denom g τ := by
    rw [hden, div_inv_eq_mul, c0]
    simp only [UpperHalfPlane.num]; ring
  have hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    have him := UpperHalfPlane.moebius_im g τ
    rw [← hnum] at him
    have h1 : 0 < ((τ' : UpperHalfPlane) : ℂ).im := τ'.im_pos
    have h2 : 0 < Complex.normSq (UpperHalfPlane.denom g τ) :=
      Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero g τ)
    have h3 : 0 < (τ : ℂ).im := τ.im_pos
    rw [him, Matrix.GeneralLinearGroup.val_det_apply] at h1
    have := (div_pos_iff_of_pos_right h2).mp h1
    exact pos_of_mul_pos_left this h3.le
  refine ⟨g, ⟨x, ⟨y, hxy, hyx, hnorm⟩, hgm, hdet⟩, ?_⟩
  ext1
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet),
    ← hnum]

/-- **`QMLatticeTwistAlg` (proved from Skolem–Noether).** -/
theorem qmLatticeTwistAlg_of (hSN : GlueDescent.LeafSkolemNoether) : QMLatticeTwistAlg :=
  fun τ τ' => ⟨qmLatticeTwistAlg_mp hSN τ τ', qmLatticeTwistAlg_mpr τ τ'⟩

/-- **`QMTwistLattice` from the `Hom` form of T11a and Skolem–Noether (proved).** -/
theorem qmTwistLattice_of' (hH : T11aRiemannHom) (hSN : GlueDescent.LeafSkolemNoether) :
    QMTwistLattice :=
  qmTwistLattice_of hH (qmLatticeTwistAlg_of hSN)

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/PiTwist.lean (declarations already in the chain dropped) -/

/-! # period-glue: `PiTwistC` from R2fp and two smaller named Props

Task period-glue, 2026-11-13. `PiTwistC Y Φ π` (period-map, `PGBase`, unchanged) is proved from
* `R1fpProps Y Φ` (only: `Y` proper and smooth over `ℚ`) and `R2fpProps Y Φ π` (the leaves R1, R2;
  both already hypotheses at the own triple),
* `TwistOrbitFinite Y Φ` (**GLUE**, moduli: the twist relation on `ℚ̄`- and `ℂ`-points is the
  orbit relation of a finite set of automorphisms of `Y`), and
* `FibreTransferC Y π` (**GLUE**, algebraic geometry: a fibre statement for `π` that holds on
  `ℚ̄`-points holds on `ℂ`-points),
by `piTwistC_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **GLUE (moduli: the `Aut(𝒪)`-twist relation is a finite orbit relation).** There is a finite
set `G` of automorphisms of `Y` over `ℚ` such that, on `ℚ̄`-points and on `ℂ`-points, two points
have twist-equivalent QM pairs iff one is the image of the other under some `g ∈ G`.

Why true for the genuine `Y₃` (model argument): `G` = the automorphisms inducing `twist α`
(`α ∈ Aut 𝒪`) and `rightMul u` (`u ∈ 𝒪^×`) on points (`R1heckeProps`, a clause of R1), composed.
It is finite: `rightMul u` depends only on `u mod 3𝒪` (`Level3.rightMul_eq_self`), inner twists
are `rightMul`s up to isomorphism, and `Aut(𝒪)/Inn` is finite (mobius-glue `AutOInnerFinite`,
from the kernel's Skolem–Noether); an automorphism of the reduced `Y` is determined by its action
on field points. (⇐) is `Φ` of `y ≫ g`. (⇒) a QM isomorphism `Q.q.twist α ≅ Q'.q` transports
`Q'`'s level structure to one on `(A, ι∘α)`; over an algebraically closed field two level
structures on the same QM pair differ by right multiplication by a unit of `𝒪/3𝒪` (both are
`𝒪`-linear isomorphisms `𝒪/3𝒪 ≅ A[3]`, `|A[3]| = 81`), and `𝒪^× → (𝒪/3𝒪)^×` is onto (strong
approximation for `𝒪¹`, plus `1 + i` of reduced norm `−1`; a finite check on the 72 units of
`𝒪/3𝒪`); then `Φ` injective gives `y' = y ≫ g`. Size: medium. -/
def TwistOrbitFinite (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ G : Set (Y ≅ Y), G.Finite ∧
    (∀ (y y' : fieldPt Qbar ⟶ Y) (Q Q' : QML3 Qbar), Φ Qbar y = M3.mk Q → Φ Qbar y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom)) ∧
    (∀ (y y' : fieldPt ℂ ⟶ Y) (Q Q' : QML3 ℂ), Φ ℂ y = M3.mk Q → Φ ℂ y' = M3.mk Q' →
      ((∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
        ∃ g ∈ G, y' = y ≫ g.hom))

/-- **GLUE (algebraic geometry: transfer of a fibre statement from `ℚ̄`- to `ℂ`-points).** For a
proper smooth curve `Y` over `ℚ` (the hypotheses make the statement true for every `Y`; without
them it fails, e.g. for `Y = Spec ℂ`, which has no `ℚ̄`-points) and a finite set `G` of
automorphisms of `Y` over `ℚ`, if the fibres of `π` on `ℚ̄`-points are exactly
the `G`-orbits (in the sense below), the same holds on `ℂ`-points.

Why true (model argument), for `Y` of finite type and separated over `ℚ` (R1fp: proper):
`E = {(p, q) ∈ Y ×_ℚ Y : π(p) = π(q)}` (the equalizer of `π∘pr₁`, `π∘pr₂`, closed since `P¹` is
separated) and `Γ = ⋃_{g ∈ G} graph(g)` (finite union of closed graphs, `Y` separated) are closed
subsets of the finite-type `ℚ`-scheme `Y ×_ℚ Y`, hence Jacobson: each is the closure of its closed
points. Closed points are the images of `ℚ̄`-points (Nullstellensatz), and on those `E` and `Γ`
agree by hypothesis, so `E = Γ`. A `ℂ`-point `(y, y')` lies in `E` iff `π(y) = π(y')`, and in
`Γ` iff `y' = y ≫ g` for some `g ∈ G` (it factors through the reduced closed subscheme
`graph(g) ≅ Y`, `Y` smooth hence reduced). Mathlib has Jacobson schemes
(`AlgebraicGeometry.JacobsonSpace`) and equalizers/graphs of morphisms; the charts of `ToP1` must
be turned into a morphism to `P¹`. Size: medium. -/
def FibreTransferC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)

/-- **`PiTwistC` from R2fp, `TwistOrbitFinite` and `FibreTransferC` (proved).** -/
theorem piTwistC_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : TwistOrbitFinite Y Φ)
    (hF : FibreTransferC Y π) :
    PiTwistC Y Φ π := by
  obtain ⟨G, hG, hQbar, hC⟩ := hT
  have hfibQ : ∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom) := by
    intro y y'
    have hP : Φ Qbar y = M3.mk (Quotient.out (Φ Qbar y)) := (Quotient.out_eq _).symm
    have hQ : Φ Qbar y' = M3.mk (Quotient.out (Φ Qbar y')) := (Quotient.out_eq _).symm
    exact ((h2 y y' _ _ hP hQ).1).trans (hQbar y y' _ _ hP hQ)
  intro y y' Q Q' hQ hQ'
  exact (hF h1.1 h1.2.1 G hG hfibQ y y').trans (hC y y' Q Q' hQ hQ').symm

/-! ## `FibreTransferC` split into its two directions -/

/-- **GLUE (AG, textbook density): two maps to `P¹` agreeing on `ℚ̄`-points agree on `ℂ`-points.**
For `Y` proper and smooth over `ℚ` and `σ, ρ : Y → P¹` (by charts) with the same values at every
`ℚ̄`-point, the values agree at every `ℂ`-point.

Why true: the locus where two morphisms to the separated `P¹` agree, residue maps included, is a
closed subscheme (the equalizer). It contains every closed point, since closed points are images of
`ℚ̄`-points. `Y` is Jacobson (finite type over a field) and reduced (smooth), so the equalizer is
`Y`. Size: medium (the equalizer of two `ToP1` charts; Mathlib's `JacobsonSpace`). -/
def ToP1AgreeC (Y : Over (Spec (CommRingCat.of ℚ))) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ σ ρ : ToP1 Y.left,
    (∀ y : fieldPt Qbar ⟶ Y, σ.val (K := Qbar) y.left = ρ.val (K := Qbar) y.left) →
    ∀ y : fieldPt ℂ ⟶ Y, σ.val (K := ℂ) y.left = ρ.val (K := ℂ) y.left

/-- **GLUE (AG; the hard half of `FibreTransferC`).** If the fibres of `π` on `ℚ̄`-points are the
orbits of a finite set `G` of automorphisms, then two `ℂ`-points with the same `π`-value are in one
`G`-orbit.

Why true (model argument): the hypothesis forces `π` to be non-constant on every component (a
component has infinitely many `ℚ̄`-points, while `G`-orbits are finite). A `ℂ`-point over a closed
point of `Y` comes from a `ℚ̄`-point through one embedding `ℚ̄ → ℂ`, and so does every point in its
`π`-fibre (the value is algebraic, and `π` is non-constant on components). That case reduces to the
hypothesis. For points over generic points of components, the closed subsets `{π(p) = π(q)}` and
`⋃ graph(g)` of `Y ×_ℚ Y` agree on closed points, hence agree (Jacobson). Size: medium-large. -/
def FibreGenericC (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ G : Set (Y ≅ Y), G.Finite →
    (∀ y y' : fieldPt Qbar ⟶ Y,
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔ ∃ g ∈ G, y' = y ≫ g.hom)) →
    ∀ y y' : fieldPt ℂ ⟶ Y,
      π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left → ∃ g ∈ G, y' = y ≫ g.hom

/-- **`FibreTransferC` from `ToP1AgreeC` and `FibreGenericC` (proved).** The direction (⇐) is
`ToP1AgreeC` applied to `π ∘ g` and `π`. -/
theorem fibreTransferC_of (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left)
    (hA : ToP1AgreeC Y) (hG : FibreGenericC Y π) : FibreTransferC Y π := by
  intro hP hS G hGf hQ y y'
  refine ⟨hG hP hS G hGf hQ y y', ?_⟩
  rintro ⟨g, hg, rfl⟩
  have e : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      (π.comp g.hom.left).val (K := K) z.left = π.val (K := K) (z ≫ g.hom).left :=
    fun K _ _ z => ToP1.val_comp_right π g.hom.left (K := K) z.left
  have hagree := hA hP hS (π.comp g.hom.left) π (fun y0 => by
    rw [e]
    exact ((hQ y0 (y0 ≫ g.hom)).mpr ⟨g, hg, rfl⟩).symm) y
  rw [e] at hagree
  exact hagree.symm

/-! ### `ToP1AgreeC` (proved: density of closed points) -/

/-- A closed point of `Y` (locally of finite type over `ℚ`) is the point of a `ℚ̄`-point. -/
theorem exists_qbarPt (Y : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType Y.hom]
    (x : Y.left) (hx : IsClosed ({x} : Set Y.left)) :
    ∃ emb : Y.left.residueField x ⟶ CommRingCat.of Qbar, ∃ y0 : fieldPt Qbar ⟶ Y,
      y0.left = (Scheme.SpecToEquivOfField Qbar Y.left).symm ⟨x, emb⟩ := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : LocallyOfFiniteType (Y.left.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (Y.left.fromSpecResidueField x ≫ Y.hom)
  have hφ' : Spec.map φ = Y.left.fromSpecResidueField x ≫ Y.hom := hφ
  have hft : RingHom.FiniteType φ.hom := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ']; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℚ (Y.left.residueField x) := hft
  haveI : Module.Finite ℚ (Y.left.residueField x) := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsAlgebraic ℚ (Y.left.residueField x) := Algebra.IsAlgebraic.of_finite ℚ _
  let emb : Y.left.residueField x →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom emb.toRingHom,
    Over.homMk ((Scheme.SpecToEquivOfField Qbar Y.left).symm ⟨x, CommRingCat.ofHom emb.toRingHom⟩) ?_,
    rfl⟩
  show _ ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
  apply Spec.homEquiv.injective
  ext1
  exact Subsingleton.elim _ _

theorem eval_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (f : Γ(X, U)) :
    X.evaluation V x hx (X.presheaf.map (homOfLE h).op f) = X.evaluation U x (h hx) f := by
  rw [← Scheme.germ_residue, ← Scheme.germ_residue, CommRingCat.comp_apply,
    CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- **`ToP1AgreeC` (proved).** -/
theorem toP1AgreeC_proof (Y : Over (Spec (CommRingCat.of ℚ))) : ToP1AgreeC Y := by
  intro hP hS σ ρ hQ y
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  -- closed points
  have hcl : ∀ x : Y.left, IsClosed ({x} : Set Y.left) → (x ∈ σ.U ↔ x ∈ ρ.U) ∧
      ∀ (h1 : x ∈ σ.U) (h2 : x ∈ ρ.U),
        Y.left.evaluation σ.U x h1 σ.f = Y.left.evaluation ρ.U x h2 ρ.f := by
    intro x hx
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt Y x hx
    have e := hQ y0
    unfold ToP1.val at e
    rw [hy0, Equiv.apply_symm_apply] at e
    refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
    · by_contra h2
      rw [dif_pos h1, dif_neg h2] at e
      exact OnePoint.coe_ne_infty _ e
    · by_contra h1
      rw [dif_neg h1, dif_pos h2] at e
      exact OnePoint.coe_ne_infty _ e.symm
    · rw [dif_pos h1, dif_pos h2] at e
      exact emb.hom.injective (OnePoint.coe_injective e)
  -- the two chart domains coincide
  have hU : ∀ p : Y.left, p ∈ σ.U ↔ p ∈ ρ.U := by
    have side : ∀ (σ ρ : ToP1 Y.left),
        (∀ x : Y.left, IsClosed ({x} : Set Y.left) → (x ∈ σ.U → x ∈ ρ.U)) →
        ∀ p : Y.left, p ∈ σ.U → p ∈ ρ.U := by
      intro σ ρ hc p hp
      by_contra hq
      obtain ⟨x, ⟨hxσ, hxρ⟩, hxc⟩ := nonempty_inter_closedPoints (Z := (σ.U : Set Y.left) ∩ (ρ.U : Set Y.left)ᶜ)
        ⟨p, hp, hq⟩ (σ.U.isOpen.isLocallyClosed.inter ρ.U.isOpen.isClosed_compl.isLocallyClosed)
      exact hxρ (hc x hxc hxσ)
    intro p
    exact ⟨side σ ρ (fun x hx => (hcl x hx).1.mp) p, side ρ σ (fun x hx => (hcl x hx).1.mpr) p⟩
  -- the difference of the two chart functions vanishes in every residue field of `U ∩ V`
  set W := σ.U ⊓ ρ.U with hW
  let s : Γ(Y.left, W) := Y.left.presheaf.map (homOfLE inf_le_left).op σ.f -
    Y.left.presheaf.map (homOfLE inf_le_right).op ρ.f
  have hsx : ∀ (x : Y.left) (hx : x ∈ W), Y.left.evaluation W x hx s =
      Y.left.evaluation σ.U x hx.1 σ.f - Y.left.evaluation ρ.U x hx.2 ρ.f := by
    intro x hx
    simp only [s, map_sub, eval_res]
  have hs : Y.left.basicOpen s = ⊥ := by
    by_contra hne
    have hne' : ((Y.left.basicOpen s : Y.left.Opens) : Set Y.left).Nonempty := by
      by_contra h0
      apply hne
      ext1
      simpa [Set.not_nonempty_iff_eq_empty] using h0
    obtain ⟨x, hxb, hxc⟩ := nonempty_inter_closedPoints hne'
      (Y.left.basicOpen s).isOpen.isLocallyClosed
    have hxW : x ∈ W := Y.left.basicOpen_le s hxb
    have h0 := (Y.left.evaluation_ne_zero_iff_mem_basicOpen x hxW s).mpr hxb
    rw [hsx x hxW, (hcl x hxc).2 hxW.1 hxW.2, sub_self] at h0
    exact h0 rfl
  have hev : ∀ (p : Y.left) (h1 : p ∈ σ.U) (h2 : p ∈ ρ.U),
      Y.left.evaluation σ.U p h1 σ.f = Y.left.evaluation ρ.U p h2 ρ.f := by
    intro p h1 h2
    have := (Y.left.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s).mp hs ⟨p, h1, h2⟩
    rw [hsx p ⟨h1, h2⟩] at this
    exact sub_eq_zero.mp this
  -- conclusion at the `ℂ`-point
  unfold ToP1.val
  by_cases h1 : (Scheme.SpecToEquivOfField ℂ Y.left y.left).1 ∈ σ.U
  · have h2 := (hU _).mp h1
    rw [dif_pos h1, dif_pos h2, hev _ h1 h2]
  · have h2 : (Scheme.SpecToEquivOfField ℂ Y.left y.left).1 ∉ ρ.U := fun h => h1 ((hU _).mpr h)
    rw [dif_neg h1, dif_neg h2]

/-- **`FibreTransferC` from its hard half `FibreGenericC` alone (proved).** -/
theorem fibreTransferC_of' (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left)
    (hG : FibreGenericC Y π) : FibreTransferC Y π :=
  fibreTransferC_of Y π (toP1AgreeC_proof Y) hG

/-! ### `FibreGenericC` (proved: Jacobson on `Y ×_ℚ Y`) -/

/-- Two maps to `P¹` agree at a point: same chart, same value. -/
def Agree {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) : Prop :=
  (p ∈ σ.U ↔ p ∈ ρ.U) ∧ ∀ (h1 : p ∈ σ.U) (h2 : p ∈ ρ.U),
    X.evaluation σ.U p h1 σ.f = X.evaluation ρ.U p h2 ρ.f

theorem agree_comm {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) : Agree σ ρ p ↔ Agree ρ σ p :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun a b => (h2 b a).symm⟩,
   fun ⟨h1, h2⟩ => ⟨h1.symm, fun a b => (h2 b a).symm⟩⟩

theorem val_eq_iff_agree {X : Scheme.{0}} (σ ρ : ToP1 X) {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ X) :
    σ.val a = ρ.val a ↔ Agree σ ρ (Scheme.SpecToEquivOfField K X a).1 := by
  unfold ToP1.val
  constructor
  · intro h
    refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 h2 => ?_⟩
    · by_contra h2
      rw [dif_pos h1, dif_neg h2] at h
      exact OnePoint.coe_ne_infty _ h
    · by_contra h1
      rw [dif_neg h1, dif_pos h2] at h
      exact OnePoint.coe_ne_infty _ h.symm
    · rw [dif_pos h1, dif_pos h2] at h
      exact (Scheme.SpecToEquivOfField K X a).2.hom.injective (OnePoint.coe_injective h)
  · rintro ⟨hU, hev⟩
    by_cases h1 : (Scheme.SpecToEquivOfField K X a).1 ∈ σ.U
    · rw [dif_pos h1, dif_pos (hU.mp h1), hev h1 (hU.mp h1)]
    · rw [dif_neg h1, dif_neg (fun h => h1 (hU.mpr h))]

theorem eval_mul_inv_P1 {X : Scheme.{0}} (ρ : ToP1 X) (q : X) (hq : q ∈ ρ.U ⊓ ρ.V) :
    X.evaluation ρ.U q hq.1 ρ.f * X.evaluation ρ.V q hq.2 ρ.g = 1 := by
  have h := congrArg (X.evaluation (ρ.U ⊓ ρ.V) q hq) ρ.inv
  rw [map_mul, map_one, eval_res, eval_res] at h
  exact h

/-- Near a point in one chart domain but not the other, the two maps disagree. -/
theorem disagree_nhds {X : Scheme.{0}} (σ ρ : ToP1 X) (p : X) (h1 : p ∈ σ.U) (h2 : p ∉ ρ.U) :
    ∀ᶠ q in nhds p, ¬ Agree σ ρ q := by
  have hpV : p ∈ ρ.V := by
    have : p ∈ ρ.U ⊔ ρ.V := by rw [ρ.cover]; trivial
    rcases this with h | h
    · exact absurd h h2
    · exact h
  set W := σ.U ⊓ ρ.V with hW
  let hfun : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op σ.f *
    X.presheaf.map (homOfLE inf_le_right).op ρ.g - 1
  have hhx : ∀ x (hx : x ∈ W), X.evaluation W x hx hfun =
      X.evaluation σ.U x hx.1 σ.f * X.evaluation ρ.V x hx.2 ρ.g - 1 := by
    intro x hx
    simp only [hfun, map_sub, map_mul, map_one, eval_res]
  have hg0 : X.evaluation ρ.V p hpV ρ.g = 0 := by
    rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ρ.basicOpen_g]
    exact fun h => h2 h.1
  have hpb : p ∈ X.basicOpen hfun := by
    rw [← X.evaluation_ne_zero_iff_mem_basicOpen p (show p ∈ W from ⟨h1, hpV⟩), hhx, hg0, mul_zero,
      zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  filter_upwards [(X.basicOpen hfun).isOpen.mem_nhds hpb] with q hq hag
  have hqW : q ∈ W := X.basicOpen_le hfun hq
  have hqU : q ∈ ρ.U := hag.1.mp hqW.1
  have hev := hag.2 hqW.1 hqU
  have hinv := eval_mul_inv_P1 ρ q ⟨hqU, hqW.2⟩
  have := (X.evaluation_ne_zero_iff_mem_basicOpen q hqW hfun).mpr hq
  rw [hhx, hev, hinv, sub_self] at this
  exact this rfl

/-- The agreement locus of two maps to `P¹` is closed. -/
theorem isClosed_agree {X : Scheme.{0}} (σ ρ : ToP1 X) : IsClosed {p | Agree σ ρ p} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hp
  show ∀ᶠ q in nhds p, ¬ Agree σ ρ q
  by_cases h1 : p ∈ σ.U <;> by_cases h2 : p ∈ ρ.U
  · have hne : X.evaluation σ.U p h1 σ.f ≠ X.evaluation ρ.U p h2 ρ.f := fun h =>
      hp ⟨⟨fun _ => h2, fun _ => h1⟩, fun _ _ => h⟩
    set W := σ.U ⊓ ρ.U with hW
    let s : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op σ.f -
      X.presheaf.map (homOfLE inf_le_right).op ρ.f
    have hsx : ∀ x (hx : x ∈ W), X.evaluation W x hx s =
        X.evaluation σ.U x hx.1 σ.f - X.evaluation ρ.U x hx.2 ρ.f := by
      intro x hx
      simp only [s, map_sub, eval_res]
    have hpb : p ∈ X.basicOpen s := by
      rw [← X.evaluation_ne_zero_iff_mem_basicOpen p (show p ∈ W from ⟨h1, h2⟩), hsx]
      exact sub_ne_zero.mpr hne
    filter_upwards [(X.basicOpen s).isOpen.mem_nhds hpb] with q hq hag
    have hqW : q ∈ W := X.basicOpen_le s hq
    have := (X.evaluation_ne_zero_iff_mem_basicOpen q hqW s).mpr hq
    rw [hsx, hag.2 hqW.1 hqW.2, sub_self] at this
    exact this rfl
  · exact disagree_nhds σ ρ p h1 h2
  · filter_upwards [disagree_nhds ρ σ p h2 h1] with q hq hag
    exact hq ((agree_comm σ ρ q).mp hag)
  · exact absurd ⟨⟨fun h => absurd h h1, fun h => absurd h h2⟩, fun h => absurd h h1⟩ hp

/-- Residue maps of the two projections at a point of the diagonal. -/
theorem diag_rfm (Y : Over (Spec (CommRingCat.of ℚ))) (r : ↥(pullback Y.hom Y.hom))
    (hr : r ∈ Set.range (fun q : Y.left => pullback.diagonal Y.hom q)) :
    ∃ e1 : pullback.fst Y.hom Y.hom r = pullback.snd Y.hom Y.hom r,
      (pullback.fst Y.hom Y.hom).residueFieldMap r =
        (Y.left.residueFieldCongr e1).hom ≫ (pullback.snd Y.hom Y.hom).residueFieldMap r := by
  obtain ⟨q, rfl⟩ := hr
  set D := pullback.diagonal Y.hom with hD
  have hpt : ∀ (f : pullback Y.hom Y.hom ⟶ Y.left), D ≫ f = 𝟙 _ → f (D q) = q := by
    intro f hf
    have := congrArg (fun h : Y.left ⟶ Y.left => h q) hf
    simpa using this
  have e1 : pullback.fst Y.hom Y.hom (D q) = pullback.snd Y.hom Y.hom (D q) :=
    (hpt _ (pullback.diagonal_fst Y.hom)).trans (hpt _ (pullback.diagonal_snd Y.hom)).symm
  refine ⟨e1, ?_⟩
  haveI : Mono (D.residueFieldMap q) :=
    ConcreteCategory.mono_of_injective _ (D.residueFieldMap q).hom.injective
  rw [← cancel_mono (D.residueFieldMap q), Category.assoc]
  have c1 := Scheme.residueFieldMap_comp D (pullback.fst Y.hom Y.hom) q
  have c2 := Scheme.residueFieldMap_comp D (pullback.snd Y.hom Y.hom) q
  have d1 := Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst Y.hom) q
  have d2 := Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd Y.hom) q
  rw [Scheme.residueFieldMap_id] at d1 d2
  rw [← c1, ← c2, d1, d2]
  simp only [Scheme.residueFieldCongr, eqToIso.hom]
  erw [Category.comp_id, Category.comp_id, eqToHom_trans]
  rfl

/-- A field-valued point of `Y ×_ℚ Y` over the diagonal has equal projections. -/
theorem diag_eq (Y : Over (Spec (CommRingCat.of ℚ))) {K : Type} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ pullback Y.hom Y.hom)
    (hb : (Scheme.SpecToEquivOfField K _ b).1 ∈ Set.range (fun q : Y.left => pullback.diagonal Y.hom q)) :
    b ≫ pullback.fst Y.hom Y.hom = b ≫ pullback.snd Y.hom Y.hom := by
  apply (Scheme.SpecToEquivOfField K Y.left).injective
  rw [specToEquivOfField_comp_right, specToEquivOfField_comp_right,
    Scheme.SpecToEquivOfField_eq_iff]
  obtain ⟨e1, he1⟩ := diag_rfm Y _ hb
  refine ⟨e1, ?_⟩
  simp only
  rw [he1, Category.assoc]

/-- **`FibreGenericC` (proved).** Jacobson on `P = Y ×_ℚ Y`: the agreement locus `A` of `π∘pr₁`,
`π∘pr₂` is closed, `Γ = ⋃_{g ∈ G} (pr₁ ≫ g, pr₂)⁻¹(Δ)` is closed (`Y` separated), `A \ Γ` has no
closed point (closed points come from `ℚ̄`-points, where the hypothesis applies), so `A ⊆ Γ`; a
`ℂ`-point of `A` over `Γ` has `y ≫ g = y'` (`diag_eq`). -/
theorem fibreGenericC_proof (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    FibreGenericC Y π := by
  intro hP hS G hGf hQ y y' hval
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : IsSeparated Y.hom := inferInstance
  let PO : Over (Spec (CommRingCat.of ℚ)) := Over.mk ((pullback.fst Y.hom Y.hom) ≫ Y.hom)
  haveI : LocallyOfFiniteType PO.hom := by
    show LocallyOfFiniteType ((pullback.fst Y.hom Y.hom) ≫ Y.hom); infer_instance
  haveI : JacobsonSpace ↥(pullback Y.hom Y.hom : Scheme.{0}) :=
    LocallyOfFiniteType.jacobsonSpace PO.hom
  set σ1 := π.comp (pullback.fst Y.hom Y.hom) with hσ1
  set σ2 := π.comp (pullback.snd Y.hom Y.hom) with hσ2
  set D := pullback.diagonal Y.hom with hD
  have hLw : ∀ g : Y ≅ Y, ((pullback.fst Y.hom Y.hom) ≫ g.hom.left) ≫ Y.hom = (pullback.snd Y.hom Y.hom) ≫ Y.hom := fun g => by
    rw [Category.assoc, Over.w g.hom, pullback.condition]
  let L : (Y ≅ Y) → (pullback Y.hom Y.hom ⟶ pullback Y.hom Y.hom) :=
    fun g => pullback.lift ((pullback.fst Y.hom Y.hom) ≫ g.hom.left) (pullback.snd Y.hom Y.hom) (hLw g)
  have hLf : ∀ g : Y ≅ Y, L g ≫ pullback.fst Y.hom Y.hom = pullback.fst Y.hom Y.hom ≫ g.hom.left :=
    fun g => pullback.lift_fst _ _ _
  have hLs : ∀ g : Y ≅ Y, L g ≫ pullback.snd Y.hom Y.hom = pullback.snd Y.hom Y.hom :=
    fun g => pullback.lift_snd _ _ _
  let Γ : Set ↥(pullback Y.hom Y.hom : Scheme.{0}) :=
    ⋃ g ∈ G, (fun x => L g x) ⁻¹' Set.range (fun q : Y.left => D q)
  have hΓ : IsClosed Γ := by
    apply hGf.isClosed_biUnion
    intro g _
    exact D.isClosedEmbedding.isClosed_range.preimage (L g).continuous
  have hmemΓ : ∀ (K : Type) [Field K] (b : Spec (CommRingCat.of K) ⟶ (pullback Y.hom Y.hom : Scheme.{0}))
      (g : Y ≅ Y) (c : Spec (CommRingCat.of K) ⟶ Y.left), b ≫ L g = c ≫ D →
      L g (Scheme.SpecToEquivOfField K _ b).1 ∈ Set.range (fun q : Y.left => D q) := by
    intro K _ b g c h
    have := congrArg (fun t => (Scheme.SpecToEquivOfField K _ t).1) h
    simp only [specToEquivOfField_comp_right] at this
    exact ⟨_, this.symm⟩
  -- the agreement locus lies in `Γ`
  have hAΓ : ∀ p, Agree σ1 σ2 p → p ∈ Γ := by
    intro p hp
    by_contra hpΓ
    obtain ⟨x, ⟨hxA, hxΓ⟩, hxc⟩ := nonempty_inter_closedPoints
      (Z := {p : ↥(pullback Y.hom Y.hom : Scheme.{0}) | Agree σ1 σ2 p} ∩ Γᶜ) ⟨p, hp, hpΓ⟩
      ((isClosed_agree σ1 σ2).isLocallyClosed.inter hΓ.isOpen_compl.isLocallyClosed)
    obtain ⟨emb, z, hz⟩ := exists_qbarPt PO x hxc
    let zl : Spec (CommRingCat.of Qbar) ⟶ (pullback Y.hom Y.hom : Scheme.{0}) := z.left
    have hzl : zl = (Scheme.SpecToEquivOfField Qbar (pullback Y.hom Y.hom : Scheme.{0})).symm
        ⟨x, emb⟩ := hz
    have hzw : z.left ≫ ((pullback.fst Y.hom Y.hom) ≫ Y.hom) = (fieldPt Qbar).hom := Over.w z
    let z1 : fieldPt Qbar ⟶ Y := Over.homMk (z.left ≫ (pullback.fst Y.hom Y.hom)) (by
      rw [Category.assoc]; exact hzw)
    let z2 : fieldPt Qbar ⟶ Y := Over.homMk (z.left ≫ (pullback.snd Y.hom Y.hom)) (by
      rw [Category.assoc, ← pullback.condition]; exact hzw)
    have hzval : π.val (K := Qbar) z1.left = π.val (K := Qbar) z2.left := by
      show π.val (zl ≫ (pullback.fst Y.hom Y.hom)) = π.val (zl ≫ (pullback.snd Y.hom Y.hom))
      rw [← ToP1.val_comp_right, ← ToP1.val_comp_right, ← hσ1, ← hσ2]
      apply (val_eq_iff_agree σ1 σ2 zl).mpr
      rw [hzl, Equiv.apply_symm_apply]
      exact hxA
    obtain ⟨g, hg, hgz⟩ := (hQ z1 z2).mp hzval
    apply hxΓ
    refine Set.mem_biUnion hg ?_
    let z2l : Spec (CommRingCat.of Qbar) ⟶ Y.left := z2.left
    have hfac : zl ≫ L g = z2l ≫ D := by
      apply pullback.hom_ext
      · rw [Category.assoc, hLf g, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        have h3 := congrArg CommaMorphism.left hgz
        exact h3.symm
      · rw [Category.assoc, hLs g, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        rfl
    have := hmemΓ Qbar zl g z2l hfac
    rw [hzl, Equiv.apply_symm_apply] at this
    exact this
  -- the `ℂ`-point
  have hyw : y.left ≫ Y.hom = y'.left ≫ Y.hom := by rw [Over.w y, Over.w y']
  let w : Spec (CommRingCat.of ℂ) ⟶ (pullback Y.hom Y.hom : Scheme.{0}) :=
    pullback.lift y.left y'.left hyw
  have hw1 : w ≫ pullback.fst Y.hom Y.hom = y.left := pullback.lift_fst _ _ _
  have hw2 : w ≫ pullback.snd Y.hom Y.hom = y'.left := pullback.lift_snd _ _ _
  have hwA : Agree σ1 σ2 (Scheme.SpecToEquivOfField ℂ _ w).1 := by
    apply (val_eq_iff_agree σ1 σ2 w).mp
    rw [hσ1, hσ2, ToP1.val_comp_right, ToP1.val_comp_right, hw1, hw2]
    exact hval
  obtain ⟨g, hg, hgΓ⟩ := Set.mem_iUnion₂.mp (hAΓ _ hwA)
  refine ⟨g, hg, ?_⟩
  have key := diag_eq Y (w ≫ L g) (by rw [specToEquivOfField_comp_right]; exact hgΓ)
  rw [Category.assoc, Category.assoc, hLf g, hLs g, ← Category.assoc, hw1, hw2] at key
  ext1
  exact key.symm

/-- **`FibreTransferC` (proved).** -/
theorem fibreTransferC_proof (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    FibreTransferC Y π :=
  fibreTransferC_of' Y π (fibreGenericC_proof Y π)

/-! ## `TwistOrbitFinite` from R1hecke, `TorsionStructure` and two algebra facts -/

/-- **GLUE, proved in mobius-glue** (`scratch/mobius-glue/MobiusGlue.lean` §7, `AutOInnerFinite`;
from the kernel's Skolem–Noether and `N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`; copied verbatim up to writing
`LeafQM.O` for `O`; it cannot be
imported here). Every automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely
many. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (LeafQM.O ≃+* LeafQM.O), T.Finite ∧ ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T,
    ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)

/-- **GLUE (finite computation; strong approximation for `𝒪¹`).** Every element of `𝒪` that is
invertible modulo `3𝒪` is congruent modulo `3𝒪` to a unit of `𝒪` (`𝒪^× → (𝒪/3𝒪)^×` is onto).

Why true: `B` is indefinite, so `𝒪¹` is dense in `∏_p 𝒪_p¹` (Eichler's strong approximation,
Vignéras, *Arithmétique des algèbres de quaternions*, III.4; UNVERIFIED locator), hence
`𝒪¹ → (𝒪/3𝒪)¹` is onto; together with `1 + i` (reduced norm `−1`) this covers
`(𝒪/3𝒪)^×` (72 elements). A finite check: the reductions of finitely many explicit units of `𝒪`
generate the 72 classes. Size: small-medium (a `decide`-style computation over `(ℤ/3)⁴`). -/
def UnitLiftMod3 : Prop :=
  ∀ u₀ v₀ : LeafQM.O, (∃ c : LeafQM.O, v₀ * u₀ - 1 = 3 * c) →
    ∃ u : (LeafQM.O)ˣ, ∃ c : LeafQM.O, (u : LeafQM.O) - u₀ = 3 * c

section TwistOrbit

variable {K : Type} [Field K]

/-- Transport of a level structure along an isomorphism of QM pairs (copied from mobius-glue). -/
def transportLevel' {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- A level-3 isomorphism gives a QM isomorphism. -/
def QML3.Iso.toQMIso {P Q : QML3 K} (f : P.Iso Q) : QMIso P.q Q.q where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant

/-- Twists by `t` and by `v t v⁻¹` are isomorphic through `ι(v)` (copied from mobius-glue). -/
def conjUnitIso' {A : PkgI3.AbVar K} (q : QMStr A) (t α : LeafQM.O ≃+* LeafQM.O) (v : (LeafQM.O)ˣ)
    (hv : ∀ a, α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O)) :
    QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg PkgI3.AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : LeafQM.O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg PkgI3.AbVar.Hom.hom this

/-- Finitely many representatives of the units of `𝒪` modulo `3𝒪`. -/
theorem unitReps : ∃ U : Set (LeafQM.O)ˣ, U.Finite ∧
    ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c := by
  classical
  -- the class of `u` modulo `3𝒪`: its coordinates mod 3
  have hcoord : ∀ x : LeafQM.O, ∃ n : Fin 4 → ℤ, (x : LeafQM.B) = LeafQM.ofInt n := fun x => x.2
  choose n hn using hcoord
  let cls : (LeafQM.O)ˣ → (Fin 4 → ZMod 3) := fun u i => (n u i : ZMod 3)
  have hrep : ∀ c ∈ Set.range cls, ∃ u : (LeafQM.O)ˣ, cls u = c := fun c hc => hc
  choose! r hr using hrep
  refine ⟨r '' Set.range cls, (Set.toFinite (Set.range cls)).image r, fun u => ⟨r (cls u), ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩⟩
  have hcl : cls (r (cls u)) = cls u := hr _ ⟨u, rfl⟩
  -- coordinates agree mod 3
  have hmod : ∀ i, (3 : ℤ) ∣ n u i - n (r (cls u)) i := by
    intro i
    have := congrFun hcl i
    simp only [cls] at this
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp this
    exact_mod_cast h3
  choose k hk using hmod
  refine ⟨⟨LeafQM.ofInt k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
  show ((u : LeafQM.O) : LeafQM.B) - ((r (cls u) : LeafQM.O) : LeafQM.B) = 3 * LeafQM.ofInt k
  rw [hn, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  linear_combination hk i

/-- The twist relation is the orbit relation of `{g_t ∘ h_u : t ∈ T, u ∈ U}`, over any field of
characteristic `0` (proved). -/
theorem twist_iff_orbit (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hT : ObjBridge.TorsionStructure) (hU : UnitLiftMod3)
    (T : Set (LeafQM.O ≃+* LeafQM.O))
    (hTα : ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ t ∈ T, ∃ v : (LeafQM.O)ˣ, ∀ a : LeafQM.O,
      α a = (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O))
    (U : Set (LeafQM.O)ˣ) (hUu : ∀ u : (LeafQM.O)ˣ, ∃ u' ∈ U, ∃ c : LeafQM.O, (u : LeafQM.O) - u' = 3 * c)
    (g : (LeafQM.O ≃+* LeafQM.O) → (Y ≅ Y))
    (hg : ∀ α (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (g α).hom) = M3.twist α (Φ K y))
    (h : (LeafQM.O)ˣ → (Y ≅ Y))
    (hh : ∀ u (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ (h u).hom) = M3.rightMul u (Φ K y))
    (K : Type) [Field K] [Algebra ℚ K] [CharZero K] (y y' : fieldPt K ⟶ Y) (Q Q' : QML3 K)
    (hQ : Φ K y = M3.mk Q) (hQ' : Φ K y' = M3.mk Q') :
    (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (Q.q.twist α) Q'.q)) ↔
      ∃ G' ∈ (fun p : (LeafQM.O ≃+* LeafQM.O) × (LeafQM.O)ˣ => g p.1 ≪≫ h p.2) '' (T ×ˢ U),
        y' = y ≫ G'.hom := by
  constructor
  · rintro ⟨α, ⟨f⟩⟩
    obtain ⟨t, ht, v, hv⟩ := hTα α
    let f' : QMIso (Q.q.twist t) Q'.q := (conjUnitIso' Q.q t α v hv).trans f
    let P : QML3 K := Q.twist t
    let e' : Level3 P.q := transportLevel' f'.symm Q'.e
    obtain ⟨u₀, v₀, hinv, hu₀⟩ := Level3.torsor hT P e'
    obtain ⟨u, cu, hcu⟩ := hU u₀ v₀ hinv
    obtain ⟨u', hu'U, cu', hcu'⟩ := hUu u
    have hlev : ∀ a : LeafQM.O, e'.eta a = P.e.eta (a * u') := by
      intro a
      rw [hu₀ a, P.e.eq_iff]
      exact ⟨a * (cu' - cu), by
        calc a * u₀ - a * (u' : LeafQM.O)
            = a * (((u : LeafQM.O) - u') - ((u : LeafQM.O) - u₀)) := by noncomm_ring
          _ = a * (3 * cu' - 3 * cu) := by rw [hcu, hcu']
          _ = 3 * (a * (cu' - cu)) := by noncomm_ring⟩
    let iso : (P.rightMul u').Iso Q' :=
      { φ := f'.φ
        ψ := f'.ψ
        left := f'.left
        right := f'.right
        equivariant := f'.equivariant
        level := fun a => by
          change Additive.ofMul (Additive.toMul (P.e.eta (a * u')) ≫ f'.φ.hom) = Q'.e.eta a
          rw [← hlev a]
          change Additive.ofMul ((Additive.toMul (Q'.e.eta a) ≫ f'.ψ.hom) ≫ f'.φ.hom) = _
          rw [Category.assoc, f'.right, Category.comp_id]
          rfl }
    have hm : Φ K (y ≫ (g t ≪≫ h u').hom) = M3.mk Q' := by
      rw [Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      exact Quotient.sound ⟨iso⟩
    exact ⟨g t ≪≫ h u', ⟨(t, u'), ⟨ht, hu'U⟩, rfl⟩, (Φ K).injective (hQ'.trans hm.symm)⟩
  · rintro ⟨G', ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, hy'⟩
    have hm : M3.mk Q' = M3.mk ((Q.twist t).rightMul u) := by
      rw [← hQ', hy', Iso.trans_hom, ← Category.assoc, hh, hg, hQ, M3.twist_mk]
      rfl
    obtain ⟨iso⟩ := Quotient.exact hm
    exact ⟨t, ⟨QML3.Iso.toQMIso iso.symm⟩⟩

end TwistOrbit

/-- **`TwistOrbitFinite` from R1hecke, the textbook leaf `TorsionStructure` (T5), `AutOInnerFinite`
(proved in mobius-glue) and `UnitLiftMod3` (proved).** -/
theorem twistOrbitFinite_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite)
    (hU : UnitLiftMod3) : TwistOrbitFinite Y Φ := by
  obtain ⟨hα, hu⟩ := hH
  choose g hg using hα
  choose h hh using hu
  obtain ⟨T, hTf, hTα⟩ := hA
  obtain ⟨U, hUf, hUu⟩ := unitReps
  exact ⟨_, (hTf.prod hUf).image (fun p => g p.1 ≪≫ h p.2),
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh Qbar y y' Q Q' hQ hQ',
    fun y y' Q Q' hQ hQ' => twist_iff_orbit Y Φ hT hU T hTα U hUu g hg h hh ℂ y y' Q Q' hQ hQ'⟩

/-! ## `UnitLiftMod3` (proved by a finite computation) -/

/-- The reduced norm of `ofInt n` (`= nrd`, an integer). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mulCoord (n m : Fin 4 → ℤ) : nrdZ (LeafQM.mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, LeafQM.mulCoord]; ring

/-- Coordinates of the conjugate of `ofInt n`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : LeafQM.mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : LeafQM.mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [LeafQM.mulCoord, conjC, nrdZ] <;> ring

/-- A unit of `𝒪` in each class of `(𝒪/3𝒪)^×` (`py/unit_table.py`; entry `c₀ + 3c₁ + 9c₂ + 27c₃`). -/
def unitTbl : Fin 81 → (Fin 4 → ℤ) :=
  ![![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-3, -2, 0, 0], ![1, 1, 0, 0], ![-1, 1, 0, 0], ![-3, -1, -3, -3], ![1, -1, 0, 0], ![-1, -1, 0, 0], ![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![-1, 1, 1, 0], ![0, -1, 1, 0], ![1, -1, 1, 0], ![-1, -1, 1, 0], ![0, 0, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, 0], ![0, 1, -1, 0], ![1, 1, -1, 0], ![-1, 1, -1, 0], ![0, -1, -1, 0], ![1, -1, -1, 0], ![-1, -1, -1, 0], ![-3, 0, 0, -2], ![1, 0, 0, 1], ![-1, 0, 0, 1], ![1, 0, 0, 0], ![-2, -2, 3, 1], ![-1, -2, 3, 1], ![-3, 2, 0, -2], ![1, -1, 0, 1], ![-1, -1, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![-1, 0, 1, 1], ![-3, -2, 1, 1], ![1, 0, 0, 0], ![-1, -2, -2, 1], ![0, -1, 1, 1], ![1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![1, 0, -1, 1], ![-1, 0, -1, 1], ![-3, -2, 2, 1], ![-2, -2, -1, 1], ![1, 0, 0, 0], ![0, -1, -1, 1], ![1, -1, -1, 1], ![-1, -1, -1, 1], ![-3, -3, -3, -1], ![1, 0, 0, -1], ![-1, 0, 0, -1], ![-3, -2, 0, 2], ![1, 1, 0, -1], ![-1, 1, 0, -1], ![1, 0, 0, 0], ![-2, -1, 3, -1], ![-1, -1, 3, -1], ![0, 0, 1, -1], ![1, 0, 1, -1], ![-1, 0, 1, -1], ![0, 1, 1, -1], ![1, 1, 1, -1], ![-1, 1, 1, -1], ![-3, -1, 1, -1], ![1, 0, 0, 0], ![-1, -1, -2, -1], ![0, 0, -1, -1], ![1, 0, -1, -1], ![-1, 0, -1, -1], ![0, 1, -1, -1], ![1, 1, -1, -1], ![-1, 1, -1, -1], ![-3, -1, 2, -1], ![-2, -1, -1, -1], ![1, 0, 0, 0]]

/-- The index of a class. -/
def encC (a b c d : ZMod 3) : Fin 81 :=
  ⟨a.val + 3 * b.val + 9 * c.val + 27 * d.val, by
    have ha : a.val < 3 := ZMod.val_lt a
    have hb : b.val < 3 := ZMod.val_lt b
    have hc : c.val < 3 := ZMod.val_lt c
    have hd : d.val < 3 := ZMod.val_lt d
    omega⟩

theorem unitTbl_spec : ∀ a b c d : ZMod 3, a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    (((unitTbl (encC a b c d) 0 : ℤ) : ZMod 3) = a ∧ ((unitTbl (encC a b c d) 1 : ℤ) : ZMod 3) = b ∧
      ((unitTbl (encC a b c d) 2 : ℤ) : ZMod 3) = c ∧ ((unitTbl (encC a b c d) 3 : ℤ) : ZMod 3) = d) ∧
    (nrdZ (unitTbl (encC a b c d)) = 1 ∨ nrdZ (unitTbl (encC a b c d)) = -1) := by
  set_option maxRecDepth 100000 in decide

/-- **`UnitLiftMod3` (proved).** -/
theorem unitLiftMod3_proof : UnitLiftMod3 := by
  rintro ⟨u₀, n, hn⟩ ⟨v₀, m, hm⟩ ⟨⟨c, k, hk⟩, hc⟩
  have hc' := congrArg Subtype.val hc
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] at hc'
  have h33 : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3
  rw [h33, hm, hn, hk, LeafQM.ofInt_mul, ← LeafQM.ofInt_one, LeafQM.AV.ofInt_sub,
    LeafQM.AV.three_mul_ofInt] at hc'
  have hco := LeafQM.AV.ofInt_injective hc'
  -- `nrd(u₀) ≢ 0 mod 3`
  have hmn : ∀ i, LeafQM.mulCoord m n i = ![1, 0, 0, 0] i + 3 * k i := fun i => by
    have := congrFun hco i
    simp only [Pi.sub_apply] at this
    linear_combination this
  have hn1 : ((nrdZ (LeafQM.mulCoord m n) : ℤ) : ZMod 3) = 1 := by
    have e : LeafQM.mulCoord m n = fun i => ![1, 0, 0, 0] i + 3 * k i := funext hmn
    rw [e]
    simp only [nrdZ]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := rfl
    rw [h3]
    norm_num
  have hnrd : (nrdZ n : ZMod 3) ≠ 0 := by
    intro h0
    rw [nrdZ_mulCoord, Int.cast_mul, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨⟨t0, t1, t2, t3⟩, hpm⟩ := unitTbl_spec (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3)
    (n 3 : ZMod 3) (by
      have : ((nrdZ n : ℤ) : ZMod 3) = (n 0 : ZMod 3) ^ 2 + (n 0 : ZMod 3) * (n 2 : ZMod 3) +
          (n 2 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) ^ 2 - 2 * (n 1 : ZMod 3) * (n 3 : ZMod 3) -
          2 * (n 3 : ZMod 3) ^ 2 := by simp [nrdZ]
      rw [← this]; exact hnrd)
  set t := unitTbl (encC (n 0 : ZMod 3) (n 1 : ZMod 3) (n 2 : ZMod 3) (n 3 : ZMod 3)) with htdef
  set ε := nrdZ t with hε
  have hεε : ε * ε = 1 := by rcases hpm with h | h <;> rw [h] <;> norm_num
  -- the unit `ofInt t`, with inverse `ε · conj`
  let x : LeafQM.O := ⟨LeafQM.ofInt t, t, rfl⟩
  let y : LeafQM.O := ⟨LeafQM.ofInt (ε • conjC t), ε • conjC t, rfl⟩
  have hxy : x * y = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt t * LeafQM.ofInt (ε • conjC t) = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC' t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  have hyx : y * x = 1 := by
    apply Subtype.ext
    show LeafQM.ofInt (ε • conjC t) * LeafQM.ofInt t = 1
    rw [LeafQM.ofInt_mul, ← LeafQM.ofInt_one]
    congr 1
    funext i
    have := congrFun (mulCoord_conjC t) i
    fin_cases i <;> simp [LeafQM.mulCoord, conjC] at this ⊢ <;>
      first | linear_combination ε * this | linear_combination ε * this + hεε
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  -- the congruence
  have hdiv : ∀ i, ∃ q : ℤ, t i - n i = 3 * q := by
    intro i
    have hti : ((t i : ℤ) : ZMod 3) = (n i : ZMod 3) := by
      fin_cases i
      · exact t0
      · exact t1
      · exact t2
      · exact t3
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).mp hti.symm
    exact ⟨q, by push_cast at hq; linear_combination hq⟩
  choose q hq using hdiv
  refine ⟨⟨LeafQM.ofInt q, q, rfl⟩, Subtype.ext ?_⟩
  show LeafQM.ofInt t - u₀ = ((3 : LeafQM.O) : LeafQM.B) * LeafQM.ofInt q
  rw [h33, hn, LeafQM.AV.ofInt_sub, LeafQM.AV.three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact hq i

/-- **`TwistOrbitFinite` from R1hecke, `TorsionStructure` and `AutOInnerFinite` (proved).** -/
theorem twistOrbitFinite_of' (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (hH : R1heckeProps Y Φ) (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistOrbitFinite Y Φ :=
  twistOrbitFinite_of Y Φ hH hT hA unitLiftMod3_proof

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/S8.lean (declarations already in the chain dropped) -/

/-! # period-glue: `S8Nonzero` reduced to a statement about one explicit matrix

Task period-glue, 2026-11-13. `S8Nonzero` (period-map, `PGLight`, unchanged) says
`Σ_{m even} θ_m(Ω(√2 + i))⁸ ≠ 0`. Proved here: `Ω(√2 + i) = Ω₀ := [[(−1+i)/2, 1], [1, −1+i]]`
exactly (`omega_cm4`), so `S8Nonzero ⇔ S8Omega0` (`s8Nonzero_iff`). `S8Omega0` is a statement about
theta constants at an explicit point of `𝔥₂` with `Im Ω₀ = diag(1/2, 1)`; its certificate is in
`docs/research/period-glue.md` §3 (`py/s8_exact.py`): `Σθ⁸(Ω₀) = −9 ϑ₀₀(i)¹⁶` numerically to 60
digits, each `θ_m(Ω₀)⁸ ∈ {−¼, −1, −4, 0}·ϑ₀₀(i)¹⁶`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

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

/-! ## `S8Omega0` proved: every `θ_m(Ω₀)⁸` has non-positive real part

Proof (no numerics beyond crude bounds on `e^{−π/2}`):
* `(Ω₀)₀₁ = 1` makes each theta constant a product of two one-variable theta series,
  `θ_m(Ω₀) = u·Θ[a₁, b₁+a₂](τ₁)·Θ[a₂, b₂+a₁](τ₂)` with `τ₁ = (−1+i)/2`, `τ₂ = −1+i`, `u⁸ = 1`
  (`thetaConst_factor`);
* at `τ₂` every term of `Θ[a,b]` is a fixed eighth root of unity times a real number, so
  `Θ[a,b](τ₂)⁸ ≥ 0` is real (`th1_τ2`);
* at `τ₁`, `Θ[1,b](τ₁) = ω·R` with `ω⁸ = −1`, `R` real (`th1_τ1_one`), and
  `Θ[0,b](τ₁) = P + σ E i` with `σ = ±1`, `1 ≤ P ≤ 1 + 2q³/(1−q²)`, `2q ≤ E ≤ 2q/(1−q²)`,
  `q = e^{−π/2} ∈ [0.173, 0.2798]`; then `Re (P + σEi)⁸ < 0` (`re_th1_τ1_zero`);
* so `Re θ_m(Ω₀)⁸ ≤ 0` for every characteristic, `< 0` for `m = ((0,0),(0,1))`. -/

open Real in
/-- `τ₁ = (−1+i)/2`. -/
def τ1 : ℂ := (-1 + I) / 2
/-- `τ₂ = −1+i`. -/
def τ2 : ℂ := -1 + I

theorem τ1_im : 0 < τ1.im := by simp [τ1]
theorem τ2_im : 0 < τ2.im := by simp [τ2]

/-- The terms of the one-variable theta series with characteristic `[a/2, b/2]`. -/
def thT (a b : ℕ) (τ : ℂ) (n : ℤ) : ℂ :=
  cexp (Real.pi * I * ((n : ℂ) + (a : ℂ) / 2) ^ 2 * τ +
    Real.pi * I * ((n : ℂ) + (a : ℂ) / 2) * (b : ℂ))

/-- `Θ[a, b](τ) = Σ_n exp(πi(n + a/2)²τ + πi(n + a/2)b)`. -/
def th1 (a b : ℕ) (τ : ℂ) : ℂ := ∑' n : ℤ, thT a b τ n

theorem thT_eq_jac (a b : ℕ) (τ : ℂ) (n : ℤ) :
    thT a b τ n = cexp (Real.pi * I * (a : ℂ) ^ 2 * τ / 4 + Real.pi * I * (a : ℂ) * b / 2) *
      jacobiTheta₂_term n (((a : ℂ) * τ + b) / 2) τ := by
  unfold thT jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

theorem summable_thT (a b : ℕ) {τ : ℂ} (hτ : 0 < τ.im) : Summable (thT a b τ) := by
  have h := ((summable_jacobiTheta₂_term_iff (((a : ℂ) * τ + b) / 2) τ).mpr hτ).mul_left
    (cexp (Real.pi * I * (a : ℂ) ^ 2 * τ / 4 + Real.pi * I * (a : ℂ) * b / 2))
  convert h using 1
  funext n
  exact thT_eq_jac a b τ n

theorem summable_norm_thT (a b : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n => ‖thT a b τ n‖) :=
  summable_norm_iff.mpr (summable_thT a b hτ)

/-- **Factorization at `Ω₀` (proved).** -/
theorem thetaConst_factor (m : PkgI1.Char2) :
    PkgI1.thetaConst m Omega0 =
      cexp (-(Real.pi * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) *
        (th1 (m.1 0 : ℕ) ((m.2 0 : ℕ) + (m.1 1 : ℕ)) τ1 *
          th1 (m.1 1 : ℕ) ((m.2 1 : ℕ) + (m.1 0 : ℕ)) τ2) := by
  unfold PkgI1.thetaConst th1
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_thT _ _ τ1_im) (summable_norm_thT _ _ τ2_im),
    ← tsum_mul_left, ← (piFinTwoEquiv fun _ => ℤ).symm.tsum_eq]
  congr 1
  funext p
  simp only [piFinTwoEquiv_symm_apply, thT]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨p.1 * p.2, ?_⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Omega0, τ1, τ2, Fin.cons_zero,
    Fin.cons_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  ring

/-! ### Phases of the one-variable terms -/

theorem exp_int_piI (k : ℤ) : cexp ((k : ℂ) * (Real.pi * I)) = (-1) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- A tsum of terms `ω · (real)` is `ω · (real)`. -/
theorem tsum_ofReal_mul (ω : ℂ) (f : ℤ → ℂ) (h : ∀ n, ∃ r : ℝ, f n = ω * r) :
    ∃ ρ : ℝ, ∑' n, f n = ω * ρ := by
  choose r hr using h
  refine ⟨∑' n, r n, ?_⟩
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr hr

theorem thT_τ2_zero (b : ℕ) (n : ℤ) :
    thT 0 b τ2 n = (((-1 : ℝ) ^ (n * (b : ℤ) - n ^ 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
  have e : Real.pi * I * ((n : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ2 +
      Real.pi * I * ((n : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) + ((n * (b : ℤ) - n ^ 2 : ℤ) : ℂ) * (Real.pi * I) := by
    simp only [τ2]; push_cast
    linear_combination (Real.pi * (n : ℂ) ^ 2) * Complex.I_sq
  unfold thT
  rw [e, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem thT_τ2_one (b : ℕ) (n : ℤ) :
    thT 1 b τ2 n = cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) *
      (((-1 : ℝ) ^ (n * (b : ℤ) - n ^ 2 - n) *
        Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2) : ℝ) : ℂ) := by
  have e : Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ2 +
      Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) +
        ((n * (b : ℤ) - n ^ 2 - n : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * ((b : ℂ) / 2 - 1 / 4) := by
    simp only [τ2]; push_cast
    linear_combination (Real.pi * ((n : ℂ) + 1 / 2) ^ 2) * Complex.I_sq
  unfold thT
  rw [e, Complex.exp_add, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem thT_τ1_one (b : ℕ) (n : ℤ) : ∃ r : ℝ,
    thT 1 b τ1 n = cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) * r := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hk' : (n : ℂ) ^ 2 + n = 2 * k := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hk
    push_cast at this; linear_combination this
  refine ⟨(-1 : ℝ) ^ (n * (b : ℤ) - k) * Real.exp (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 / 2), ?_⟩
  have e : Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * ((n : ℂ) + ((1 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 / 2 : ℝ) : ℂ) +
        ((n * (b : ℤ) - k : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * ((b : ℂ) / 2 - 1 / 8) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * ((n : ℂ) + 1 / 2) ^ 2 / 2) * Complex.I_sq +
      (-(Real.pi * I) / 2) * hk'
  unfold thT
  rw [e, Complex.exp_add, Complex.exp_add, exp_int_piI, ← Complex.ofReal_exp]
  push_cast; ring

theorem omega_τ2_pow (b : ℕ) : cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * (Real.pi * I * ((b : ℂ) / 2 - 1 / 4)) =
      ((4 * (b : ℤ) - 2 : ℤ) : ℂ) * (Real.pi * I) := by push_cast; ring
  rw [this, exp_int_piI]
  exact Even.neg_one_zpow ⟨2 * (b : ℤ) - 1, by ring⟩

theorem omega_τ1_pow (b : ℕ) : cexp (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) ^ 8 = -1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * (Real.pi * I * ((b : ℂ) / 2 - 1 / 8)) =
      ((4 * (b : ℤ) - 1 : ℤ) : ℂ) * (Real.pi * I) := by push_cast; ring
  rw [this, exp_int_piI]
  exact Odd.neg_one_zpow ⟨2 * (b : ℤ) - 1, by ring⟩

/-- `Θ[a,b](τ₂)⁸` is a non-negative real number (`a ∈ {0, 1}`). -/
theorem th1_τ2 (a b : ℕ) (ha : a = 0 ∨ a = 1) : ∃ ρ : ℝ, th1 a b τ2 ^ 8 = ((ρ ^ 8 : ℝ) : ℂ) := by
  rcases ha with rfl | rfl
  · obtain ⟨ρ, hρ⟩ := tsum_ofReal_mul 1 (thT 0 b τ2) fun n => ⟨_, by rw [thT_τ2_zero, one_mul]⟩
    refine ⟨ρ, ?_⟩
    unfold th1; rw [hρ, one_mul]; push_cast; ring
  · obtain ⟨ρ, hρ⟩ := tsum_ofReal_mul _ (thT 1 b τ2) fun n => ⟨_, thT_τ2_one b n⟩
    refine ⟨ρ, ?_⟩
    unfold th1; rw [hρ, mul_pow, omega_τ2_pow, one_mul]; push_cast; ring

/-- `Θ[1,b](τ₁)⁸ = −R⁸` with `R` real. -/
theorem th1_τ1_one (b : ℕ) : ∃ R : ℝ, th1 1 b τ1 ^ 8 = -((R ^ 8 : ℝ) : ℂ) := by
  obtain ⟨R, hR⟩ := tsum_ofReal_mul _ (thT 1 b τ1) (thT_τ1_one b)
  refine ⟨R, ?_⟩
  unfold th1; rw [hR, mul_pow, omega_τ1_pow]; push_cast; ring

/-! ### `Θ[0,b](τ₁)`: real and imaginary parts -/

/-- `E(n) = e^{−πn²/2} = |Θ[0,b](τ₁)`'s `n`-th term`|`. -/
def Eg (n : ℤ) : ℝ := Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)

theorem thT_τ1_zero_even (b : ℕ) (m : ℤ) : thT 0 b τ1 (2 * m) = ((Eg (2 * m) : ℝ) : ℂ) := by
  have e : Real.pi * I * (((2 * m : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * (((2 * m : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((2 * m : ℤ) : ℝ) ^ 2 / 2 : ℝ) : ℂ) +
        ((2 * (m * (b : ℤ) - m ^ 2) : ℤ) : ℂ) * (Real.pi * I) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * (2 * (m : ℂ)) ^ 2 / 2) * Complex.I_sq
  unfold thT Eg
  rw [e, Complex.exp_add, exp_int_piI, Even.neg_one_zpow ⟨m * (b : ℤ) - m ^ 2, by ring⟩, mul_one,
    ← Complex.ofReal_exp]

theorem exp_neg_pi_div_two_I : cexp (Real.pi * I * (-1 / 2)) = -I := by
  have : Real.pi * I * (-1 / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem thT_τ1_zero_odd (b : ℕ) (m : ℤ) :
    thT 0 b τ1 (2 * m + 1) = ((Eg (2 * m + 1) : ℝ) : ℂ) * ((((-1 : ℝ) ^ b : ℝ) : ℂ) * (-I)) := by
  have e : Real.pi * I * (((2 * m + 1 : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) ^ 2 * τ1 +
      Real.pi * I * (((2 * m + 1 : ℤ) : ℂ) + ((0 : ℕ) : ℂ) / 2) * (b : ℂ) =
      ((-Real.pi * ((2 * m + 1 : ℤ) : ℝ) ^ 2 / 2 : ℝ) : ℂ) +
        ((2 * (m * (b : ℤ) - m ^ 2 - m) : ℤ) : ℂ) * (Real.pi * I) + ((b : ℤ) : ℂ) * (Real.pi * I) +
        Real.pi * I * (-1 / 2) := by
    simp only [τ1]; push_cast
    linear_combination (Real.pi * (2 * (m : ℂ) + 1) ^ 2 / 2) * Complex.I_sq
  unfold thT Eg
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_add, exp_int_piI, exp_int_piI,
    Even.neg_one_zpow ⟨m * (b : ℤ) - m ^ 2 - m, by ring⟩, exp_neg_pi_div_two_I,
    ← Complex.ofReal_exp, zpow_natCast]
  push_cast; ring

theorem Eg_nonneg (n : ℤ) : 0 ≤ Eg n := (Real.exp_pos _).le

/-- The real part, the sign `σ` and the (non-negative) imaginary weight of the terms. -/
theorem thT_τ1_zero_parts (b : ℕ) (n : ℤ) :
    0 ≤ (thT 0 b τ1 n).re ∧ 0 ≤ (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im ∧
      (thT 0 b τ1 n).re + (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im = Eg n := by
  have hb : ((-1 : ℝ) ^ b) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · rw [thT_τ1_zero_even]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, le_refl, and_true]
    exact Eg_nonneg _
  · rw [thT_τ1_zero_odd]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    refine ⟨by simp, ?_, ?_⟩
    · have := Eg_nonneg (2 * m + 1)
      nlinarith [hb]
    · linear_combination (Eg (2 * m + 1)) * hb

theorem thT_τ1_zero_at0 (b : ℕ) : (thT 0 b τ1 0).re = 1 := by
  have := thT_τ1_zero_even b 0
  rw [mul_zero] at this
  rw [this]; simp [Eg]

theorem thT_τ1_zero_at1 (b : ℕ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    (-(-1 : ℝ) ^ b) * (thT 0 b τ1 n).im = Real.exp (-Real.pi / 2) := by
  have hb : ((-1 : ℝ) ^ b) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have key : ∀ m : ℤ, (2 * m + 1 = 1 ∨ 2 * m + 1 = -1) →
      (-(-1 : ℝ) ^ b) * (thT 0 b τ1 (2 * m + 1)).im = Real.exp (-Real.pi / 2) := by
    intro m hm
    rw [thT_τ1_zero_odd]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    have hE : Eg (2 * m + 1) = Real.exp (-Real.pi / 2) := by
      unfold Eg; congr 1
      rcases hm with h | h <;> rw [show (((2 * m + 1 : ℤ)) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) from rfl, h] <;>
        push_cast <;> ring
    rw [hE]; linear_combination (Real.exp (-Real.pi / 2)) * hb
  rcases hn with rfl | rfl
  · have h := key 0 (by norm_num)
    rwa [show (2 * 0 + 1 : ℤ) = 1 by norm_num] at h
  · have h := key (-1) (by norm_num)
    rwa [show (2 * (-1) + 1 : ℤ) = -1 by norm_num] at h

/-! ### Crude bounds and the sign of `Re Θ[0,b](τ₁)⁸` -/

theorem hasSum_geom_int {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    HasSum (fun n : ℤ => s ^ n.natAbs) ((1 - s)⁻¹ + s * (1 - s)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · convert hasSum_geometric_of_lt_one h0 h1 using 1
    funext n; simp
  · convert (hasSum_geometric_of_lt_one h0 h1).mul_left s using 1
    funext n
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]

theorem Eg_le (n : ℤ) : Eg n ≤ Real.exp (Real.pi / 2) * Real.exp (-Real.pi) ^ n.natAbs -
    (if n = 0 then Real.exp (Real.pi / 2) - 1 else 0) := by
  by_cases hn : n = 0
  · subst hn; simp [Eg]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hn), sub_zero, ← Real.exp_nat_mul, ← Real.exp_add]
    unfold Eg
    apply Real.exp_le_exp.mpr
    have ha : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [ha]
    nlinarith [Real.pi_pos, sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]

theorem re_pow8 (x y : ℝ) : (((x : ℂ) + (y : ℂ) * I) ^ 8).re =
    x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem q_lower : (0.173 : ℝ) ≤ Real.exp (-Real.pi / 2) := by
  have h8 : Real.exp (-Real.pi / 2) = Real.exp (-Real.pi / 16) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 - Real.pi / 16 ≤ Real.exp (-Real.pi / 16) := by
    have := Real.add_one_le_exp (-Real.pi / 16); linarith
  have h2 : (0.803125 : ℝ) ≤ 1 - Real.pi / 16 := by have := Real.pi_lt_d2; linarith
  rw [h8]
  calc (0.173 : ℝ) ≤ 0.803125 ^ 8 := by norm_num
    _ ≤ Real.exp (-Real.pi / 16) ^ 8 := pow_le_pow_left₀ (by norm_num) (h2.trans h1) 8

theorem q_upper : Real.exp (-Real.pi / 2) ≤ (0.2532 : ℝ) := by
  have h8 : Real.exp (Real.pi / 2) = Real.exp (Real.pi / 16) ^ 8 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 + Real.pi / 16 ≤ Real.exp (Real.pi / 16) := by
    have := Real.add_one_le_exp (Real.pi / 16); linarith
  have h2 : (1.1875 : ℝ) ≤ 1 + Real.pi / 16 := by have := Real.pi_gt_three; linarith
  have h3 : (3.95 : ℝ) ≤ Real.exp (Real.pi / 2) := by
    rw [h8]
    calc (3.95 : ℝ) ≤ 1.1875 ^ 8 := by norm_num
      _ ≤ Real.exp (Real.pi / 16) ^ 8 := pow_le_pow_left₀ (by norm_num) (h2.trans h1) 8
  have h4 : Real.exp (-Real.pi / 2) = (Real.exp (Real.pi / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h4]
  calc (Real.exp (Real.pi / 2))⁻¹ ≤ (3.95 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    _ ≤ 0.2532 := by norm_num

theorem poly8_neg (p u : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 1.0707) (hu1 : 0.1197 ≤ u)
    (hu2 : u ≤ 0.2928) :
    p ^ 4 - 28 * p ^ 3 * u + 70 * p ^ 2 * u ^ 2 - 28 * p * u ^ 3 + u ^ 4 < 0 := by
  have h1 : 0 ≤ u - 0.11 * p := by linarith
  have h2 : 0 ≤ 0.293 * p - u := by linarith
  have h3 : 0 < p * (1.2561 * p - 0.21 * u) := mul_pos (by linarith) (by linarith)
  have key : p ^ 2 - 28 * p * u + 70 * u ^ 2 < 0 := by nlinarith [mul_nonneg h1 h2]
  have hu3 : 0 ≤ u ^ 3 * (28 * p - u) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 < p ^ 2 * -(p ^ 2 - 28 * p * u + 70 * u ^ 2) :=
    mul_pos (by positivity) (neg_pos.mpr key)
  nlinarith [h4, hu3]

theorem q_frac_bounds (q : ℝ) (hq1 : 0.173 ≤ q) (hq2 : q ≤ 0.2532) :
    2 * q ^ 3 / (1 - q ^ 2) ≤ 0.0347 ∧ 2 * q / (1 - q ^ 2) ≤ 0.5411 := by
  have h0 : 0 ≤ q := by linarith
  have hq2' : q ^ 2 ≤ 0.2532 ^ 2 := pow_le_pow_left₀ h0 hq2 2
  have hq3 : q ^ 3 ≤ 0.2532 ^ 3 := pow_le_pow_left₀ h0 hq2 3
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  constructor
  · rw [div_le_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

set_option maxHeartbeats 1000000 in
/-- **`Re Θ[0,b](τ₁)⁸ < 0` (proved).** -/
theorem re_th1_τ1_zero (b : ℕ) : (th1 0 b τ1 ^ 8).re < 0 := by
  set σ : ℝ := -(-1 : ℝ) ^ b with hσdef
  have hσ : σ ^ 2 = 1 := by
    rw [hσdef, neg_sq, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hsum := summable_thT 0 b τ1_im
  have hre : Summable (fun n => (thT 0 b τ1 n).re) := Complex.reCLM.summable hsum
  have him : Summable (fun n => (thT 0 b τ1 n).im) := Complex.imCLM.summable hsum
  have hen : Summable (fun n => σ * (thT 0 b τ1 n).im) := him.mul_left σ
  set P := ∑' n, (thT 0 b τ1 n).re with hPdef
  set Es := ∑' n, σ * (thT 0 b τ1 n).im with hEdef
  have hΘ : th1 0 b τ1 = (P : ℂ) + ((σ * Es : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [th1, Complex.re_tsum hsum, hPdef]
    · simp only [th1, Complex.im_tsum hsum, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, hEdef]
      rw [tsum_mul_left, ← mul_assoc, ← sq, hσ, one_mul]
      simp
  have hP1 : 1 ≤ P := by
    rw [← thT_τ1_zero_at0 b]
    exact hre.le_tsum 0 (fun j _ => (thT_τ1_zero_parts b j).1)
  set q := Real.exp (-Real.pi / 2) with hq
  have hE1 : 2 * q ≤ Es := by
    have := hen.sum_le_tsum {1, -1} (fun j _ => (thT_τ1_zero_parts b j).2.1)
    rw [Finset.sum_pair (by norm_num), thT_τ1_zero_at1 b 1 (Or.inl rfl),
      thT_τ1_zero_at1 b (-1) (Or.inr rfl)] at this
    linarith
  have hq1 := q_lower
  have hq2 := q_upper
  rw [← hq] at hq1 hq2
  have hs : Real.exp (-Real.pi) = q ^ 2 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hqi : Real.exp (Real.pi / 2) = q⁻¹ := by
    rw [hq, ← Real.exp_neg]; congr 1; ring
  have hs1 : q ^ 2 < 1 := by nlinarith
  have hM := ((hasSum_geom_int (s := Real.exp (-Real.pi)) (Real.exp_pos _).le
    (by rw [hs]; exact hs1)).mul_left (Real.exp (Real.pi / 2))).sub
    (hasSum_ite_eq (0 : ℤ) (Real.exp (Real.pi / 2) - 1))
  have hG : P + Es ≤ 1 + 2 * q / (1 - q ^ 2) := by
    rw [hPdef, hEdef, ← hre.tsum_add hen]
    refine ((hre.add hen).tsum_le_tsum (fun n => ?_) hM.summable).trans (le_of_eq ?_)
    · rw [(thT_τ1_zero_parts b n).2.2]
      exact Eg_le n
    · rw [hM.tsum_eq, hs, hqi]
      have hq0 : q ≠ 0 := (Real.exp_pos _).ne'
      have h1q : 1 - q ^ 2 ≠ 0 := by nlinarith
      field_simp
      ring
  have hPup : P ≤ 1 + 2 * q ^ 3 / (1 - q ^ 2) := by
    have h1q : 0 < 1 - q ^ 2 := by nlinarith
    have : 2 * q / (1 - q ^ 2) - 2 * q = 2 * q ^ 3 / (1 - q ^ 2) := by
      field_simp; ring
    linarith
  obtain ⟨hb1, hb2⟩ := q_frac_bounds q hq1 hq2
  have hPb : P ≤ 1.0347 := by linarith
  have hEb : Es ≤ 0.5411 := by linarith
  have hEl : 0.346 ≤ Es := by linarith
  rw [hΘ, re_pow8]
  set p := P ^ 2 with hp
  set u := Es ^ 2 with hu
  have e : P ^ 8 - 28 * P ^ 6 * (σ * Es) ^ 2 + 70 * P ^ 4 * (σ * Es) ^ 4 -
      28 * P ^ 2 * (σ * Es) ^ 6 + (σ * Es) ^ 8 =
      p ^ 4 - 28 * p ^ 3 * u + 70 * p ^ 2 * u ^ 2 - 28 * p * u ^ 3 + u ^ 4 := by
    have h2 : (σ * Es) ^ 2 = u := by rw [mul_pow, hσ, one_mul]
    have h4 : (σ * Es) ^ 4 = u ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
    have h6 : (σ * Es) ^ 6 = u ^ 3 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2]
    have h8 : (σ * Es) ^ 8 = u ^ 4 := by rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, h2]
    rw [h2, h4, h6, h8, hp]; ring
  rw [e]
  have hP0 : 0 ≤ P := by linarith
  have hE0 : 0 ≤ Es := by linarith
  exact poly8_neg p u (by rw [hp]; nlinarith) (by rw [hp]; nlinarith) (by rw [hu]; nlinarith)
    (by rw [hu]; nlinarith)

/-! ### Assembly -/

theorem fin2_val (x : Fin 2) : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by have := x.isLt; omega

theorem u_pow8 (a1 a2 : ℕ) :
    cexp (-(Real.pi * I * (a1 : ℂ) * (a2 : ℂ) / 2)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : ((8 : ℕ) : ℂ) * -(Real.pi * I * (a1 : ℂ) * (a2 : ℂ) / 2) =
      ((-2 * (a1 : ℤ) * a2 : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **Every `θ_m(Ω₀)⁸` has non-positive real part (proved).** -/
theorem re_theta8_nonpos (m : PkgI1.Char2) : (PkgI1.thetaConst m Omega0 ^ 8).re ≤ 0 := by
  rw [thetaConst_factor, mul_pow, u_pow8, one_mul, mul_pow]
  obtain ⟨ρ, hρ⟩ := th1_τ2 (m.1 1 : ℕ) ((m.2 1 : ℕ) + (m.1 0 : ℕ)) (fin2_val _)
  rw [hρ, Complex.re_mul_ofReal]
  have hρ8 : 0 ≤ ρ ^ 8 := Even.pow_nonneg ⟨4, by norm_num⟩ ρ
  rcases fin2_val (m.1 0) with h | h
  · rw [h]
    exact mul_nonpos_of_nonpos_of_nonneg (re_th1_τ1_zero _).le hρ8
  · rw [h]
    obtain ⟨R, hR⟩ := th1_τ1_one ((m.2 0 : ℕ) + (m.1 1 : ℕ))
    rw [hR]
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hR8 : 0 ≤ R ^ 8 := Even.pow_nonneg ⟨4, by norm_num⟩ R
    nlinarith [mul_nonneg hR8 hρ8]

/-- `Θ[0,1](τ₂) = Σ e^{−πn²} ≥ 1`. -/
theorem th1_τ2_01 : ∃ ρ : ℝ, 1 ≤ ρ ∧ th1 0 1 τ2 = ρ := by
  have hterm : ∀ n : ℤ, thT 0 1 τ2 n = ((Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [thT_τ2_zero]
    have hev : Even (n * ((1 : ℕ) : ℤ) - n ^ 2) := by
      obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
      exact ⟨-k, by push_cast; linear_combination (-1 : ℤ) * hk⟩
    rw [hev.neg_one_zpow, one_mul]
  have hsum := summable_thT 0 1 τ2_im
  have hre : Summable (fun n => (thT 0 1 τ2 n).re) := Complex.reCLM.summable hsum
  have hre' : ∀ n, (thT 0 1 τ2 n).re = Real.exp (-Real.pi * (n : ℝ) ^ 2) := fun n => by
    rw [hterm, Complex.ofReal_re]
  refine ⟨∑' n, (thT 0 1 τ2 n).re, ?_, ?_⟩
  · have h0 := hre.le_tsum 0 (fun j _ => by rw [hre']; exact (Real.exp_pos _).le)
    rw [hre'] at h0
    simpa using h0
  · rw [Complex.ofReal_tsum]
    unfold th1
    exact tsum_congr fun n => by rw [hre', hterm]

/-- The characteristic `((0,0),(0,1))`. -/
def m0 : PkgI1.Char2 := (![0, 0], ![0, 1])

theorem re_theta8_m0 : (PkgI1.thetaConst m0 Omega0 ^ 8).re < 0 := by
  rw [thetaConst_factor, mul_pow, u_pow8, one_mul, mul_pow]
  have e1 : ((m0.1 0 : Fin 2) : ℕ) = 0 := rfl
  have e2 : ((m0.1 1 : Fin 2) : ℕ) = 0 := rfl
  have e3 : ((m0.2 0 : Fin 2) : ℕ) = 0 := rfl
  have e4 : ((m0.2 1 : Fin 2) : ℕ) = 1 := rfl
  rw [e1, e2, e3, e4]
  obtain ⟨ρ, hρ1, hρ⟩ := th1_τ2_01
  rw [show (1 + 0 : ℕ) = 1 from rfl, show (0 + 0 : ℕ) = 0 from rfl, hρ, ← Complex.ofReal_pow,
    Complex.re_mul_ofReal]
  have : 0 < ρ ^ 8 := by positivity
  exact mul_neg_of_neg_of_pos (re_th1_τ1_zero 0) this

/-- **`S8Omega0` (proved): `Re Σθ⁸(Ω₀) < 0`.** -/
theorem s8Omega0_re_neg : (PkgI1.thetaSum8 Omega0).re < 0 := by
  unfold PkgI1.thetaSum8
  rw [Complex.re_sum]
  have hm0 : m0 ∈ PkgI1.evenChars := by decide
  rw [← Finset.add_sum_erase _ _ hm0]
  have hrest : ∑ x ∈ PkgI1.evenChars.erase m0, (PkgI1.thetaConst x Omega0 ^ 8).re ≤ 0 :=
    Finset.sum_nonpos fun m _ => re_theta8_nonpos m
  linarith [re_theta8_m0]

theorem s8Omega0_proof : S8Omega0 := fun h => by
  have := s8Omega0_re_neg
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **`S8Nonzero` (proved).** -/
theorem s8Nonzero_proof : S8Nonzero := s8Nonzero_of s8Omega0_proof

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/W8.lean (declarations already in the chain dropped) -/

/-! # period-glue: `S8WeightExact` from Igusa's `ThetaModularity` and the generation of `Γ*`

Task period-glue, 2026-11-13. `S8WeightExact` (period-map, `PGLight`, unchanged) is proved from
* `PkgI1.ThetaModularity` (**LEAF**, Igusa; pkg-I1's statement, unchanged), and
* `GammaStarGen` (**LEAF candidate**: `Γ* = ℚ^×·⟨ι(1+i+j), ι((j−3)/2)⟩`, a consequence of the
  published signature `(0; 2, 4, 6)` of `Γ*/ℚ^×` with Poincaré's polygon theorem; flagged for a
  human check),
by `s8WeightExact_of`. Proved here, with no other input:
* the elements of `GL₂(ℝ)⁺` for which `G8` has the exact automorphy form a subgroup
  (`G8AutoSubgroup`; the cocycle of `denom`), containing the rational scalars;
* the modular embedding of the two generators: explicit `M ∈ Sp₄(ℤ)` with
  `Ω(gτ) = M·Ω(τ)` and `det g · det(CΩ(τ) + D)(τ−3)(τ+1) = −(cτ+d)²(gτ−3)(gτ+1)`
  (`py/modemb.py` found them; the `linear_combination` coefficients are from `py/w8_lean.py`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap
open UpperHalfPlane (num denom σ coe_smul_of_det_pos denom_ne_zero)

/-! ### The automorphy subgroup -/

/-- `g ∈ GL₂(ℝ)⁺` and `G8` has the exact automorphy of `S8WeightExact` for `g`. -/
def G8Auto (γ : GL (Fin 2) ℝ) : Prop :=
  0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ∧ ∀ z : UpperHalfPlane,
    G8 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ z ^ 8 * G8 (z : ℂ)

theorem detv (g : GL (Fin 2) ℝ) : (g.det : ℝ) = (g : Matrix (Fin 2) (Fin 2) ℝ).det :=
  Matrix.GeneralLinearGroup.val_det_apply g

theorem σ_of_pos {g : GL (Fin 2) ℝ} (h : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (w : ℂ) :
    σ g w = w := by
  have h' : 0 < (g.det : ℝ) := by rwa [detv]
  simp only [σ, if_pos h', ContinuousAlgEquiv.refl_apply]

theorem denom_mul_pos (g h : GL (Fin 2) ℝ) (hh : 0 < (h : Matrix (Fin 2) (Fin 2) ℝ).det)
    (z : UpperHalfPlane) : denom (g * h) z = denom g ((h • z : UpperHalfPlane) : ℂ) * denom h z := by
  rw [UpperHalfPlane.denom_cocycle_σ, σ_of_pos hh]

theorem g8Auto_one : G8Auto 1 := by
  refine ⟨by simp, fun z => ?_⟩
  simp [UpperHalfPlane.denom]

theorem g8Auto_mul {g h : GL (Fin 2) ℝ} (hg : G8Auto g) (hh : G8Auto h) : G8Auto (g * h) := by
  refine ⟨by rw [Units.val_mul, det_mul]; exact mul_pos hg.1 hh.1, fun z => ?_⟩
  rw [mul_smul, denom_mul_pos g h hh.1, Units.val_mul, det_mul]
  have e1 := hg.2 (h • z)
  have e2 := hh.2 z
  push_cast
  calc G8 ((g • h • z : UpperHalfPlane) : ℂ) *
        (((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^ 4
      = (G8 ((g • h • z : UpperHalfPlane) : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4 := by ring
    _ = denom g ((h • z : UpperHalfPlane) : ℂ) ^ 8 * (G8 ((h • z : UpperHalfPlane) : ℂ) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4) := by rw [e1]; ring
    _ = _ := by rw [e2]; ring

theorem g8Auto_inv {g : GL (Fin 2) ℝ} (hg : G8Auto g) : G8Auto g⁻¹ := by
  have hd : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨by rw [hd]; exact inv_pos.mpr hg.1, fun z => ?_⟩
  set z' := g⁻¹ • z with hz'
  have e := hg.2 z'
  rw [hz', smul_inv_smul] at e
  have hc := denom_mul_pos g g⁻¹ (by rw [hd]; exact inv_pos.mpr hg.1) z
  rw [mul_inv_cancel] at hc
  have h1 : denom (1 : GL (Fin 2) ℝ) z = 1 := by simp [UpperHalfPlane.denom]
  rw [h1] at hc
  have hD : denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ≠ 0 := by exact_mod_cast hg.1.ne'
  rw [hd]
  push_cast
  have key : G8 ((g⁻¹ • z : UpperHalfPlane) : ℂ) = G8 (z : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4 /
      denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ^ 8 := by
    rw [eq_div_iff (pow_ne_zero _ hD), e]; ring
  rw [key]
  have hinv : denom g⁻¹ z = (denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ))⁻¹ :=
    (eq_inv_of_mul_eq_one_right hc.symm)
  rw [hinv]
  field_simp

theorem g8Auto_scalar {g : GL (Fin 2) ℝ} (q : ℚ) (hq : q ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1) : G8Auto g := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = (q : ℝ) ^ 2 := by
    rw [hg, Matrix.det_smul, Matrix.det_one]; simp
  have hpos : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; positivity
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by rw [hg]; simp
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg]; simp
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hg]; simp
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = q := by rw [hg]; simp
  refine ⟨hpos, fun z => ?_⟩
  have hden : denom g z = (q : ℂ) := by simp [UpperHalfPlane.denom, e10, e11]
  have hsm : g • z = z := by
    ext1
    rw [coe_smul_of_det_pos (by rwa [detv]), hden]
    simp only [UpperHalfPlane.num, e00, e01]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    field_simp
    push_cast; ring
  rw [hsm, hden, hdet]
  push_cast; ring

/-- The automorphy group of `G8` (a subgroup of `GL₂(ℝ)⁺`). -/
def G8AutoSubgroup : Subgroup (GL (Fin 2) ℝ) where
  carrier := {γ | G8Auto γ}
  one_mem' := g8Auto_one
  mul_mem' := g8Auto_mul
  inv_mem' := g8Auto_inv

/-! ### From the modular embedding of one element to its automorphy -/

theorem dF_ne {z : ℂ} (hz : 0 < z.im) : dF z ≠ 0 := by
  unfold dF
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) h3) h4) two_ne_zero

theorem zz_ne {z : ℂ} (hz : 0 < z.im) : (z - 3) * (z + 1) ≠ 0 := by
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact mul_ne_zero h3 h4

theorem sub3_add1_ne {z : ℂ} (hz : 0 < z.im) : z - 3 ≠ 0 ∧ z + 1 ≠ 0 :=
  ⟨fun h => by have := congrArg Complex.im h; simp at this; linarith,
   fun h => by have := congrArg Complex.im h; simp at this; linarith⟩

theorem g8Auto_of_sp (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (hrel : ∀ z : ℂ, 0 < z.im →
      PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 4 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    G8Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := (hT M hM (PkgI1.Omega z) (omegaSiegel_proof z z.im_pos)).1
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold G8
  rw [hw, hmod]
  have hf4 : (PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 4 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 4 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  generalize num g z / denom g z = w at *
  field_simp
  linear_combination (PkgI1.thetaSum8 (PkgI1.Omega z)) * hf4

/-! ### The two generators -/

/-- `x₄ = 1 + i + j` (reduced norm 2; `ι(x₄)` is elliptic of order 4 in `PSL₂(ℝ)`, fixing
`√2 + i`). -/
def x4 : PkgI1.B := ⟨1, 1, 1, 0⟩
/-- `x₆ = (j − 3)/2 = j(1+j)/2` (reduced norm 3; `ι(x₆)` is elliptic of order 6, fixing `i√3`). -/
def x6 : PkgI1.B := ⟨-3 / 2, 0, 1 / 2, 0⟩

/-- `Nf` homogenized: `V²·Nf(W/V)`. -/
def Nfh (W V : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(√2 : ℂ) * (W ^ 2 / 2 + W * V - 3 / 2 * V ^ 2) - W ^ 2 / 2 - 3 / 2 * V ^ 2,
     (√2 : ℂ) * (-W ^ 2 / 2 - W * V + 3 / 2 * V ^ 2) + W ^ 2 + 3 * V ^ 2;
     (√2 : ℂ) * (-W ^ 2 / 2 - W * V + 3 / 2 * V ^ 2) + W ^ 2 + 3 * V ^ 2,
     (√2 : ℂ) * (W ^ 2 + 2 * W * V - 3 * V ^ 2) - W ^ 2 - 3 * V ^ 2]

/-- `dF` homogenized: `V²·dF(W/V)`. -/
def dFh (W V : ℂ) : ℂ := -(√2 : ℂ) * (W - 3 * V) * (W + V) / 2

theorem Nf_hom (W V : ℂ) (hV : V ≠ 0) : Nf (W / V) = (V ^ 2)⁻¹ • Nfh W V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nf, Nfh] <;> field_simp <;> ring

theorem dF_hom (W V : ℂ) (hV : V ≠ 0) : dF (W / V) = dFh W V / V ^ 2 := by
  simp only [dF, dFh]; field_simp

theorem omega_smul {z : ℂ} (hz : dF z ≠ 0) : PkgI1.Omega z = (dF z)⁻¹ • Nf z := by
  ext i j
  rw [omega_eq, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- **`spAct` from a polynomial identity (proved).** -/
theorem spAct_of_poly (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (z W V : ℂ) (hV : V ≠ 0) (hz : dF z ≠ 0) (hw : dF (W / V) ≠ 0)
    (hP : (C * Nf z + dF z • D).det ≠ 0)
    (hI : dFh W V • (A * Nf z + dF z • B) = Nfh W V * (C * Nf z + dF z • D)) :
    PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (W / V) := by
  unfold PkgI1.spAct
  simp only [hM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [omega_smul hz, omega_smul hw, Nf_hom W V hV, dF_hom W V hV]
  set c := (dF z)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hz
  set P := C * Nf z + dF z • D with hPdef
  set X := A * Nf z + dF z • B with hX
  have hZ : C * (c • Nf z) + D = c • P := by
    rw [hPdef, smul_add, smul_smul, hc, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  have hY : A * (c • Nf z) + B = c • X := by
    rw [hX, smul_add, smul_smul, hc, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  rw [hZ, hY]
  have hdetZ : (c • P).det ≠ 0 := by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) hP
  letI := Matrix.invertibleOfIsUnitDet (c • P) (isUnit_iff_ne_zero.mpr hdetZ)
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  have hdFh : dFh W V ≠ 0 := by
    intro h0; apply hw; rw [dF_hom W V hV, h0, zero_div]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hI.symm]
  match_scalars
  all_goals field_simp
  all_goals ring

/-! #### `g₄ = ι(1 + i + j)` -/

def A4 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def B4 : Matrix (Fin 2) (Fin 2) ℂ := !![1, -2; -2, 2]
def C4 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def D4 : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 2; 1, -1]
/-- The symplectic matrix of `g₄` (`py/modemb.py`). -/
def M4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  Matrix.fromBlocks !![1, 0; 0, 1] !![1, -2; -2, 2] !![0, 1; 1, 0] !![-1, 2; 1, -1]

theorem M4_map : M4.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A4 B4 C4 D4 := by
  unfold M4 A4 B4 C4 D4
  rw [Matrix.fromBlocks_map]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem M4_symp : M4 ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  unfold M4 Matrix.J
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_transpose]

theorem I1_g4 (z : ℂ) :
    dFh ((√2 : ℂ) * z + z - 3) (-(√2 : ℂ) + z + 1) • (A4 * Nf z + dF z • B4) =
      Nfh ((√2 : ℂ) * z + z - 3) (-(√2 : ℂ) + z + 1) * (C4 * Nf z + dF z • D4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A4, B4, C4, D4, Nf, Nfh, dF, dFh, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ((√2 : ℂ)^2*z^3 - 6*(√2 : ℂ)^2*z^2 - 3*(√2 : ℂ)^2*z - (√2 : ℂ)*z^4/2 +
      7*(√2 : ℂ)*z^3 + 21*(√2 : ℂ)*z + 9*(√2 : ℂ)/2 - 2*z^4 - 12*z^2 - 18) * sqrt2_sq
  · linear_combination (-(√2 : ℂ)^2*z^4/4 - 2*(√2 : ℂ)^2*z^3 + 21*(√2 : ℂ)^2*z^2/2 +
      6*(√2 : ℂ)^2*z - 9*(√2 : ℂ)^2/4 + (√2 : ℂ)*z^4/2 - 11*(√2 : ℂ)*z^3 - 33*(√2 : ℂ)*z -
      9*(√2 : ℂ)/2 + 3*z^4 + 18*z^2 + 27) * sqrt2_sq
  · linear_combination (-(√2 : ℂ)^2*z^4/4 - 2*(√2 : ℂ)^2*z^3 + 21*(√2 : ℂ)^2*z^2/2 +
      6*(√2 : ℂ)^2*z - 9*(√2 : ℂ)^2/4 + (√2 : ℂ)*z^4/2 - 11*(√2 : ℂ)*z^3 - 33*(√2 : ℂ)*z -
      9*(√2 : ℂ)/2 + 3*z^4 + 18*z^2 + 27) * sqrt2_sq
  · linear_combination (2*(√2 : ℂ)^2*z^3 - 12*(√2 : ℂ)^2*z^2 - 6*(√2 : ℂ)^2*z - (√2 : ℂ)*z^4 +
      14*(√2 : ℂ)*z^3 + 42*(√2 : ℂ)*z + 9*(√2 : ℂ) - 4*z^4 - 24*z^2 - 36) * sqrt2_sq

theorem I2_g4 (z : ℂ) :
    (C4 * Nf z + dF z • D4).det * 2 * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * ((((√2 : ℂ) * z + z - 3) - 3 * (-(√2 : ℂ) + z + 1)) *
        (((√2 : ℂ) * z + z - 3) + (-(√2 : ℂ) + z + 1))) := by
  rw [Matrix.det_fin_two]
  simp [C4, D4, Nf, dF, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination ((√2 : ℂ)^2*z^6/4 - (√2 : ℂ)^2*z^5/2 - 13*(√2 : ℂ)^2*z^4/4 +
    5*(√2 : ℂ)^2*z^3 + 39*(√2 : ℂ)^2*z^2/4 - 9*(√2 : ℂ)^2*z/2 - 27*(√2 : ℂ)^2/4 - z^6/2 + z^5 -
    3*z^4/2 + 6*z^3 + 9*z^2/2 + 9*z + 27/2) * sqrt2_sq

/-! #### `g₆ = ι((j − 3)/2)` -/

def A6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 0]
def B6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]
def C6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
def D6 : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 2; -1, 1]
/-- The symplectic matrix of `g₆` (`py/modemb.py`). -/
def M6 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  Matrix.fromBlocks !![0, 0; 0, 0] !![0, -1; 1, 0] !![0, 1; -1, 0] !![-1, 2; -1, 1]

theorem M6_map : M6.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A6 B6 C6 D6 := by
  unfold M6 A6 B6 C6 D6
  rw [Matrix.fromBlocks_map]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem M6_symp : M6 ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  unfold M6 Matrix.J
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_transpose]

theorem I1_g6 (z : ℂ) :
    dFh (-3 * z / 2 - 3 / 2) (z / 2 - 3 / 2) • (A6 * Nf z + dF z • B6) =
      Nfh (-3 * z / 2 - 3 / 2) (z / 2 - 3 / 2) * (C6 * Nf z + dF z • D6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, B6, C6, D6, Nf, Nfh, dF, dFh, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination (-3*z^4/4 - 9*z^2/2 - 27/4) * sqrt2_sq
  · linear_combination (3*z^4/4 + 9*z^2/2 + 27/4) * sqrt2_sq
  · ring

theorem I2_g6 (z : ℂ) :
    (C6 * Nf z + dF z • D6).det * 3 * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * (((-3 * z / 2 - 3 / 2) - 3 * (z / 2 - 3 / 2)) *
        ((-3 * z / 2 - 3 / 2) + (z / 2 - 3 / 2))) := by
  rw [Matrix.det_fin_two]
  simp [C6, D6, Nf, dF, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (3*z^6/4 - 3*z^5/2 + 9*z^4/4 - 9*z^3 - 27*z^2/4 - 27*z/2 - 81/4) * sqrt2_sq

/-! ### Assembly -/

/-- **The automorphy factor from a polynomial identity (proved).** -/
theorem spFactor_of_poly (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (z W V detg : ℂ) (hV : V ≠ 0) (hz : dF z ≠ 0)
    (hI2 : (C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * ((W - 3 * V) * (W + V))) :
    PkgI1.spFactor M (PkgI1.Omega z) * detg * ((z - 3) * (z + 1)) =
      -1 * V ^ 2 * ((W / V - 3) * (W / V + 1)) := by
  unfold PkgI1.spFactor
  simp only [hM, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [omega_smul hz]
  have hZ : C * ((dF z)⁻¹ • Nf z) + D = (dF z)⁻¹ • (C * Nf z + dF z • D) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  rw [hZ, Matrix.det_smul, Fintype.card_fin]
  calc (dF z)⁻¹ ^ 2 * (C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1))
      = (dF z)⁻¹ ^ 2 * ((C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1))) := by ring
    _ = _ := by rw [hI2]; field_simp

/-- `G8` has the exact automorphy for `g = ι(x)` once the modular embedding identities hold. -/
theorem g8Auto_gen (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hMs : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    G8Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g8Auto_of_sp hT g hdet M hMs (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem iota_x4 : PkgI1.iota x4 = !![1 + √2, -3; 1, 1 - √2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x4]

theorem iota_x6 : PkgI1.iota x6 = !![-3 / 2, -3 / 2; 1 / 2, -3 / 2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x6] <;> norm_num

theorem g8Auto_g4 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4) : G8Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen hT g (by rw [hdet]; norm_num) M4 M4_symp A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g8Auto_g6 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6) : G8Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen hT g (by rw [hdet]; norm_num) M6 M6_symp A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **LEAF candidate (generation of `Γ*`; flagged for a human check).** Every `γ ∈ Γ*` lies in
the subgroup of `GL₂(ℝ)` generated by `ι(1 + i + j)`, `ι((j − 3)/2)` and the rational scalars.

Source and derivation: `Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` (image in `PSL₂(ℝ)`) is a Fuchsian group of
signature `(0; 2, 4, 6)`, i.e. the `(2, 4, 6)` triangle group, of covolume
`2π(−2 + 1/2 + 3/4 + 5/6) = π/6` (Takeuchi, *Commensurability classes of arithmetic triangle
groups*, J. Fac. Sci. Univ. Tokyo 24 (1977), the class of `(2, 4, 6)` with quaternion algebra of
discriminant 6; Elkies, *Shimura curve computations*, ANTS 1998, §3 (`X*(6)` and the `(2,4,6)`
group); locators UNVERIFIED). Derivation of the stated form (model argument, numerics VERIFIED in
`py/triangle.py`): `g₄ = ι(1+i+j)` and `g₆ = ι((j−3)/2)` are elliptic of orders 4 and 6 in
`PSL₂(ℝ)` (`trd² / nrd = 2, 3`), fixing `√2 + i` and `i√3`; `x₂ = 2x₆x₄⁻¹ = (3/2)i + 2j + (1/2)ij`
has `trd = 0`, so `g₆g₄⁻¹` has order 2; the hyperbolic distance `d` of the two fixed points has
`cosh d = 1 + ((√2)² + (√3 − 1)²)/(2·√3) = √3 = cot(π/4)cot(π/6)`, which is the side of the
hyperbolic triangle with angles `π/4, π/6, π/2`. By Poincaré's polygon theorem (Beardon, *The
geometry of discrete groups*, §9.8 and §10.6, UNVERIFIED) `⟨g₄, g₆⟩` is the `(2,4,6)` triangle group
of that triangle, covolume `π/6`, so it has index 1 in `Γ*/ℚ^×`; an element of `N_B(𝒪)⁺` that is
a real multiple of a word in `x₄, x₆` is a rational multiple (the center of `B` is `ℚ`). -/
def GammaStarGen : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, γ ∈ Subgroup.closure
    ({γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4} ∪
      {γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6} ∪
      {γ : GL (Fin 2) ℝ | ∃ q : ℚ, q ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1})

/-- **`S8WeightExact` from Igusa's `ThetaModularity` and `GammaStarGen` (proved).** -/
theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact := by
  intro γ hγ z
  have hmem : γ ∈ G8AutoSubgroup := by
    refine (Subgroup.closure_le (K := G8AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g8Auto_g4 hT hg
    · exact g8Auto_g6 hT hg
    · exact g8Auto_scalar q hq hg
  exact hmem.2 z

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/SFA.lean (declarations already in the chain dropped) -/

/-! # period-glue: `SphereFactorAffine` from three textbook facts of one-variable complex analysis

Task period-glue, 2026-11-13. `SphereFactorAffine` (period-map, `PGLight`, unchanged) is proved
(`sphereFactorAffine_of`) from
* `HolP1OpenMap` (open mapping theorem for maps `ℍ → P¹`),
* `HolP1FactorHol` (a continuous `φ` with `h = φ ∘ f`, `f` onto and holomorphic, is
  holomorphic on `P¹`: local inverse off the critical values, removable singularities), and
* `SphereInjAffine` (an injective holomorphic self-map of `P¹` fixing `∞` is affine).
All three are **GLUE** (textbook complex analysis, not in Mathlib v4.35 in this form). Proved
here: holomorphy into `P¹` (`IsHolP1At`) implies continuity (`continuousAt_of_isHolP1At`); `φ`
is well defined, injective, continuous (`f` is open), and fixes `∞`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex Filter Topology HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap

/-- `g : ℂ → P¹(ℂ)` is holomorphic at `z` (the shape of `IsHolP1At`, on `ℂ`). -/
def IsHolC1At (g : ℂ → OnePoint ℂ) (z : ℂ) : Prop :=
  (∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ w in 𝓝 z, g w = (G w : OnePoint ℂ)) ∨
  (∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ G z = 0 ∧
      ∀ᶠ w in 𝓝 z, g w = if G w = 0 then OnePoint.infty else (((G w)⁻¹ : ℂ) : OnePoint ℂ))

/-- The chart of `P¹` at `∞`: `w ↦ 1/w`, `0 ↦ ∞`. -/
def chartInf (w : ℂ) : OnePoint ℂ := if w = 0 then OnePoint.infty else ((w⁻¹ : ℂ) : OnePoint ℂ)

/-- `φ : P¹ → P¹` is holomorphic: in the chart `ℂ` at every point, and in the chart at `∞`. -/
def IsHolSphere (φ : OnePoint ℂ → OnePoint ℂ) : Prop :=
  (∀ z : ℂ, IsHolC1At (fun w => φ (w : OnePoint ℂ)) z) ∧ IsHolC1At (fun w => φ (chartInf w)) 0

/-- **GLUE (open mapping theorem on `ℍ`, maps to `P¹`).** A map `g : ℍ → P¹(ℂ)` that is
holomorphic into `P¹` at every point and not constant is an open map.

Why true: `ℍ` is connected, so by the identity theorem (applied in charts) `g` is nowhere locally
constant; locally `g` or `1/g` is a non-constant analytic function, which is open (Mathlib:
`AnalyticOnNhd.is_constant_or_isOpen`), and `w ↦ 1/w` is a homeomorphism of `P¹`. (Ahlfors,
*Complex Analysis*, Ch. 4, §3.3; UNVERIFIED locator.) Size: small-medium. -/
def HolP1OpenMap : Prop :=
  ∀ g : UpperHalfPlane → OnePoint ℂ, (∀ τ, IsHolP1At g τ) → (∃ τ τ', g τ ≠ g τ') → IsOpenMap g

/-- **GLUE (holomorphic factorization).** If `f, h : ℍ → P¹(ℂ)` are holomorphic into `P¹`,
`f` is onto, and `h = φ ∘ f` with `φ : P¹ → P¹` continuous, then `φ` is holomorphic on `P¹`.

Why true: at `p = f(τ₀)`, the critical points of `f` near `τ₀` are isolated, so on a punctured
neighbourhood of `p` the map `φ = h ∘ f⁻¹` (local holomorphic inverse, Mathlib's
`HasStrictDerivAt.localInverse` in charts) is holomorphic; `φ` is continuous at `p`, so the
singularity is removable (Mathlib: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
applied to `φ` or `1/φ` in charts). (Ahlfors Ch. 4 §3.2-3.3; UNVERIFIED locators.)
Size: medium. -/
def HolP1FactorHol : Prop :=
  ∀ (f h : UpperHalfPlane → OnePoint ℂ) (φ : OnePoint ℂ → OnePoint ℂ),
    (∀ τ, IsHolP1At f τ) → (∀ τ, IsHolP1At h τ) → Function.Surjective f → Continuous φ →
    (∀ τ, h τ = φ (f τ)) → IsHolSphere φ

/-- **GLUE (textbook: injective holomorphic maps of the sphere).** An injective holomorphic
`φ : P¹ → P¹` with `φ(∞) = ∞` is `z ↦ az + b`, `a ≠ 0`.

Why true: `φ(ℂ) ⊆ ℂ` (injective, `φ(∞) = ∞`), so `φ|ℂ` is entire; holomorphy at `∞` with value
`∞` gives `|φ(z)| → ∞`, so `φ|ℂ` is a polynomial (Liouville / pole at `∞`); an injective
polynomial has degree one (a polynomial of degree `≥ 2` has a critical point or a value taken
twice). (Ahlfors Ch. 4; Conway, *Functions of One Complex Variable*, Ch. V; UNVERIFIED locators.)
Size: medium (polynomial from a pole at `∞`). -/
def SphereInjAffine : Prop :=
  ∀ φ : OnePoint ℂ → OnePoint ℂ, IsHolSphere φ → Function.Injective φ →
    φ OnePoint.infty = OnePoint.infty →
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, φ (z : OnePoint ℂ) = ((a * z + b : ℂ) : OnePoint ℂ)

/-! ### Holomorphic into `P¹` implies continuous (proved) -/

theorem tendsto_ite_inv {G : ℂ → ℂ} {z0 : ℂ} (hG : ContinuousAt G z0) (h0 : G z0 = 0) :
    Tendsto (fun z => if G z = 0 then (OnePoint.infty : OnePoint ℂ)
      else (((G z)⁻¹ : ℂ) : OnePoint ℂ)) (𝓝 z0) (𝓝 OnePoint.infty) := by
  rw [OnePoint.nhds_infty_eq]
  intro s hs
  rw [Filter.mem_sup, Filter.mem_map, Filter.mem_pure] at hs
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨t, ⟨-, htc⟩, hts⟩ := hasBasis_coclosedCompact.mem_iff.mp hs1
  obtain ⟨R, hR⟩ := htc.isBounded.subset_closedBall 0
  set R' := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hev : ∀ᶠ z in 𝓝 z0, ‖G z‖ < R'⁻¹ := by
    have h' : Tendsto (fun x => ‖G x‖) (𝓝 z0) (𝓝 0) := by
      have h'' : Tendsto (fun x => ‖G x‖) (𝓝 z0) (𝓝 ‖G z0‖) := hG.norm
      rwa [h0, norm_zero] at h''
    exact h' (Iio_mem_nhds (inv_pos.mpr hR'pos))
  rw [Filter.mem_map]
  filter_upwards [hev] with z hz
  rw [Set.mem_preimage]
  by_cases hz0 : G z = 0
  · rw [if_pos hz0]; exact hs2
  · rw [if_neg hz0]
    apply hts
    intro ht
    have h1 := hR ht
    rw [Metric.mem_closedBall, dist_zero_right, norm_inv] at h1
    have h2 : R' < ‖G z‖⁻¹ := by
      rw [lt_inv_comm₀ hR'pos (norm_pos_iff.mpr hz0)]; exact hz
    have : R ≤ R' := le_max_left _ _
    linarith

theorem continuousAt_of_isHolP1At {h : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane}
    (hh : IsHolP1At h τ) : ContinuousAt h τ := by
  have hc : ContinuousAt (fun w : UpperHalfPlane => (w : ℂ)) τ :=
    UpperHalfPlane.continuous_coe.continuousAt
  rcases hh with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
  · have hF : ContinuousAt (fun z : ℂ => (G z : OnePoint ℂ)) (τ : ℂ) :=
      OnePoint.continuous_coe.continuousAt.comp hG.continuousAt
    refine (hF.comp hc).congr ?_
    filter_upwards [hc.eventually hev] with w hw
    exact (hw w.im_pos).symm
  · have hF : ContinuousAt (fun z : ℂ => if G z = 0 then (OnePoint.infty : OnePoint ℂ)
        else (((G z)⁻¹ : ℂ) : OnePoint ℂ)) (τ : ℂ) := by
      unfold ContinuousAt
      simp only [hG0, ite_true]
      exact tendsto_ite_inv hG.continuousAt hG0
    refine (hF.comp hc).congr ?_
    filter_upwards [hc.eventually hev] with w hw
    exact (hw w.im_pos).symm

/-! ### The reduction -/

/-- **`SphereFactorAffine` from `HolP1OpenMap`, `HolP1FactorHol`, `SphereInjAffine` (proved).** -/
theorem sphereFactorAffine_of (hA : HolP1OpenMap) (hB : HolP1FactorHol) (hC : SphereInjAffine) :
    SphereFactorAffine := by
  intro f h hf hh hsurj hfib ⟨τ0, hf0, hh0⟩
  have hcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun τ => continuousAt_of_isHolP1At (hh τ)
  have hnc : ∃ τ τ', f τ ≠ f τ' := by
    obtain ⟨τ, hτ⟩ := hsurj ((0 : ℂ) : OnePoint ℂ)
    exact ⟨τ, τ0, by rw [hτ, hf0]; exact OnePoint.coe_ne_infty 0⟩
  have hopen : IsOpenMap f := hA f hf hnc
  choose g hg using hsurj
  set φ : OnePoint ℂ → OnePoint ℂ := fun w => h (g w) with hφdef
  have hφ : ∀ τ, h τ = φ (f τ) := fun τ => (hfib _ _).mp (hg (f τ)).symm
  have hφc : Continuous φ := by
    rw [continuous_def]
    intro U hU
    have : φ ⁻¹' U = f '' (h ⁻¹' U) := by
      ext w
      constructor
      · intro hw
        exact ⟨g w, by simpa [hφdef] using hw, hg w⟩
      · rintro ⟨τ, hτ, rfl⟩
        show φ (f τ) ∈ U
        rw [← hφ]; exact hτ
    rw [this]
    exact hopen _ (hU.preimage hcont)
  have hinj : Function.Injective φ := by
    intro w w' hww
    have := (hfib (g w) (g w')).mpr hww
    rwa [hg, hg] at this
  have hinf : φ OnePoint.infty = OnePoint.infty := by
    have := (hφ τ0).symm
    rw [hf0] at this
    rw [this, hh0]
  have hsurj' : Function.Surjective f := fun w => ⟨g w, hg w⟩
  obtain ⟨a, b, ha, hab⟩ := hC φ (hB f h φ hf hh hsurj' hφc hφ) hinj hinf
  refine ⟨a, b, ha, fun τ => ?_⟩
  rw [hφ]
  generalize f τ = w
  induction w using OnePoint.rec with
  | infty => rw [hinf, OnePoint.map_infty]
  | coe z => rw [hab, OnePoint.map_some]

/-! ### `HolP1OpenMap` (proved) -/

theorem chartInf_injective : Function.Injective chartInf := by
  intro w w' h
  unfold chartInf at h
  by_cases hw : w = 0 <;> by_cases hw' : w' = 0
  · rw [hw, hw']
  · rw [if_pos hw, if_neg hw'] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rw [if_neg hw, if_pos hw'] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [if_neg hw, if_neg hw'] at h
    exact inv_injective (OnePoint.coe_injective h)

theorem nhds_le_map_chartInf : 𝓝 (OnePoint.infty : OnePoint ℂ) ≤ map chartInf (𝓝 0) := by
  intro s hs
  rw [Filter.mem_map] at hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  rw [OnePoint.nhds_infty_eq, Filter.mem_sup, Filter.mem_map, Filter.mem_pure]
  have h0 : chartInf 0 ∈ s := hball (Metric.mem_ball_self hε)
  have hc0 : chartInf 0 = OnePoint.infty := by simp [chartInf]
  rw [hc0] at h0
  refine ⟨?_, h0⟩
  rw [hasBasis_coclosedCompact.mem_iff]
  refine ⟨Metric.closedBall 0 ε⁻¹, ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 _⟩, ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith [inv_pos.mpr hε]
  have hmem : z⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    exact inv_lt_of_inv_lt₀ hε hz
  have := hball hmem
  rw [Set.mem_preimage, chartInf, if_neg (inv_ne_zero hz0), inv_inv] at this
  exact this

/-- The chart of a holomorphic `P¹`-valued map at a point. -/
theorem chart_of_isHolP1At {g : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane}
    (hg : IsHolP1At g τ) :
    ∃ (F : ℂ → OnePoint ℂ) (G : ℂ → ℂ), Function.Injective F ∧
      𝓝 (F (G τ)) ≤ map F (𝓝 (G τ)) ∧
      ∃ r > 0, (∀ z ∈ Metric.ball (τ : ℂ) r, 0 < z.im) ∧
        AnalyticOnNhd ℂ G (Metric.ball (τ : ℂ) r) ∧
        ∀ z (hz : 0 < z.im), z ∈ Metric.ball (τ : ℂ) r → g ⟨z, hz⟩ = F (G z) := by
  have him : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  rcases hg with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
  · obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hev.and hG.eventually_analyticAt).and him)
    exact ⟨(↑), G, OnePoint.coe_injective, (OnePoint.isOpenEmbedding_coe.map_nhds_eq _).ge,
      r, hr, fun z hz => (hb z hz).2, fun z hz => (hb z hz).1.2,
      fun z hz hzb => (hb z hzb).1.1 hz⟩
  · obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hev.and hG.eventually_analyticAt).and him)
    refine ⟨chartInf, G, chartInf_injective, ?_, r, hr, fun z hz => (hb z hz).2,
      fun z hz => (hb z hz).1.2, fun z hz hzb => (hb z hzb).1.1 hz⟩
    rw [hG0]
    have : chartInf 0 = OnePoint.infty := by simp [chartInf]
    rw [this]
    exact nhds_le_map_chartInf

theorem eventually_coe_iff {τ : UpperHalfPlane} {P : UpperHalfPlane → Prop} :
    (∀ᶠ σ in 𝓝 τ, P σ) ↔ ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩ := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.eventually_map]
  constructor
  · intro h
    filter_upwards [h] with σ hσ
    intro hz
    exact hσ
  · intro h
    filter_upwards [h] with σ hσ
    exact hσ σ.im_pos

/-- **`HolP1OpenMap` (proved).** -/
theorem holP1OpenMap_proof : HolP1OpenMap := by
  intro g hg hnc
  choose F G hFi hFn r hr hpos hGan hgFG using fun τ => chart_of_isHolP1At (hg τ)
  have hgτ : ∀ τ : UpperHalfPlane, g τ = F τ (G τ τ) := fun τ =>
    hgFG τ τ τ.im_pos (Metric.mem_ball_self (hr τ))
  -- `g = F τ ∘ G τ` near `τ`, as a filter statement on `ℍ`
  have hloc : ∀ τ : UpperHalfPlane, ∀ᶠ σ in 𝓝 τ, g σ = F τ (G τ σ) := by
    intro τ
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with z hz hzi
    exact hgFG τ z hzi hz
  set S : Set UpperHalfPlane := {τ | ∀ᶠ σ in 𝓝 τ, g σ = g τ} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    obtain ⟨U, hU, hUo, hτU⟩ := eventually_nhds_iff.mp hτ
    filter_upwards [hUo.mem_nhds hτU] with σ hσ
    show ∀ᶠ σ' in 𝓝 σ, g σ' = g σ
    filter_upwards [hUo.mem_nhds hσ] with σ' hσ'
    rw [hU σ' hσ', hU σ hσ]
  -- if `g` is locally constant at some point of a chart ball, it is constant on the ball
  have hball_const : ∀ τ : UpperHalfPlane, ∀ σ : UpperHalfPlane,
      (σ : ℂ) ∈ Metric.ball (τ : ℂ) (r τ) → σ ∈ S →
      Set.EqOn (G τ) (fun _ => G τ σ) (Metric.ball (τ : ℂ) (r τ)) := by
    intro τ σ hσB hσS
    apply (hGan τ).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball _ _).isPreconnected hσB
    have h1 := eventually_coe_iff.mp hσS
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds hσB] with z hz hzB
    apply hFi τ
    rw [← hgFG τ z (hpos τ z hzB) hzB, hz (hpos τ z hzB), hgFG τ σ σ.im_pos hσB]
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro τ hτ
    show ∀ᶠ σ in 𝓝 τ, σ ∉ S
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with z hzB hzi hzS
    apply hτ
    have hc := hball_const τ ⟨z, hzi⟩ hzB hzS
    show ∀ᶠ σ in 𝓝 τ, g σ = g τ
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with w hwB hwi
    rw [hgFG τ w hwi hwB, hgτ τ, hc hwB, hc (Metric.mem_ball_self (hr τ))]
  have hSempty : S = ∅ := by
    rcases isClopen_iff.mp ⟨hSclosed, hSopen⟩ with h | h
    · exact h
    · exfalso
      obtain ⟨τ0, τ1, hne⟩ := hnc
      set T : Set UpperHalfPlane := {σ | g σ = g τ0} with hT
      have hTo : IsOpen T := by
        rw [isOpen_iff_mem_nhds]
        intro σ hσ
        have : σ ∈ S := h ▸ Set.mem_univ σ
        filter_upwards [this] with σ' hσ'
        show g σ' = g τ0
        rw [hσ']; exact hσ
      have hTc : IsClosed T := by
        rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
        intro σ hσ
        have : σ ∈ S := h ▸ Set.mem_univ σ
        filter_upwards [this] with σ' hσ'
        show ¬ g σ' = g τ0
        rw [hσ']; exact hσ
      rcases isClopen_iff.mp ⟨hTc, hTo⟩ with hT0 | hT1
      · have : τ0 ∈ T := rfl
        rw [hT0] at this; exact this
      · have : τ1 ∈ T := hT1 ▸ Set.mem_univ τ1
        exact hne this.symm
  -- open mapping at every point
  rw [isOpenMap_iff_nhds_le]
  intro τ
  have hnot : ¬ ∀ᶠ z in 𝓝 (τ : ℂ), G τ z = G τ τ := by
    intro hc
    have : τ ∈ S := by
      show ∀ᶠ σ in 𝓝 τ, g σ = g τ
      rw [eventually_coe_iff]
      filter_upwards [hc, Metric.ball_mem_nhds _ (hr τ)] with z hz hzB hzi
      rw [hgFG τ z hzi hzB, hgτ τ, hz]
    rw [hSempty] at this; exact this
  have hopen := ((hGan τ) τ (Metric.mem_ball_self (hr τ))).eventually_constant_or_nhds_le_map_nhds
  rcases hopen with h | h
  · exact absurd h hnot
  · calc 𝓝 (g τ) = 𝓝 (F τ (G τ τ)) := by rw [hgτ]
      _ ≤ map (F τ) (𝓝 (G τ τ)) := hFn τ
      _ ≤ map (F τ) (map (G τ) (𝓝 (τ : ℂ))) := Filter.map_mono h
      _ = map (fun σ : UpperHalfPlane => F τ (G τ σ)) (𝓝 τ) := by
          rw [Filter.map_map, ← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.map_map]
          rfl
      _ = map g (𝓝 τ) := Filter.map_congr (by
          filter_upwards [hloc τ] with σ hσ
          exact hσ.symm)

/-- **`SphereFactorAffine` from `HolP1FactorHol` and `SphereInjAffine` (proved).** -/
theorem sphereFactorAffine_of' (hB : HolP1FactorHol) (hC : SphereInjAffine) :
    SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof hB hC

/-! ### `SphereInjAffine` (proved)

`f = φ|ℂ` is entire and injective. Pick `z₁` with `f'(z₁) ≠ 0`; then `q = dslope f z₁` is entire
and never `0`, so `r = 1/q`, `r(z) = (z − z₁)/(f(z) − f(z₁))`, is entire. Near `∞`,
`f(z) = 1/G(1/z)` with `G(0) = 0`, so `r(z) → G'(0)`. By Liouville `r` is constant, and
`f(z) = f(z₁) + (z − z₁)/G'(0)`. -/

/-- **`SphereInjAffine` (proved).** -/
theorem sphereInjAffine_proof : SphereInjAffine := by
  intro φ ⟨hfin_hol, hinf_hol⟩ hinj hinf
  -- `φ` is finite on `ℂ`
  have hfin : ∀ z : ℂ, ∃ v : ℂ, φ (z : OnePoint ℂ) = (v : OnePoint ℂ) := by
    intro z
    have hne : φ (z : OnePoint ℂ) ≠ OnePoint.infty := by
      rw [← hinf]; intro h; exact OnePoint.coe_ne_infty z (hinj h)
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hne
    exact ⟨v, hv.symm⟩
  choose f hf using hfin
  have hfinj : Function.Injective f := by
    intro z z' h
    have : φ (z : OnePoint ℂ) = φ (z' : OnePoint ℂ) := by rw [hf, hf, h]
    exact OnePoint.coe_injective (hinj this)
  -- `f` is entire
  have hdiff : Differentiable ℂ f := by
    intro z
    rcases hfin_hol z with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
    · have : f =ᶠ[𝓝 z] G := by
        filter_upwards [hev] with w hw
        rw [hf] at hw
        exact OnePoint.coe_injective hw
      exact hG.differentiableAt.congr_of_eventuallyEq this
    · exfalso
      have h0 := hev.self_of_nhds
      simp only [hG0, ite_true] at h0
      rw [hf] at h0
      exact OnePoint.coe_ne_infty _ h0
  -- the chart at `∞`
  obtain ⟨G, hG, hG0, hev⟩ : ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), φ (chartInf w) =
        if G w = 0 then OnePoint.infty else (((G w)⁻¹ : ℂ) : OnePoint ℂ) := by
    rcases hinf_hol with ⟨G, hG, hev⟩ | h
    · exfalso
      have h0 : φ (chartInf 0) = ((G 0 : ℂ) : OnePoint ℂ) := hev.self_of_nhds
      have hc0 : chartInf 0 = OnePoint.infty := by simp [chartInf]
      rw [hc0, hinf] at h0
      exact OnePoint.coe_ne_infty _ h0.symm
    · exact h
  -- a point with `f' ≠ 0`
  obtain ⟨z1, hz1⟩ : ∃ z1, deriv f z1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have := is_const_of_deriv_eq_zero hdiff hcon 0 1
    exact zero_ne_one (hfinj this)
  set q := dslope f z1 with hqdef
  have hq : Differentiable ℂ q := by
    have := (Complex.differentiableOn_dslope (c := z1) (s := Set.univ) Filter.univ_mem).mpr
      hdiff.differentiableOn
    exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  have hq0 : ∀ z, q z ≠ 0 := by
    intro z
    by_cases hz : z = z1
    · rw [hz, hqdef, dslope_same]; exact hz1
    · rw [hqdef, dslope_of_ne _ hz, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr (fun h => hz (hfinj h))) (sub_ne_zero.mpr hz)
  set L := deriv G 0 with hL
  -- `1/q → G'(0)` at `∞`
  set rt : ℂ → ℂ := fun w => (1 - z1 * w) * dslope G 0 w / (1 - f z1 * G w) with hrt
  have hrt_cont : ContinuousAt rt 0 := by
    have h1 : ContinuousAt (dslope G 0) 0 :=
      continuousAt_dslope_same.mpr hG.differentiableAt
    have h2 : ContinuousAt G 0 := hG.continuousAt
    apply ContinuousAt.div ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul h1)
      (continuousAt_const.sub (continuousAt_const.mul h2))
    simp [hG0]
  have hrt0 : rt 0 = L := by simp [hrt, hG0, dslope_same, hL]
  have hev' : ∀ᶠ z in Bornology.cobounded ℂ, (q z)⁻¹ = rt z⁻¹ := by
    have h1 := (Filter.tendsto_inv₀_cobounded (α := ℂ)).eventually hev
    filter_upwards [h1, Bornology.eventually_ne_cobounded z1, Bornology.eventually_ne_cobounded 0]
      with z hz hzz1 hz0
    have hw0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
    have hcz : chartInf z⁻¹ = (z : OnePoint ℂ) := by simp [chartInf, hz0]
    rw [hcz, hf] at hz
    have hGw : G z⁻¹ ≠ 0 := by
      intro h; rw [if_pos h] at hz; exact OnePoint.coe_ne_infty _ hz
    rw [if_neg hGw] at hz
    have hfz : f z = (G z⁻¹)⁻¹ := OnePoint.coe_injective hz
    have hne : f z - f z1 ≠ 0 := sub_ne_zero.mpr (fun h => hzz1 (hfinj h))
    have hne' : 1 - f z1 * G z⁻¹ ≠ 0 := by
      intro h
      have h2 : f z1 = (G z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -h)
      exact hne (by rw [hfz, h2, sub_self])
    have hA : (G z⁻¹)⁻¹ - f z1 ≠ 0 := by rw [← hfz]; exact hne
    have hzz : z - z1 ≠ 0 := sub_ne_zero.mpr hzz1
    rw [hqdef, dslope_of_ne _ hzz1, slope_def_field, hrt]
    simp only
    rw [dslope_of_ne _ hw0, slope_def_field, hG0, sub_zero, sub_zero, hfz]
    rw [inv_div]
    have e1 : (G z⁻¹)⁻¹ - f z1 = (1 - f z1 * G z⁻¹) / G z⁻¹ := by
      rw [eq_div_iff hGw, sub_mul, inv_mul_cancel₀ hGw]
    have e2 : (1 - z1 * z⁻¹) * (G z⁻¹ / z⁻¹) = (z - z1) * G z⁻¹ := by
      rw [div_inv_eq_mul]
      linear_combination (-(z1 * G z⁻¹)) * (inv_mul_cancel₀ hz0)
    rw [e1, e2, div_div_eq_mul_div]
  have htend : Filter.Tendsto (fun z => (q z)⁻¹) (Filter.cocompact ℂ) (𝓝 L) := by
    rw [← Metric.cobounded_eq_cocompact]
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev') ?_
    rw [← hrt0]
    exact (hrt_cont.tendsto.mono_left nhdsWithin_le_nhds).comp
      (Filter.tendsto_inv₀_cobounded' (α := ℂ))
  have hconst : ∀ z, (q z)⁻¹ = L := fun z =>
    (hq.inv hq0).apply_eq_of_tendsto_cocompact z htend
  have hL0 : L ≠ 0 := by
    rw [← hconst 0]; exact inv_ne_zero (hq0 0)
  refine ⟨L⁻¹, f z1 - z1 * L⁻¹, inv_ne_zero hL0, fun z => ?_⟩
  rw [hf]
  congr 1
  by_cases hz : z = z1
  · rw [hz]; ring
  · have h1 := hconst z
    rw [hqdef, dslope_of_ne _ hz, slope_def_field, inv_div] at h1
    have hzz : z - z1 ≠ 0 := sub_ne_zero.mpr hz
    have hfne : f z - f z1 ≠ 0 := sub_ne_zero.mpr (fun h => hz (hfinj h))
    field_simp at h1 ⊢
    linear_combination -h1

/-! ### `HolP1FactorHol` (proved) -/

/-- **Removable singularity through a branched cover.** If `Ψ ∘ A = H` near `t₀` with `A, H`
analytic, `A` not locally constant and `Ψ` continuous at `A t₀`, then `Ψ` is analytic at `A t₀`:
off the (isolated) critical points `A` has an analytic local inverse, so `Ψ` is holomorphic on a
punctured neighbourhood of `A t₀` (open mapping), and continuity removes the singularity. -/
theorem core_removable {A H Ψ : ℂ → ℂ} {t0 : ℂ} (hA : AnalyticAt ℂ A t0) (hH : AnalyticAt ℂ H t0)
    (hnc : ¬ ∀ᶠ t in 𝓝 t0, A t = A t0) (hΨ : ContinuousAt Ψ (A t0))
    (hrel : ∀ᶠ t in 𝓝 t0, Ψ (A t) = H t) : AnalyticAt ℂ Ψ (A t0) := by
  -- critical points of `A` are isolated
  have hd : ∀ᶠ t in 𝓝[≠] t0, deriv A t ≠ 0 := by
    rcases hA.deriv.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hnc
      obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (h.and hA.eventually_analyticAt)
      filter_upwards [Metric.ball_mem_nhds t0 hr] with t ht
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t0 r).isPreconnected
        (fun y hy => (hb y hy).2.differentiableAt.differentiableWithinAt)
        (fun y hy => (hb y hy).1) ht (Metric.mem_ball_self hr)
    · exact h
  have hopen : 𝓝 (A t0) ≤ map A (𝓝 t0) :=
    (hA.eventually_constant_or_nhds_le_map_nhds).resolve_left hnc
  -- the good set
  have hgood : ∀ᶠ t in 𝓝 t0, t ≠ t0 → AnalyticAt ℂ Ψ (A t) := by
    have h1 := eventually_nhdsWithin_iff.mp hd
    filter_upwards [h1, hrel.eventually_nhds, hH.eventually_analyticAt,
      hA.eventually_analyticAt] with t ht hrt hHt hAt hne
    have hcomp : AnalyticAt ℂ (Ψ ∘ A) t := hHt.congr (by
      filter_upwards [hrt] with t' ht'; exact ht'.symm)
    exact (analyticAt_comp_iff_of_deriv_ne_zero hAt (ht hne)).mp hcomp
  obtain ⟨V, hV, hVgood⟩ := hgood.exists_mem
  have hAV : A '' V ∈ 𝓝 (A t0) :=
    hopen (Filter.mem_map.mpr (Filter.mem_of_superset hV (Set.subset_preimage_image A V)))
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hΨ
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hAV] with s hs hs0
  obtain ⟨t, htV, rfl⟩ := hs
  have hne : t ≠ t0 := fun h => hs0 (by rw [h]; rfl)
  exact (hVgood t htV hne).differentiableAt

/-- `ℂ`-coordinate of a point of `P¹` (junk `0` at `∞`). -/
def toC (x : OnePoint ℂ) : ℂ := x.elim 0 id
/-- The coordinate of the chart at `∞` (`∞ ↦ 0`, `z ↦ 1/z`). -/
def invC (x : OnePoint ℂ) : ℂ := x.elim 0 (fun z => z⁻¹)

theorem toC_coe (z : ℂ) : toC (z : OnePoint ℂ) = z := rfl
theorem invC_coe (z : ℂ) : invC (z : OnePoint ℂ) = z⁻¹ := rfl
theorem invC_infty : invC OnePoint.infty = 0 := rfl

theorem continuousAt_toC (z : ℂ) : ContinuousAt toC (z : OnePoint ℂ) := by
  rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
  exact continuousAt_id

theorem continuousAt_invC_infty : ContinuousAt invC OnePoint.infty := by
  unfold ContinuousAt
  rw [invC_infty, OnePoint.nhds_infty_eq, Filter.tendsto_sup]
  constructor
  · rw [Filter.tendsto_map'_iff]
    have : invC ∘ ((↑) : ℂ → OnePoint ℂ) = fun z => z⁻¹ := rfl
    rw [this, Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  · rw [Filter.tendsto_pure_left]
    intro s hs
    rw [invC_infty]; exact mem_of_mem_nhds hs

theorem chartInf_invC {x : OnePoint ℂ} (hx : x ≠ ((0 : ℂ) : OnePoint ℂ)) : chartInf (invC x) = x := by
  induction x using OnePoint.rec with
  | infty => simp [chartInf, invC_infty]
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    rw [invC_coe, chartInf, if_neg (inv_ne_zero hz), inv_inv]

theorem invC_chartInf (w : ℂ) : invC (chartInf w) = w := by
  by_cases hw : w = 0
  · rw [hw]; simp [chartInf, invC_infty]
  · rw [chartInf, if_neg hw, invC_coe, inv_inv]

theorem continuous_chartInf : Continuous chartInf := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · rw [hw]
    unfold ContinuousAt
    have : chartInf 0 = OnePoint.infty := by simp [chartInf]
    rw [this]
    exact tendsto_ite_inv continuousAt_id rfl
  · have hev : chartInf =ᶠ[𝓝 w] (fun w' => ((w'⁻¹ : ℂ) : OnePoint ℂ)) := by
      filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
      rw [chartInf, if_neg hw']
    exact (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)).congr hev.symm

theorem not_isOpen_singleton_P1 (x : OnePoint ℂ) : ¬ IsOpen ({x} : Set (OnePoint ℂ)) := by
  induction x using OnePoint.rec with
  | infty =>
    intro h
    rw [OnePoint.isOpen_iff_of_mem (Set.mem_singleton _)] at h
    obtain ⟨-, h2⟩ := h
    have : (OnePoint.some ⁻¹' ({OnePoint.infty} : Set (OnePoint ℂ)))ᶜ = (Set.univ : Set ℂ) := by
      ext z; simp
    rw [this] at h2
    exact noncompact_univ ℂ h2
  | coe z =>
    intro h
    have h2 : IsOpen (((↑) : ℂ → OnePoint ℂ) ⁻¹' {(z : OnePoint ℂ)}) :=
      h.preimage OnePoint.continuous_coe
    have : ((↑) : ℂ → OnePoint ℂ) ⁻¹' {(z : OnePoint ℂ)} = {z} := by
      ext w; simp
    rw [this] at h2
    exact not_isOpen_singleton z h2

/-- **`HolP1FactorHol` (proved).** -/
theorem holP1FactorHol_proof : HolP1FactorHol := by
  intro f h φ hf hh hsurj hφc hfac
  have hnc : ∃ τ τ', f τ ≠ f τ' := by
    obtain ⟨τ, hτ⟩ := hsurj ((0 : ℂ) : OnePoint ℂ)
    obtain ⟨τ', hτ'⟩ := hsurj OnePoint.infty
    exact ⟨τ, τ', by rw [hτ, hτ']; exact OnePoint.coe_ne_infty 0⟩
  have hopen : IsOpenMap f := holP1OpenMap_proof f hf hnc
  -- `f` is not locally constant anywhere
  have hfnc : ∀ τ0 : UpperHalfPlane, ¬ ∀ᶠ τ in 𝓝 τ0, f τ = f τ0 := by
    intro τ0 hc
    obtain ⟨U, hU, hUo, hτU⟩ := eventually_nhds_iff.mp hc
    have himg : f '' U = {f τ0} := by
      ext x; constructor
      · rintro ⟨τ, hτ, rfl⟩; exact hU τ hτ
      · intro hx; rw [Set.mem_singleton_iff] at hx; exact ⟨τ0, hτU, hx.symm⟩
    exact not_isOpen_singleton_P1 _ (himg ▸ hopen U hUo)
  -- the key step, in a source chart `f = C ∘ A`
  have key : ∀ (τ0 : UpperHalfPlane) (C : ℂ → OnePoint ℂ) (A : ℂ → ℂ),
      ContinuousAt C (A τ0) → AnalyticAt ℂ A τ0 →
      (∀ᶠ z in 𝓝 (τ0 : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = C (A z)) →
      IsHolC1At (fun w => φ (C w)) (A τ0) := by
    intro τ0 C A hC hA hfA
    have hAnc : ¬ ∀ᶠ t in 𝓝 (τ0 : ℂ), A t = A τ0 := by
      intro hc
      apply hfnc τ0
      rw [eventually_coe_iff]
      filter_upwards [hc, hfA] with z hz hfz hzi
      rw [hfz hzi, hz]
      have := (hfA.self_of_nhds) τ0.im_pos
      exact this.symm
    have hΦ : ContinuousAt (fun w => φ (C w)) (A τ0) := hφc.continuousAt.comp hC
    have hhA : ∀ᶠ z in 𝓝 (τ0 : ℂ), ∀ hz : 0 < z.im, h ⟨z, hz⟩ = φ (C (A z)) := by
      filter_upwards [hfA] with z hz hzi
      rw [hfac, hz hzi]
    have hh0 : h τ0 = φ (C (A τ0)) := (hhA.self_of_nhds) τ0.im_pos
    have him : ∀ᶠ z in 𝓝 (τ0 : ℂ), 0 < z.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ0.im_pos
    rcases hh τ0 with ⟨H, hH, hevH⟩ | ⟨H, hH, hH0, hevH⟩
    · -- finite value
      have hval : φ (C (A τ0)) = ((H τ0 : ℂ) : OnePoint ℂ) := by
        rw [← hh0]; exact (hevH.self_of_nhds) τ0.im_pos
      left
      refine ⟨fun w => toC (φ (C w)), ?_, ?_⟩
      · apply core_removable hA hH hAnc
        · show ContinuousAt (toC ∘ fun w => φ (C w)) (A τ0)
          apply ContinuousAt.comp _ hΦ
          rw [hval]; exact continuousAt_toC _
        · filter_upwards [hhA, hevH, him] with z hz hHz hzi
          show toC (φ (C (A z))) = H z
          rw [← hz hzi, hHz hzi, toC_coe]
      · have hfin : ∀ᶠ w in 𝓝 (A τ0), φ (C w) ∈ Set.range ((↑) : ℂ → OnePoint ℂ) :=
          hΦ (OnePoint.isOpen_range_coe.mem_nhds (by
            show φ (C (A (τ0 : ℂ))) ∈ _
            rw [hval]; exact ⟨_, rfl⟩))
        filter_upwards [hfin] with w hw
        obtain ⟨v, hv⟩ := hw
        rw [← hv, toC_coe]
    · -- the value `∞`
      have hval : φ (C (A τ0)) = OnePoint.infty := by
        rw [← hh0]
        have := (hevH.self_of_nhds) τ0.im_pos
        rw [this, if_pos hH0]
      right
      refine ⟨fun w => invC (φ (C w)), ?_, ?_, ?_⟩
      · apply core_removable hA hH hAnc
        · show ContinuousAt (invC ∘ fun w => φ (C w)) (A τ0)
          apply ContinuousAt.comp _ hΦ
          rw [hval]; exact continuousAt_invC_infty
        · filter_upwards [hhA, hevH, him] with z hz hHz hzi
          show invC (φ (C (A z))) = H z
          rw [← hz hzi, hHz hzi]
          exact invC_chartInf (H z)
      · show invC (φ (C (A τ0))) = 0
        rw [hval, invC_infty]
      · have hne0 : ∀ᶠ w in 𝓝 (A τ0), φ (C w) ≠ ((0 : ℂ) : OnePoint ℂ) :=
          hΦ (isOpen_ne.mem_nhds (by
            show φ (C (A (τ0 : ℂ))) ≠ _
            rw [hval]; exact (OnePoint.coe_ne_infty 0).symm))
        filter_upwards [hne0] with w hw
        exact (chartInf_invC hw).symm
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨τ0, hτ0⟩ := hsurj (z : OnePoint ℂ)
    rcases hf τ0 with ⟨G, hG, hevG⟩ | ⟨G, hG, hG0, hevG⟩
    · have hGz : G τ0 = z := by
        have := (hevG.self_of_nhds) τ0.im_pos
        rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0] at this
        exact (OnePoint.coe_injective this).symm
      have := key τ0 (↑) G OnePoint.continuous_coe.continuousAt hG hevG
      rwa [hGz] at this
    · exfalso
      have := (hevG.self_of_nhds) τ0.im_pos
      rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0, if_pos hG0] at this
      exact OnePoint.coe_ne_infty z this
  · obtain ⟨τ0, hτ0⟩ := hsurj OnePoint.infty
    rcases hf τ0 with ⟨G, hG, hevG⟩ | ⟨G, hG, hG0, hevG⟩
    · exfalso
      have := (hevG.self_of_nhds) τ0.im_pos
      rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0] at this
      exact OnePoint.coe_ne_infty _ this.symm
    · have := key τ0 chartInf G continuous_chartInf.continuousAt hG hevG
      rwa [hG0] at this

/-- **`SphereFactorAffine` (proved, from Mathlib alone).** -/
theorem sphereFactorAffine_proof : SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof holP1FactorHol_proof sphereInjAffine_proof

/-- **`SphereFactorAffine` from `HolP1FactorHol` alone (proved).** -/
theorem sphereFactorAffine_of'' (hB : HolP1FactorHol) : SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof hB sphereInjAffine_proof

end HSyn.G0Split.FibreQM.PeriodGlue



/-! ## leaf-fold4: scratch/period-glue/final_part.lean (declarations already in the chain dropped) -/


/-! ## End to end: fibre-qm-period's `FibreQMPeriod` with period-glue's pieces (proved) -/

namespace HSyn.G0Split.FibreQM.PeriodGlue
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **`FibreQMPeriod` from leaves and the remaining glue (proved).** period-map's
`fibreQMPeriod_periodMap` with `BaseChangeClassUnique`, `S8Nonzero` proved, `T11aRiemannEnd`
derived from `T11aRiemannHom`, `SphereFactorAffine` proved, and `PiTwistC`, `QMTwistLattice`,
`S8WeightExact` replaced by their pieces.
* Leaves: `R1R2fp`, `PkgI1.QMHauptmodul`, T35 (`UniformizationExistsT35`), `T11aRiemannHom`,
  `QMClassNumberOne`, `R1bFamily`, `CMDescends` (candidate), `PkgI1.ThetaModularity`,
  `ObjBridge.TorsionStructure` (T5, Mumford §4),
  `GammaStarGen` (candidate), `ValenceBoundGammaStar` (candidate), and
  `GlueDescent.LeafSkolemNoether` (proved in the kernel: `TSkolemKW.leafSkolemNoether`).
* Glue: `Pin.MobiusGlue` and `AutOInnerFinite` (both proved by mobius-glue), and the inherited
  `CPtsTransport`. -/
theorem fibreQMPeriod_periodGlue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hHom : T11aRiemannHom)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hTors : ObjBridge.TorsionStructure) (hAI : AutOInnerFinite)
    (hSN : GlueDescent.LeafSkolemNoether) (hD : CMDescends)
    (hTM : PkgI1.ThetaModularity) (hG : GammaStarGen)
    (hV : PeriodMap.ValenceBoundGammaStar) (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_periodMap h hM hH hE (t11aRiemannEnd_of_hom hHom) hCN hR
    baseChangeClassUnique_proof
    (piTwistC_of _ _ _ (own_spec h).1 (own_spec h).2.2
      (twistOrbitFinite_of' _ _ (own_spec h).2.1 hTors hAI) (fibreTransferC_proof _ _))
    (qmTwistLattice_of' hHom hSN) hD s8Nonzero_proof
    sphereFactorAffine_proof (s8WeightExact_of hTM hG) hV hCP

end HSyn.G0Split.FibreQM.PeriodGlue



end
end
end
end
end
end
end G0A2_c90_periodglue

end HDec
