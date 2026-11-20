import ZInQKernel.Contrib.OneProof.H.TailZ2

/-! # The valence formula for a cocompact Fuchsian group (task gt-valence)

`ValenceCocompact.valenceFormulaCocompactEq_proof : HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`,
with no hypotheses and only the standard axioms. This proves the published leaf `valenceFormulaCocompactEq`
(Shimura 1971, Prop. 2.16 and Thm. 2.20; Rankin 1977, Thm. 4.1.4) of the single proof in the generality in
which it is stated (every cocompact Fuchsian group, every fundamental domain, every weight `2m`, norm
automorphy). Report: `docs/research/gt-valence.md`.

The proof avoids fundamental polygons and boundary integrals entirely:
* **Partition of unity** (Part B2). From cocompactness, a smooth compactly supported `χ ≥ 0` on `ℍ` with
  `∑_{g ∈ Γ̄} χ(g z) = 1` for every `z` (`Γ̄` = the group of Möbius maps of `Γ`, a subgroup of `Perm ℍ`;
  local finiteness from proper discontinuity).
* **Riesz identity** (Parts A1-A5). `∫_ℂ log|F| Δχ = 2π Σ_ρ ord_ρ(F) χ(ρ)`: Green's identity for test
  functions (Mathlib's integration by parts), the fundamental solution `∫ log|x−u| Δχ = 2π χ(u)` (regularize
  by `½ log(|x−u|² + ε²)`, dominated convergence, `∫_ℂ 2/(1+|z|²)² = 2π`), and Mathlib's
  `MeromorphicOn.extract_zeros_poles_log` with harmonicity of `log|g|`.
* **Cancellation** (Parts A6, B4). `Φ = log(|F| y^m)` is exactly `Γ`-invariant; `y²Δ` commutes with Möbius
  maps (`Δ(χ∘φ) = |φ'|² (Δχ)∘φ` for holomorphic `φ`); unfolding with the finite partition sums and Mathlib's
  `GL(2,ℝ)`-invariant measure `dx dy/y²` on `ℍ` gives `∫ Φ Δχ = 0`.
* **Assembly** (Parts B3, B5-B8). `Δ log y = −1/y²`, `∫_ℍ χ dμ = vol(s)` (Mathlib's
  `IsFundamentalDomain.lintegral_eq_tsum'`), so `2π Σ_ρ ord_ρ χ(ρ) = m vol(s)`; orbit-stabilizer counting
  (`Σ_{ρ ∈ Γz} χ(ρ) = 1/e_z`, orders constant on orbits) turns the left side into `Σ_{z ∈ T} ord_z/e_z`.
-/

set_option linter.all false

noncomputable section

/-! ### Part A1 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian

namespace ValenceCocompact

/-- Second directional derivative. -/
noncomputable def d2 (f : ℂ → ℝ) (v x : ℂ) : ℝ := fderiv ℝ (fun y => fderiv ℝ f y v) x v

theorem d2_eq_iter {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    iteratedFDeriv ℝ 2 f x ![v, v] = d2 f v x := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [d2, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem laplacian_eq_d2 {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = d2 f 1 x + d2 f I x := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [d2_eq_iter hf, d2_eq_iter hf]

theorem integrable_of_tsupport {h : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hh : ContinuousOn h V)
    (hs : tsupport h ⊆ V) (hc : HasCompactSupport h) : Integrable h :=
  (hh.continuous_of_tsupport_subset hV hs).integrable_of_hasCompactSupport hc

/-- Product of a function continuous on `V` with a continuous function compactly supported in `V`. -/
theorem integrable_mul_of {f g : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContinuousOn f V)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgV : tsupport g ⊆ V) :
    Integrable (fun x => f x * g x) := by
  refine integrable_of_tsupport hV (hf.mul hg.continuousOn) ?_ (hgc.mul_left)
  exact (tsupport_mul_subset_right).trans hgV

/-- One-direction double integration by parts. -/
theorem integral_mul_d2 {f χ : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) (v : ℂ) :
    ∫ x, f x * d2 χ v x = ∫ x, d2 f v x * χ x := by
  set g : ℂ → ℝ := fun y => fderiv ℝ χ y v with hg
  have hg1 : ContDiff ℝ 1 g := (hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgc : HasCompactSupport g := hχc.fderiv_apply (𝕜 := ℝ) v
  have hgV : tsupport g ⊆ V := (tsupport_fderiv_apply_subset ℝ v).trans hχV
  have hf1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) V :=
    (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hfd : ∀ x ∈ V, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)
  have hf1d : ∀ x ∈ V, DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := fun x hx =>
    (hf1.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgc' : HasCompactSupport (fun x => fderiv ℝ g x v) := hgc.fderiv_apply (𝕜 := ℝ) v
  have hgV' : tsupport (fun x => fderiv ℝ g x v) ⊆ V := (tsupport_fderiv_apply_subset ℝ v).trans hgV
  -- step 1
  have e1 : ∫ x, f x * fderiv ℝ g x v = - ∫ x, fderiv ℝ f x v * g x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of hV hf1.continuousOn hg1.continuous hgc hgV
    · exact integrable_mul_of hV hf.continuousOn hgd' hgc' hgV'
    · exact integrable_mul_of hV hf.continuousOn hg1.continuous hgc hgV
    · exact fun x hx => hfd x (hgV hx)
    · exact fun x _ => (hg1.differentiable (by norm_num)) x
  -- step 2
  have e2 : ∫ x, fderiv ℝ f x v * fderiv ℝ χ x v =
      - ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * χ x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x v) V :=
        ((hf1.continuousOn_fderiv_of_isOpen hV (by norm_num))).clm_apply continuousOn_const
      exact integrable_mul_of hV hcont hχ.continuous hχc hχV
    · exact integrable_mul_of hV hf1.continuousOn hg1.continuous hgc hgV
    · exact integrable_mul_of hV hf1.continuousOn hχ.continuous hχc hχV
    · exact fun x hx => hf1d x (hχV hx)
    · exact fun x _ => (hχ.differentiable (by norm_num)) x
  simp only [d2]
  rw [e1]
  change -∫ x, fderiv ℝ f x v * fderiv ℝ χ x v = _
  rw [e2, neg_neg]

/-- **Green's identity** for a test function: `∫ f Δχ = ∫ Δf χ` when `f` is `C²` on an open set containing the
support of `χ`. -/
theorem integral_mul_laplacian {f χ : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) :
    ∫ x, f x * Δ χ x = ∫ x, Δ f x * χ x := by
  have hd2 : ∀ v, Integrable (fun x => f x * d2 χ v x) := by
    intro v
    have hc : Continuous (d2 χ v) := by
      have := ((hχ.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiff_const (c := v)))
      exact (this.continuous_fderiv (by norm_num)).clm_apply continuous_const
    refine integrable_mul_of hV hf.continuousOn hc ?_ ?_
    · exact ((hχc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v)
    · exact (tsupport_fderiv_apply_subset ℝ v).trans ((tsupport_fderiv_apply_subset ℝ v).trans hχV)
  have hd2' : ∀ v, Integrable (fun x => d2 f v x * χ x) := by
    intro v
    have hf1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) V :=
      (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
    have hcont : ContinuousOn (d2 f v) V :=
      ((hf1.continuousOn_fderiv_of_isOpen hV (by norm_num))).clm_apply continuousOn_const
    exact integrable_mul_of hV hcont hχ.continuous hχc hχV
  have L1 : ∀ x, f x * Δ χ x = f x * d2 χ 1 x + f x * d2 χ I x := fun x => by
    rw [laplacian_eq_d2 (hχ.contDiffAt)]; ring
  have L2 : ∀ x, Δ f x * χ x = d2 f 1 x * χ x + d2 f I x * χ x ∨ χ x = 0 := by
    intro x
    by_cases hx : χ x = 0
    · exact Or.inr hx
    · left
      have hxV : x ∈ V := hχV (subset_tsupport _ hx)
      rw [laplacian_eq_d2 (hf.contDiffAt (hV.mem_nhds hxV))]; ring
  have L2' : (fun x => Δ f x * χ x) = fun x => d2 f 1 x * χ x + d2 f I x * χ x := by
    funext x
    rcases L2 x with h | h
    · exact h
    · simp [h]
  simp_rw [L1, L2']
  rw [integral_add (hd2 1) (hd2 I), integral_add (hd2' 1) (hd2' I),
    integral_mul_d2 hV hf hχ hχc hχV 1, integral_mul_d2 hV hf hχ hχc hχV I]

end ValenceCocompact

/-! ### Part A2 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian

namespace ValenceCocompact

/-- `d2` as a second derivative along the line `t ↦ x + t v`. -/
theorem d2_eq_line {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    d2 f v x = deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  set φ : ℂ → ℝ := fun y => fderiv ℝ f y v
  have hφ : DifferentiableAt ℝ φ x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hline : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using this.tendsto 0
  have hev' : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0 : ℝ)] fun t => φ (x + t • v) := by
    filter_upwards [hline.eventually hev] with t ht
    have hd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hd.comp_hasDerivAt t hl).deriv
  rw [hev'.deriv_eq]
  have hl0 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0:ℝ) • v) := by simpa using hφ.hasFDerivAt
  have := (hφ'.comp_hasDerivAt (0:ℝ) hl0).deriv
  simp only [Function.comp_def] at this
  rw [this]
  rfl

/-- The regularized logarithm `½ log(|w|² + ε²)`. -/
noncomputable def ureg (ε : ℝ) (w : ℂ) : ℝ := Real.log (‖w‖ ^ 2 + ε ^ 2) / 2

theorem ureg_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (ureg ε) := by
  unfold ureg
  apply ContDiff.div_const
  apply ContDiff.log ((contDiff_norm_sq ℝ).add contDiff_const)
  intro w; positivity

theorem norm_line_sq (x v : ℂ) (t : ℝ) :
    ‖x + t • v‖ ^ 2 = (x.re + t * v.re) ^ 2 + (x.im + t * v.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- Second derivative of `t ↦ ½ log(a(t)² + b(t)² + ε²)` for affine `a, b`. -/
theorem deriv2_ureg_line {ε : ℝ} (hε : 0 < ε) (x v : ℂ) :
    deriv (deriv (fun t : ℝ => ureg ε (x + t • v))) 0 =
      ((v.re ^ 2 + v.im ^ 2) * (‖x‖ ^ 2 + ε ^ 2) - 2 * (x.re * v.re + x.im * v.im) ^ 2) /
        (‖x‖ ^ 2 + ε ^ 2) ^ 2 := by
  set q : ℝ → ℝ := fun t => (x.re + t * v.re) ^ 2 + (x.im + t * v.im) ^ 2 + ε ^ 2 with hq
  have hqpos : ∀ t, 0 < q t := fun t => by simp only [hq]; positivity
  have hfun : (fun t : ℝ => ureg ε (x + t • v)) = fun t => Real.log (q t) / 2 := by
    funext t; simp only [ureg, norm_line_sq, hq]
  have hq' : ∀ t, HasDerivAt q (2 * (x.re + t * v.re) * v.re + 2 * (x.im + t * v.im) * v.im) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x.re + t * v.re) v.re t := by
      simpa using ((hasDerivAt_id t).mul_const v.re).const_add x.re
    have h2 : HasDerivAt (fun t : ℝ => x.im + t * v.im) v.im t := by
      simpa using ((hasDerivAt_id t).mul_const v.im).const_add x.im
    have := ((h1.pow 2).add (h2.pow 2)).add_const (ε ^ 2)
    convert this using 1; simp
  have hd1 : deriv (fun t => Real.log (q t) / 2) =
      fun t => ((x.re + t * v.re) * v.re + (x.im + t * v.im) * v.im) / q t := by
    funext t
    have := ((hq' t).log (hqpos t).ne').div_const 2
    rw [this.deriv]; field_simp
  rw [hfun, hd1]
  have hn : HasDerivAt (fun t : ℝ => (x.re + t * v.re) * v.re + (x.im + t * v.im) * v.im)
      (v.re ^ 2 + v.im ^ 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x.re + t * v.re) v.re 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.re).const_add x.re
    have h2 : HasDerivAt (fun t : ℝ => x.im + t * v.im) v.im 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.im).const_add x.im
    convert (h1.mul_const v.re).add (h2.mul_const v.im) using 1; ring
  rw [(hn.fun_div (hq' 0) (hqpos 0).ne').deriv]
  have hq0 : q 0 = ‖x‖ ^ 2 + ε ^ 2 := by
    simp only [hq]; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hq0]; simp only [zero_mul, add_zero]
  field_simp

theorem laplacian_ureg {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Δ (ureg ε) x = 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hc := (ureg_contDiff hε).contDiffAt (x := x)
  rw [laplacian_eq_d2 hc, d2_eq_line hc, d2_eq_line hc, deriv2_ureg_line hε, deriv2_ureg_line hε]
  have hN : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  rw [← add_div, div_eq_div_iff (by positivity) (by positivity)]
  simp only [Complex.one_re, Complex.one_im, I_re, I_im]
  rw [hN]; ring

/-- `Δ log(Im z) = -1/(Im z)²` on the upper half-plane. -/
theorem laplacian_log_im {x : ℂ} (hx : 0 < x.im) :
    Δ (fun z : ℂ => Real.log z.im) x = -1 / x.im ^ 2 := by
  have hc : ContDiffAt ℝ 2 (fun z : ℂ => Real.log z.im) x :=
    (Complex.imCLM.contDiff.contDiffAt).log hx.ne'
  rw [laplacian_eq_d2 hc, d2_eq_line hc, d2_eq_line hc]
  have e1 : (fun t : ℝ => Real.log (x + t • (1:ℂ)).im) = fun _ => Real.log x.im := by
    funext t; simp
  have e2 : (fun t : ℝ => Real.log (x + t • I).im) = fun t => Real.log (x.im + t) := by
    funext t; simp
  rw [e1, e2]
  simp only [deriv_const', zero_add]
  have hev : deriv (fun t : ℝ => Real.log (x.im + t)) =ᶠ[𝓝 0] fun t => (x.im + t)⁻¹ := by
    have : ∀ᶠ t in 𝓝 (0:ℝ), 0 < x.im + t := by
      have hc : Continuous (fun t : ℝ => x.im + t) := by fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hx))
    filter_upwards [this] with t ht
    have := ((hasDerivAt_id t).const_add x.im).log ht.ne'
    simp only [id] at this
    rw [this.deriv]; simp
  rw [hev.deriv_eq]
  have := ((hasDerivAt_id (0:ℝ)).const_add x.im).fun_inv (by simpa using hx.ne')
  simp only [id] at this
  rw [this.deriv]; simp

end ValenceCocompact

/-! ### Part A3 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem abs_log_le (R r : ℝ) (hr0 : 0 < r) (hr : r < R) : |Real.log r| ≤ (1 + R ^ 2) * r⁻¹ := by
  rw [le_mul_inv_iff₀ hr0]
  rcases le_or_gt r 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt r hr0 h1
    rw [abs_mul, abs_of_pos hr0] at this
    nlinarith
  · have hl : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
    have hl0 : 0 ≤ Real.log r := Real.log_nonneg h1.le
    rw [abs_of_nonneg hl0]
    nlinarith

theorem integrableOn_log_norm_ball (R : ℝ) :
    IntegrableOn (fun x : ℂ => Real.log ‖x‖) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1 + R ^ 2) (α := 1) (by simp) (by simp) ?_ ?_
  · rw [ae_restrict_iff' measurableSet_ball]
    refine Eventually.of_forall fun x hx => ?_
    rw [mem_ball_zero_iff] at hx
    rw [Real.rpow_neg_one, Real.norm_eq_abs]
    rcases eq_or_lt_of_le (norm_nonneg x) with h | h
    · rw [← h]; simp
    · exact abs_log_le R ‖x‖ h hx
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable

theorem locallyIntegrable_log_norm : LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  exact (integrableOn_log_norm_ball R).mono_set hR

theorem integrable_log_norm_mul {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => Real.log ‖x‖ * g x) := by
  simpa [smul_eq_mul] using
    locallyIntegrable_log_norm.integrable_smul_right_of_hasCompactSupport hg hgc

theorem integral_radial : ∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 = 2 * Real.pi := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => 2 / (y ^ 2 + 1) ^ 2)
  rw [h]
  have hball : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have key : ∫ y in Ioi (0:ℝ), y * (2 / (y ^ 2 + 1) ^ 2) = 1 := by
    have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
      (g := fun y : ℝ => -(y ^ 2 + 1)⁻¹) (g' := fun y : ℝ => y * (2 / (y ^ 2 + 1) ^ 2))
      (fun x _ => by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
          simpa using (hasDerivAt_pow 2 x).add_const 1
        have := (h1.inv (by positivity)).neg
        convert this using 1
        field_simp)
      (fun x hx => by have : (0:ℝ) < x := hx; positivity)
      (by
        have : Tendsto (fun y : ℝ => y ^ 2 + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by norm_num))
        exact this.inv_tendsto_atTop.neg.congr (fun _ => rfl) |>.trans (by simp))
    rw [this]; norm_num
  have hI : ∫ y in Ioi (0:ℝ), y ^ (Module.finrank ℝ ℂ - 1) • (2 / (y ^ 2 + 1) ^ 2) = 1 := by
    simp only [Complex.finrank_real_complex, smul_eq_mul]
    simpa using key
  rw [hI, hball, Complex.finrank_real_complex]; simp

end ValenceCocompact

/-! ### Part A4 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem laplacian_continuous {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) : Continuous (Δ χ) := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  have h := hχ.continuous_iteratedFDeriv' (m := 2)
  exact ((continuous_eval_const _).comp h).add ((continuous_eval_const _).comp h)

theorem tsupport_laplacian_subset (χ : ℂ → ℝ) : tsupport (Δ χ) ⊆ tsupport χ := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra h
  apply hx
  have := image_eq_zero_of_notMem_tsupport
    (fun hx' => h (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := χ) 2 hx'))
  simp [this]

theorem laplacian_hasCompactSupport {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (Δ χ) :=
  hχc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset χ)

theorem integral_scale {χ : ℂ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∫ x, 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 * χ x =
      ∫ z, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z) := by
  have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun x => 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 * χ x) ε (hR := hε.le)
  have h2 : (fun z : ℂ => 2 * ε ^ 2 / (‖ε • z‖ ^ 2 + ε ^ 2) ^ 2 * χ (ε • z)) =
      fun z => (ε ^ 2)⁻¹ * (2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) := by
    funext z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    field_simp
  rw [h2, integral_const_mul, Complex.finrank_real_complex, smul_eq_mul] at h1
  exact (mul_left_cancel₀ (by positivity) h1).symm

theorem abs_ureg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℂ} (hx : x ≠ 0) :
    |ureg ε x| ≤ |Real.log ‖x‖| + Real.log (‖x‖ ^ 2 + 1) / 2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have ha : Real.log ‖x‖ ≤ ureg ε x := by
    unfold ureg
    have : Real.log (‖x‖ ^ 2) ≤ Real.log (‖x‖ ^ 2 + ε ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hb : ureg ε x ≤ Real.log (‖x‖ ^ 2 + 1) / 2 := by
    unfold ureg
    have : Real.log (‖x‖ ^ 2 + ε ^ 2) ≤ Real.log (‖x‖ ^ 2 + 1) :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  have hb0 : 0 ≤ Real.log (‖x‖ ^ 2 + 1) / 2 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ ‖x‖ ^ 2 + 1 by nlinarith); linarith
  rcases le_or_gt 0 (ureg ε x) with h | h
  · rw [abs_of_nonneg h]; linarith [abs_nonneg (Real.log ‖x‖)]
  · rw [abs_of_neg h]; linarith [neg_abs_le (Real.log ‖x‖)]

/-- **The fundamental solution**: `∫ log|x| Δχ = 2π χ(0)` for a `C²` test function. -/
theorem integral_log_norm_laplacian_zero {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) : ∫ x, Real.log ‖x‖ * Δ χ x = 2 * Real.pi * χ 0 := by
  set l : Filter ℝ := 𝓝[>] 0
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  -- equality for ε > 0
  have heq : ∀ᶠ ε in l, ∫ x, ureg ε x * Δ χ x = ∫ z, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    rw [integral_mul_laplacian isOpen_univ (ureg_contDiff hε).contDiffOn hχ hχc (subset_univ _)]
    simp_rw [laplacian_ureg hε]
    exact integral_scale hε
  -- right side limit
  have hint : Integrable (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2) :=
    .of_integral_ne_zero (by rw [integral_radial]; positivity)
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have T1 : Tendsto (fun ε : ℝ => ∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) l
      (𝓝 (∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2 * C)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) (hint.mul_const C) ?_
    · exact (Continuous.mul (show Continuous (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2) by
          fun_prop (disch := (intro; positivity)))
        (hχ.continuous.comp (show Continuous (fun z : ℂ => ε • z) by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
    · refine Eventually.of_forall fun z => ?_
      have hc : Continuous (fun ε : ℝ => 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) :=
        continuous_const.mul (hχ.continuous.comp (continuous_id.smul continuous_const))
      have := hc.tendsto 0
      simp only [zero_smul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
  rw [integral_mul_const, integral_radial] at T1
  -- left side limit
  have hbint : Integrable (fun x => |Real.log ‖x‖ * Δ χ x| + Real.log (‖x‖ ^ 2 + 1) / 2 * |Δ χ x|) := by
    refine (integrable_log_norm_mul hΔ hΔc).abs.add ?_
    exact (Continuous.mul (show Continuous (fun x : ℂ => Real.log (‖x‖ ^ 2 + 1) / 2) by
      fun_prop (disch := (intro; positivity))) hΔ.abs).integrable_of_hasCompactSupport
      hΔc.abs.mul_left
  have hae : ∀ᵐ x : ℂ, x ≠ 0 := by
    rw [ae_iff]; simp
  have T2 : Tendsto (fun ε : ℝ => ∫ x, ureg ε x * Δ χ x) l (𝓝 (∫ x, Real.log ‖x‖ * Δ χ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((ureg_contDiff hε).continuous.mul hΔ).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      filter_upwards [hae] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have := abs_ureg_le hε.1 hε.2 hx
      nlinarith [abs_nonneg (Δ χ x)]
    · filter_upwards [hae] with x hx
      have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hc : ContinuousAt (fun ε : ℝ => ureg ε x * Δ χ x) 0 := by
        unfold ureg
        refine ContinuousAt.mul (ContinuousAt.div_const ?_ _) continuousAt_const
        exact (continuous_const.add (continuous_pow 2)).continuousAt.log (by simp; positivity)
      have := hc.tendsto
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      convert this using 2
      simp only [ureg]
      rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, Real.log_pow]; push_cast; ring
  have T1' := T1.congr' (EventuallyEq.symm heq)
  have := tendsto_nhds_unique T2 T1'
  rw [this]

/-- **The fundamental solution**: `∫ log|x - u| Δχ = 2π χ(u)`. -/
theorem integral_log_norm_sub_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (u : ℂ) : ∫ x, Real.log ‖x - u‖ * Δ χ x = 2 * Real.pi * χ u := by
  set χu : ℂ → ℝ := fun x => χ (x + u)
  have h1 : ContDiff ℝ 2 χu := hχ.comp (contDiff_id.add contDiff_const)
  have h2 : HasCompactSupport χu := hχc.comp_homeomorph (Homeomorph.addRight u)
  have h3 : ∀ y, Δ χu y = Δ χ (y + u) := by
    intro y
    rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [χu, iteratedFDeriv_comp_add_right]
  have := integral_log_norm_laplacian_zero h1 h2
  simp only [h3, χu, zero_add] at this
  rw [← this, ← integral_add_right_eq_self (μ := volume) (fun x => Real.log ‖x - u‖ * Δ χ x) u]
  simp

end ValenceCocompact

/-! ### Part A5 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem integrable_log_norm_sub_mul {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : ℂ) : Integrable (fun x => Real.log ‖x - u‖ * g x) := by
  have h := integrable_log_norm_mul (g := fun y => g (y + u)) (hg.comp (continuous_id.add continuous_const))
    (hgc.comp_homeomorph (Homeomorph.addRight u))
  have := h.comp_sub_right u
  simpa using this

/-- Harmonic functions integrate to zero against `Δχ`. -/
theorem integral_log_norm_nonvanishing {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hg : AnalyticOnNhd ℂ g V) (hg0 : ∀ u ∈ V, g u ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) :
    ∫ x, Real.log ‖g x‖ * Δ χ x = 0 := by
  have hH : ∀ x ∈ V, InnerProductSpace.HarmonicAt (fun z => Real.log ‖g z‖) x :=
    fun x hx => (hg x hx).harmonicAt_log_norm (hg0 x hx)
  have hC : ContDiffOn ℝ 2 (fun z => Real.log ‖g z‖) V :=
    fun x hx => (hH x hx).1.contDiffWithinAt
  rw [integral_mul_laplacian hV hC hχ hχc hχV]
  have : ∀ x, Δ (fun z => Real.log ‖g z‖) x * χ x = 0 := by
    intro x
    by_cases hx : χ x = 0
    · simp [hx]
    · have hxV : x ∈ V := hχV (subset_tsupport _ hx)
      rw [(hH x hxV).2.eq_of_nhds]; simp
  simp [this]

/-- Zeros of a nonzero analytic function on a preconnected open set are isolated. -/
theorem zeros_isolated {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {z : ℂ} (hz : z ∈ U) : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 := by
  rcases (hF z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨w, hw, hFw⟩ := hne
    exact hFw (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz h hw)
  · exact h

theorem order_ne_top {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {z : ℂ} (hz : z ∈ U) : analyticOrderAt F z ≠ ⊤ := by
  obtain ⟨w, hw, hFw⟩ := hne
  exact hF.analyticOrderAt_ne_top_of_isPreconnected hU hw hz
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr hFw)]; simp)

/-- **Riesz decomposition of `log |F|`** (the distributional Laplacian of `log|F|` is `2π Σ ord_ρ δ_ρ`):
for `F` analytic and not identically zero on a preconnected open `U` and a `C²` test function `χ`
supported in `U`, `∫ log|F| Δχ = 2π Σ_ρ ord_ρ(F) χ(ρ)`; also the integrand is integrable. -/
theorem integral_log_norm_analytic {F : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Integrable (fun x => Real.log ‖F x‖ * Δ χ x) ∧
    ∫ x, Real.log ‖F x‖ * Δ χ x =
      2 * Real.pi * ∑ᶠ z, ((analyticOrderAt F z).toNat : ℝ) * χ z := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hχc hUo hχU
  have hFV : MeromorphicOn F V := fun x hx => (hF x (hVU (subset_closure hx))).meromorphicAt
  have hFcl : MeromorphicOn F (closure V) := fun x hx => (hF x (hVU hx)).meromorphicAt
  have hfin : (MeromorphicOn.divisor F V).support.Finite :=
    hFcl.divisor_support_finite_of_subset hVc subset_closure
  have hord : ∀ u : V, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    rw [(hF u (hVU (subset_closure u.2))).meromorphicOrderAt_eq]
    have := order_ne_top hU hF hne (hVU (subset_closure u.2))
    revert this
    cases analyticOrderAt F u <;> simp
  obtain ⟨g, hg, hg0, hfg⟩ := hFV.extract_zeros_poles hord hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfg
  set D := MeromorphicOn.divisor F V
  set S := hfin.toFinset
  -- evaluate the finsum of functions
  have hsum : ∀ x, (∑ᶠ u, (fun z => (D u : ℝ) * Real.log ‖z - u‖)) x =
      ∑ u ∈ S, (D u : ℝ) * Real.log ‖x - u‖ := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (s := S)]
    · rw [Finset.sum_apply]
    · intro u hu
      simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
      intro h; apply hu; simp [h]; rfl
  -- a.e. equality on V
  have hae : ∀ᵐ x, x ∈ V → Real.log ‖F x‖ = ∑ u ∈ S, (D u : ℝ) * Real.log ‖x - u‖ +
      Real.log ‖g x‖ := by
    have h1 : ∀ᵐ x ∂(volume.restrict V), Real.log ‖F x‖ =
        ((∑ᶠ u, fun z => (D u : ℝ) * Real.log ‖z - u‖) + fun z => Real.log ‖g z‖) x :=
      ae_restrict_le_codiscreteWithin hVo.measurableSet hlog
    rw [ae_restrict_iff' hVo.measurableSet] at h1
    filter_upwards [h1] with x hx hxV
    have := hx hxV
    simp only [Pi.add_apply] at this
    rw [this, hsum]
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  have hΔV : tsupport (Δ χ) ⊆ V := (tsupport_laplacian_subset χ).trans hKV
  have heq : (fun x => Real.log ‖F x‖ * Δ χ x) =ᵐ[volume]
      fun x => ∑ u ∈ S, (D u : ℝ) * (Real.log ‖x - u‖ * Δ χ x) + Real.log ‖g x‖ * Δ χ x := by
    filter_upwards [hae] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · have : Δ χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxV (hΔV h))
      simp [this]
  have hgint : Integrable (fun x => Real.log ‖g x‖ * Δ χ x) := by
    have hc : ContinuousOn (fun x => Real.log ‖g x‖) V :=
      fun x hx => ((hg x hx).continuousAt.norm.log (by simpa using hg0 ⟨x, hx⟩)).continuousWithinAt
    exact integrable_mul_of hVo hc hΔ hΔc hΔV
  have hsint : ∀ u ∈ S, Integrable (fun x => (D u : ℝ) * (Real.log ‖x - u‖ * Δ χ x)) :=
    fun u _ => (integrable_log_norm_sub_mul hΔ hΔc u).const_mul _
  refine ⟨(Integrable.add (integrable_finsetSum _ hsint) hgint).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add (integrable_finsetSum _ hsint) hgint,
    integral_finsetSum _ hsint,
    integral_log_norm_nonvanishing hVo hg (fun u hu => hg0 ⟨u, hu⟩) hχ hχc hKV, add_zero]
  simp_rw [integral_const_mul, integral_log_norm_sub_laplacian hχ hχc]
  rw [finsum_eq_sum_of_support_subset _ (s := S), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun u hu => ?_
    have huV : u ∈ V := D.supportWithinDomain (by simpa [S] using hu)
    have hD : (D u : ℝ) = ((analyticOrderAt F u).toNat : ℝ) := by
      simp only [D]
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF.mono (subset_closure.trans hVU)) huV]
      have := order_ne_top hU hF hne (hVU (subset_closure huV))
      revert this
      cases analyticOrderAt F u <;> simp
    rw [hD]; ring
  · intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    have huV : u ∈ V := hKV (subset_tsupport _ hu.2)
    simp only [Set.Finite.coe_toFinset, Function.mem_support, S, D]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF.mono (subset_closure.trans hVU)) huV]
    have := order_ne_top hU hF hne (hVU (subset_closure huV))
    have h1 := hu.1
    revert this h1
    cases analyticOrderAt F u <;> simp

end ValenceCocompact

/-! ### Part A6 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem bilin_rot' (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (α β : ℝ) :
    B (α • (1:ℂ) + β • I) (α • (1:ℂ) + β • I) + B ((-β) • (1:ℂ) + α • I) ((-β) • (1:ℂ) + α • I) =
      (α ^ 2 + β ^ 2) * (B 1 1 + B I I) := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

theorem bilin_rot (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (a * I) (a * I) = ‖a‖ ^ 2 * (B 1 1 + B I I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • I := by apply Complex.ext <;> simp
  have haI : a * I = (-a.im) • (1 : ℂ) + a.re • I := by apply Complex.ext <;> simp
  have hn : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [haI, hn]
  have := bilin_rot' B a.re a.im
  rw [← ha] at this
  exact this

theorem fderiv_real_of_complex {φ : ℂ → ℂ} {y : ℂ} (h : DifferentiableAt ℂ φ y) (v : ℂ) :
    HasFDerivAt φ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv φ y)).restrictScalars ℝ) y
    ∧ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv φ y)).restrictScalars ℝ) v =
      deriv φ y * v := by
  refine ⟨h.hasDerivAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp [mul_comm]

/-- `d2 (χ ∘ φ) v z` for `φ` holomorphic. -/
theorem d2_comp {χ : ℂ → ℝ} {φ : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hχ : ContDiffAt ℝ 2 χ (φ z)) (v : ℂ) :
    d2 (χ ∘ φ) v z = fderiv ℝ χ (φ z) (deriv (deriv φ) z * v * v) +
      fderiv ℝ (fderiv ℝ χ) (φ z) (deriv φ z * v) (deriv φ z * v) := by
  have hφev : ∀ᶠ y in 𝓝 z, AnalyticAt ℂ φ y := hφ.eventually_analyticAt
  have hχev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 χ (φ y) :=
    hφ.continuousAt.eventually (hχ.eventually (by simp))
  have hev : (fun y => fderiv ℝ (χ ∘ φ) y v) =ᶠ[𝓝 z]
      fun y => fderiv ℝ χ (φ y) (deriv φ y * v) := by
    filter_upwards [hφev, hχev] with y hy1 hy2
    obtain ⟨hL, hLv⟩ := fderiv_real_of_complex hy1.differentiableAt v
    have hχy : HasFDerivAt χ (fderiv ℝ χ (φ y)) (φ y) :=
      (hy2.differentiableAt (by norm_num)).hasFDerivAt
    rw [(hχy.comp y hL).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hLv]
  unfold d2
  rw [hev.fderiv_eq]
  -- derivative of y ↦ fderiv χ (φ y)
  obtain ⟨hLz, hLzv⟩ := fderiv_real_of_complex hφ.differentiableAt v
  have hd2 : DifferentiableAt ℝ (fderiv ℝ χ) (φ z) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : HasFDerivAt (fun y => fderiv ℝ χ (φ y)) _ z := hd2.hasFDerivAt.comp z hLz
  -- derivative of y ↦ deriv φ y * v
  have hφ' : AnalyticAt ℂ (deriv φ) z := hφ.deriv
  have hH : HasDerivAt (fun y => deriv φ y * v) (deriv (deriv φ) z * v) z :=
    hφ'.differentiableAt.hasDerivAt.mul_const v
  obtain ⟨hHf, hHv⟩ := fderiv_real_of_complex (φ := fun y => deriv φ y * v)
    hH.differentiableAt v
  rw [hH.deriv] at hHf hHv
  have := (hG.clm_apply hHf).fderiv
  rw [this]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hHv, hLzv]

/-- **Conformal invariance of the Laplacian**: `Δ(χ ∘ φ)(z) = |φ'(z)|² (Δχ)(φ z)` for `φ` holomorphic. -/
theorem laplacian_comp_holomorphic {χ : ℂ → ℝ} {φ : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hχ : ContDiffAt ℝ 2 χ (φ z)) :
    Δ (χ ∘ φ) z = ‖deriv φ z‖ ^ 2 * Δ χ (φ z) := by
  have hc : ContDiffAt ℝ 2 (χ ∘ φ) z :=
    hχ.comp z (hφ.contDiffAt.restrict_scalars ℝ)
  rw [laplacian_eq_d2 hc, d2_comp hφ hχ, d2_comp hφ hχ, laplacian_eq_d2 hχ]
  rw [d2, d2]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ χ) (φ z) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd2 (differentiableAt_const 1), fderiv_clm_apply hd2 (differentiableAt_const I)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply]
  have hrot := bilin_rot (fderiv ℝ (fderiv ℝ χ) (φ z)) (deriv φ z)
  have h1 : deriv (deriv φ) z * 1 * 1 = - (deriv (deriv φ) z * I * I) := by
    rw [mul_assoc, mul_assoc, I_mul_I]; ring
  rw [h1, map_neg, mul_one]
  linear_combination hrot

end ValenceCocompact

/-! ### Part B1 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise


namespace ValenceCocompact

/-- The Möbius map of `γ` on `ℂ`. -/
def mob (γ : GL (Fin 2) ℝ) (w : ℂ) : ℂ := UpperHalfPlane.num γ w / UpperHalfPlane.denom γ w

theorem det_val_eq (γ : GL (Fin 2) ℝ) :
    (γ.det : ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℝ).det := Matrix.GeneralLinearGroup.val_det_apply γ

theorem coe_smul_eq_mob {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (z : UpperHalfPlane) : ((γ • z : UpperHalfPlane) : ℂ) = mob γ z :=
  UpperHalfPlane.coe_smul_of_det_pos (by rw [det_val_eq]; exact hγ) z

theorem denom_ne {γ : GL (Fin 2) ℝ} {w : ℂ} (hw : 0 < w.im) : UpperHalfPlane.denom γ w ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hw.ne'

theorem hasDerivAt_mob (γ : GL (Fin 2) ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (mob γ) (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) / UpperHalfPlane.denom γ w ^ 2) w := by
  have h1 : HasDerivAt (fun w : ℂ => UpperHalfPlane.num γ w) ((γ 0 0 : ℝ) : ℂ) w := by
    simpa [UpperHalfPlane.num] using
      ((hasDerivAt_id w).const_mul ((γ 0 0 : ℝ) : ℂ)).add_const ((γ 0 1 : ℝ) : ℂ)
  have h2 : HasDerivAt (fun w : ℂ => UpperHalfPlane.denom γ w) ((γ 1 0 : ℝ) : ℂ) w := by
    simpa [UpperHalfPlane.denom] using
      ((hasDerivAt_id w).const_mul ((γ 1 0 : ℝ) : ℂ)).add_const ((γ 1 1 : ℝ) : ℂ)
  have := h1.fun_div h2 (denom_ne hw)
  have e : mob γ = fun y => UpperHalfPlane.num γ y / UpperHalfPlane.denom γ y := rfl
  rw [e]
  convert this using 1
  rw [Matrix.det_fin_two]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  push_cast
  ring

theorem analyticAt_mob (γ : GL (Fin 2) ℝ) {w : ℂ} (hw : 0 < w.im) : AnalyticAt ℂ (mob γ) w := by
  unfold mob UpperHalfPlane.num UpperHalfPlane.denom
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  exact denom_ne hw

theorem mob_im {γ : GL (Fin 2) ℝ} (w : ℂ) :
    (mob γ w).im = (γ : Matrix (Fin 2) (Fin 2) ℝ).det * w.im /
      Complex.normSq (UpperHalfPlane.denom γ w) := by
  rw [mob, UpperHalfPlane.moebius_im, det_val_eq]

theorem mob_im_pos {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) {w : ℂ}
    (hw : 0 < w.im) : 0 < (mob γ w).im := by
  rw [mob_im]
  exact div_pos (mul_pos hγ hw) (Complex.normSq_pos.2 (denom_ne hw))

theorem norm_deriv_mob_sq {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {w : ℂ} (hw : 0 < w.im) :
    ‖deriv (mob γ) w‖ ^ 2 * w.im ^ 2 = (mob γ w).im ^ 2 := by
  rw [(hasDerivAt_mob γ hw).deriv, mob_im, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hγ.le]
  have hd := denom_ne (γ := γ) hw
  have hn : ‖UpperHalfPlane.denom γ w‖ ^ 2 = Complex.normSq (UpperHalfPlane.denom γ w) :=
    Complex.sq_norm _
  have hpos : 0 < ‖UpperHalfPlane.denom γ w‖ := norm_pos_iff.2 hd
  rw [← hn]
  field_simp

/-- Conformal invariance of `y² Δ` under `γ ∈ GL₂⁺(ℝ)`. -/
theorem im_sq_laplacian_comp_mob {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) {w : ℂ} (hw : 0 < w.im) :
    w.im ^ 2 * Δ (χ ∘ mob γ) w = (mob γ w).im ^ 2 * Δ χ (mob γ w) := by
  rw [laplacian_comp_holomorphic (analyticAt_mob γ hw) hχ.contDiffAt, ← norm_deriv_mob_sq hγ hw]
  ring

/-! ## The group of Möbius maps of `Γ` -/

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- `Γ` as a subgroup. -/
def subG {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := Γ
  mul_mem' ha hb := hΓ.mul_mem _ ha _ hb
  one_mem' := hΓ.one_mem
  inv_mem' ha := hΓ.inv_mem _ ha

/-- The group of Möbius transformations of `H` (a subgroup of `Perm ℍ`). -/
def permG (H : Subgroup (GL (Fin 2) ℝ)) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  H.map (MulAction.toPermHom (GL (Fin 2) ℝ) UpperHalfPlane)

theorem mem_permG {H : Subgroup (GL (Fin 2) ℝ)} {σ : Equiv.Perm UpperHalfPlane} :
    σ ∈ permG H ↔ ∃ γ ∈ H, ∀ z, σ z = γ • z := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, fun z => rfl⟩
  · rintro ⟨γ, hγ, h⟩; exact ⟨γ, hγ, Equiv.ext fun z => (h z).symm⟩

theorem smul_def {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) (z : UpperHalfPlane) :
    g • z = (g : Equiv.Perm UpperHalfPlane) z := rfl

/-- A representative matrix. -/
def rep {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) : GL (Fin 2) ℝ :=
  Classical.choose (mem_permG.1 g.2)

theorem rep_mem {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) : rep g ∈ H :=
  (Classical.choose_spec (mem_permG.1 g.2)).1

theorem rep_smul {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) (z : UpperHalfPlane) :
    g • z = rep g • z :=
  (Classical.choose_spec (mem_permG.1 g.2)).2 z

theorem smul_fun_eq {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) :
    (fun z : UpperHalfPlane => g • z) = fun z => rep g • z := funext (rep_smul g)

instance (H : Subgroup (GL (Fin 2) ℝ)) : MeasurableConstSMul (permG H) UpperHalfPlane :=
  ⟨fun g => by
    rw [smul_fun_eq g]
    exact (continuous_const_smul (rep g)).measurable⟩

instance (H : Subgroup (GL (Fin 2) ℝ)) :
    SMulInvariantMeasure (permG H) UpperHalfPlane volume :=
  ⟨fun g s hs => by
    rw [smul_fun_eq g]
    exact measure_preimage_smul (μ := (volume : Measure UpperHalfPlane)) (rep g) s⟩

theorem toPerm_mem {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ Γ) : MulAction.toPerm γ ∈ permG (subG hΓ) := ⟨γ, hγ, rfl⟩

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

theorem rep_memΓ (g : permG (subG hΓ)) : rep g ∈ Γ := rep_mem g

theorem rep_det (g : permG (subG hΓ)) : 0 < (rep g : Matrix (Fin 2) (Fin 2) ℝ).det :=
  hΓ.det_pos _ (rep_mem g)

theorem finite_meet {K : Set UpperHalfPlane} (hK : IsCompact K) :
    {g : permG (subG hΓ) | ((fun z => g • z) '' K ∩ K).Nonempty}.Finite := by
  have h := hΓ.properlyDiscontinuous K hK
  refine (h.preimage (f := fun g : permG (subG hΓ) => fun z => g • z) ?_).subset ?_
  · intro g _ h _ e
    apply Subtype.ext; apply Equiv.ext; intro z
    exact congrFun e z
  · intro g hg
    exact ⟨rep g, rep_mem g, smul_fun_eq g, hg⟩

theorem countable_G : Countable (permG (subG hΓ)) := by
  set z0 : UpperHalfPlane := UpperHalfPlane.I
  have hU : (Set.univ : Set (permG (subG hΓ))) ⊆
      ⋃ n, {g | ((fun z => g • z) '' (compactCovering UpperHalfPlane n ∪ {z0}) ∩
        (compactCovering UpperHalfPlane n ∪ {z0})).Nonempty} := by
    intro g _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering UpperHalfPlane).symm ▸
      Set.mem_univ (g • z0))
    exact Set.mem_iUnion.2 ⟨n, ⟨g • z0, ⟨z0, Or.inr rfl, rfl⟩, Or.inl hn⟩⟩
  have : (Set.univ : Set (permG (subG hΓ))).Countable :=
    (Set.countable_iUnion fun n =>
      (finite_meet hΓ ((isCompact_compactCovering UpperHalfPlane n).union
        isCompact_singleton)).countable).mono hU
  exact Set.countable_univ_iff.1 this

theorem isFundamentalDomain {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) :
    IsFundamentalDomain (permG (subG hΓ)) s volume := by
  refine IsFundamentalDomain.mk'' hs.1.nullMeasurableSet ?_ ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    obtain ⟨γ, hγ, hz⟩ := hs.2.1 z
    exact ⟨⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩, hz⟩
  · intro g hg
    have hg' : g⁻¹ ≠ 1 := inv_ne_one.2 hg
    have hne : (fun z : UpperHalfPlane => rep g⁻¹ • z) ≠ id := by
      intro h; apply hg'
      apply Subtype.ext; apply Equiv.ext; intro z
      simp only [← smul_def, rep_smul, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      exact congrFun h z
    have h0 := hs.2.2 (rep g⁻¹) (rep_mem g⁻¹) hne
    rw [← smul_fun_eq] at h0
    have : g • s = (fun z => g⁻¹ • z) ⁻¹' s := by
      ext z; simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [AEDisjoint, this, Set.inter_comm]
    exact h0
  · intro g
    exact (measurePreserving_smul g volume).quasiMeasurePreserving

theorem card_stabilizer (t : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (permG (subG hΓ)) t) = ellOrderOf Γ t := by
  unfold ellOrderOf
  apply Nat.card_congr
  let φ : MulAction.stabilizer (permG (subG hΓ)) t →
      {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • t = t ∧ f = fun z => γ • z} :=
    fun g => ⟨fun z => (g : permG (subG hΓ)) • z, rep (g : permG (subG hΓ)), rep_memΓ hΓ _,
      (rep_smul (g : permG (subG hΓ)) t).symm.trans (MulAction.mem_stabilizer_iff.1 g.2),
      smul_fun_eq _⟩
  refine Equiv.ofBijective φ ⟨?_, ?_⟩
  · intro g h e
    have e' : (fun z => (g : permG (subG hΓ)) • z) = fun z => (h : permG (subG hΓ)) • z :=
      congrArg Subtype.val e
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro z
    exact congrFun e' z
  · rintro ⟨f, γ, hγ, ht, rfl⟩
    refine ⟨⟨⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩, MulAction.mem_stabilizer_iff.2 ht⟩, rfl⟩

end ValenceCocompact

/-! ### Part B2 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise Manifold ContDiff


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem isCompact_preimage_coe {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ {w | 0 < w.im}) :
    IsCompact ((↑) ⁻¹' K : Set UpperHalfPlane) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff]
  · exact hK
  · intro w hw; exact ⟨⟨w, hKU hw⟩, rfl⟩

theorem exists_bump {C : Set UpperHalfPlane} (hC : IsCompact C) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ {w | 0 < w.im} ∧
      (∀ w, 0 ≤ ψ w) ∧ ∀ z ∈ C, ψ (z : ℂ) = 1 := by
  have hC' : IsCompact (((↑) : UpperHalfPlane → ℂ) '' C) := hC.image UpperHalfPlane.continuous_coe
  have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hCU : ((↑) : UpperHalfPlane → ℂ) '' C ⊆ {w | 0 < w.im} := by
    rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  obtain ⟨W, hWo, hCW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hC' hU hCU
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℂ)
    hWo.isClosed_compl hC'.isClosed (n := 2)
    (Set.disjoint_left.2 fun w hw hwC => hw (hCW hwC))
  have hsupp : tsupport f ⊆ closure W := by
    apply closure_mono
    intro w hw
    by_contra h
    exact hw (hf0 h)
  refine ⟨f, f.contMDiff.contDiff, hWc.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans hWU, fun w => (hf01 w).1, fun z hz => hf1 ⟨z, hz, rfl⟩⟩

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- Local finiteness: on a compact set, only finitely many translates of a compactly supported `χ`
are nonzero. -/
theorem locally_finite {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ S : Finset (permG (subG hΓ)), ∀ z ∈ K, ∀ g : permG (subG hΓ),
      (χ ((g • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) ∧ (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) := by
  have hL := isCompact_preimage_coe hχc hχU
  set L := ((↑) ⁻¹' tsupport χ : Set UpperHalfPlane)
  refine ⟨(finite_meet hΓ (hK.union hL)).toFinset, fun z hz g => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨g • z, ⟨z, Or.inl hz, rfl⟩, Or.inr (subset_tsupport _ h)⟩
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨z, ⟨g⁻¹ • z, Or.inr (subset_tsupport _ h), smul_inv_smul g z⟩, Or.inl hz⟩

theorem support_finite {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (z : UpperHalfPlane) :
    (Function.support fun g : permG (subG hΓ) => χ ((g • z : UpperHalfPlane) : ℂ)).Finite := by
  obtain ⟨S, hS⟩ := locally_finite hΓ hχc hχU (isCompact_singleton (x := z))
  exact S.finite_toSet.subset fun g hg => (hS z rfl g).1 hg

theorem finsum_eq_sum {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    {K : Set UpperHalfPlane} {S : Finset (permG (subG hΓ))}
    (hS : ∀ z ∈ K, ∀ g : permG (subG hΓ), (χ ((g • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) ∧
      (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S)) {z : UpperHalfPlane} (hz : z ∈ K) :
    ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) =
      ∑ g ∈ S, χ ((g • z : UpperHalfPlane) : ℂ) :=
  finsum_eq_sum_of_support_subset _ fun g hg => (hS z hz g).1 hg

theorem finsum_smul_invariant (φ : UpperHalfPlane → ℝ) (h z : UpperHalfPlane) (k : permG (subG hΓ))
    (hk : k • z = h) :
    ∑ᶠ g : permG (subG hΓ), φ (g • h) = ∑ᶠ g : permG (subG hΓ), φ (g • z) := by
  rw [← hk]
  simp_rw [smul_smul]
  exact finsum_comp_equiv (Equiv.mulRight k) (f := fun g => φ (g • z))

theorem rep_smul_coe (g : permG (subG hΓ)) {w : ℂ} (hw : 0 < w.im) :
    ((g • (⟨w, hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = mob (rep g) w := by
  rw [rep_smul, coe_smul_eq_mob (rep_det hΓ g)]

/-- **Automorphic partition of unity.** -/
theorem exists_partition :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ {w | 0 < w.im} ∧
      (∀ w, 0 ≤ χ w) ∧ ∀ z : UpperHalfPlane,
        ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1 := by
  obtain ⟨C, hC, hcov⟩ := hΓ.cocompact
  obtain ⟨ψ, hψ, hψc, hψU, hψ0, hψ1⟩ := exists_bump hC
  set Ψ : UpperHalfPlane → ℝ := fun z => ∑ᶠ g : permG (subG hΓ), ψ ((g • z : UpperHalfPlane) : ℂ)
  have hΨpos : ∀ z, 1 ≤ Ψ z := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hcov z
    have := single_le_finsum (f := fun g : permG (subG hΓ) => ψ ((g • z : UpperHalfPlane) : ℂ))
      ⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ (support_finite hΓ hψc hψU z) (fun g => hψ0 _)
    rw [smul_def] at this
    simp only [MulAction.toPerm_apply] at this
    rw [hψ1 _ hz] at this
    exact this
  have hΨinv : ∀ (k : permG (subG hΓ)) z, Ψ (k • z) = Ψ z := fun k z =>
    finsum_smul_invariant hΓ (fun x => ψ (x : ℂ)) _ z k rfl
  set χ : ℂ → ℝ := fun w => ψ w / Ψ (UpperHalfPlane.ofComplex w)
  have hχsupp : Function.support χ ⊆ Function.support ψ := by
    intro w hw h; apply hw; simp only [χ, h, zero_div]
  have hχts : tsupport χ ⊆ tsupport ψ := closure_mono hχsupp
  refine ⟨χ, ?_, hψc.of_isClosed_subset (isClosed_tsupport _) hχts, hχts.trans hψU,
    fun w => div_nonneg (hψ0 w) (by linarith [hΨpos (UpperHalfPlane.ofComplex w)]), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w0
    by_cases hw0 : 0 < w0.im
    · -- local finite sum
      have hball : closedBall w0 (w0.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        have := (abs_im_le_norm (w - w0)).trans hw
        simp only [sub_im, Set.mem_ofPred_eq] at this ⊢
        rw [abs_le] at this; linarith
      obtain ⟨S, hS⟩ := locally_finite hΓ hψc hψU
        (isCompact_preimage_coe (isCompact_closedBall w0 (w0.im / 2)) hball)
      have hev : χ =ᶠ[𝓝 w0] fun w => ψ w / ∑ g ∈ S, ψ (mob (rep g) w) := by
        filter_upwards [closedBall_mem_nhds w0 (by linarith : 0 < w0.im / 2)] with w hw
        have hwim : 0 < w.im := hball hw
        simp only [χ]
        congr 1
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwim]
        simp only [Ψ]
        rw [finsum_eq_sum hΓ hψc hψU hS (z := ⟨w, hwim⟩) hw]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [rep_smul_coe hΓ g hwim]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hden : (∑ g ∈ S, ψ (mob (rep g) w0)) ≠ 0 := by
        have := hΨpos ⟨w0, hw0⟩
        simp only [Ψ] at this
        rw [finsum_eq_sum hΓ hψc hψU hS (z := ⟨w0, hw0⟩) (mem_closedBall_self (by linarith))] at this
        simp_rw [rep_smul_coe hΓ _ hw0] at this
        linarith
      refine hψ.contDiffAt.div ?_ hden
      refine ContDiffAt.sum fun g _ => hψ.contDiffAt.comp w0 ?_
      exact (analyticAt_mob (rep g) hw0).contDiffAt.restrict_scalars ℝ
    · have hnot : w0 ∉ tsupport ψ := fun h => hw0 (hψU h)
      have hev : χ =ᶠ[𝓝 w0] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hnot] with w hw
        simp only [χ, hw, Pi.zero_apply, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro z
    have e : ∀ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) =
        ψ ((g • z : UpperHalfPlane) : ℂ) * (Ψ z)⁻¹ := by
      intro g
      simp only [χ, UpperHalfPlane.ofComplex_apply, hΨinv, div_eq_mul_inv]
    simp_rw [e]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (by linarith [hΨpos z])

end ValenceCocompact

/-! ### Part B3 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem range_coe' : Set.range ((↑) : UpperHalfPlane → ℂ) = {w : ℂ | 0 < w.im} :=
  UpperHalfPlane.range_coe

theorem density_eq (z : UpperHalfPlane) :
    (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) = 1 / (z : ℂ).im ^ 2 := by
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
  rw [div_pow, one_pow]; rfl

theorem measurable_density :
    Measurable fun z : UpperHalfPlane => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) := by
  refine Measurable.pow_const (Measurable.div measurable_const ?_) 2
  apply Measurable.subtype_mk
  exact Complex.measurable_im.comp UpperHalfPlane.measurable_coe

/-- `∫_ℍ f(z) y² dμ = ∫_ℂ f` for `f` vanishing off `ℍ`. -/
theorem integral_H (f : ℂ → ℝ) (hf : ∀ w : ℂ, w.im ≤ 0 → f w = 0) :
    ∫ z : UpperHalfPlane, f z * (z : ℂ).im ^ 2 = ∫ w, f w := by
  rw [UpperHalfPlane.volume_def, integral_withDensity_eq_integral_smul measurable_density]
  have e : ∀ z : UpperHalfPlane, ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) •
      (f z * (z : ℂ).im ^ 2) = f z := by
    intro z
    rw [NNReal.smul_def, smul_eq_mul, density_eq]
    have h : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  simp_rw [e]
  rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map (fun w => f w),
    UpperHalfPlane.measurableEmbedding_coe.map_comap, range_coe']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro w hw
  exact hf w (not_lt.1 hw)

theorem integrable_H {f : ℂ → ℝ} (hf : ∀ w : ℂ, w.im ≤ 0 → f w = 0) (hfi : Integrable f) :
    Integrable (fun z : UpperHalfPlane => f z * (z : ℂ).im ^ 2) := by
  rw [UpperHalfPlane.volume_def, integrable_withDensity_iff_integrable_smul measurable_density]
  have e : (fun z : UpperHalfPlane => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) •
      (f z * (z : ℂ).im ^ 2)) = fun z : UpperHalfPlane => f z := by
    funext z
    rw [NNReal.smul_def, smul_eq_mul, density_eq]
    have h : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  rw [e]
  change Integrable (f ∘ UpperHalfPlane.coe) _
  rw [← UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff,
    UpperHalfPlane.measurableEmbedding_coe.map_comap]
  exact hfi.restrict

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **Unfolding**: for the partition function `χ`, `∫_ℍ χ dμ = vol(s)`. -/
theorem lintegral_chi {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1) :
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (χ z) = volume s := by
  have := countable_G hΓ
  have hF := isFundamentalDomain hΓ hs
  rw [hF.lintegral_eq_tsum']
  have hmeas : ∀ g : permG (subG hΓ), Measurable fun z : UpperHalfPlane =>
      ENNReal.ofReal (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)) := fun g =>
    ENNReal.measurable_ofReal.comp (hχ.measurable.comp (UpperHalfPlane.measurable_coe.comp
      (measurable_const_smul g⁻¹)))
  rw [← lintegral_tsum (fun g => (hmeas g).aemeasurable)]
  have h1 : ∀ z : UpperHalfPlane, ∑' g : permG (subG hΓ),
      ENNReal.ofReal (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)) = 1 := by
    intro z
    have hinv : ∑ᶠ g : permG (subG hΓ), χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := by
      rw [← hsum z]
      exact finsum_comp_equiv (Equiv.inv _) (f := fun g => χ ((g • z : UpperHalfPlane) : ℂ))
    have hfin : (Function.support fun g : permG (subG hΓ) =>
        χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)).Finite := by
      exact (support_finite hΓ hχc hχU z).preimage (f := fun g : permG (subG hΓ) => g⁻¹)
        (inv_injective.injOn)
    rw [tsum_eq_sum (s := hfin.toFinset), ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hχ0 _),
      ← finsum_eq_sum_of_support_subset _ (by simp), hinv, ENNReal.ofReal_one]
    intro g hg
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hg
    simp [hg]
  simp_rw [h1]
  simp

end ValenceCocompact

/-! ### Part B4 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem laplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℝ) (x : ℂ)
    (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x) :
    Δ (fun w => ∑ i ∈ S, f i w) x = ∑ i ∈ S, Δ (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (fun _ : ℂ => (0:ℝ)) = fun _ => (0:ℝ) from rfl, laplacian_const]; rfl
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (f a) x := hf a (Finset.mem_insert_self a S)
    have h2 : ContDiffAt ℝ 2 (fun w => ∑ i ∈ S, f i w) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have := h1.laplacian_add h2
    rw [show (fun w => f a w + ∑ i ∈ S, f i w) = f a + fun w => ∑ i ∈ S, f i w from rfl, this,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem tsupport_laplacian_subset_U {χ : ℂ → ℝ} (hχU : tsupport χ ⊆ {w | 0 < w.im}) (w : ℂ)
    (hw : w.im ≤ 0) : Δ χ w = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    (not_lt.2 hw) (hχU (tsupport_laplacian_subset χ h))

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **The key cancellation**: for a `Γ`-invariant `Φ` with `ΦΔχ` integrable, `∫ Φ Δχ = 0`. -/
theorem integral_invariant_laplacian {Φ : ℂ → ℝ}
    (hΦ : ∀ (g : permG (subG hΓ)) (z : UpperHalfPlane), Φ ((g • z : UpperHalfPlane) : ℂ) = Φ z)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (hint : Integrable fun w => Φ w * Δ χ w) :
    ∫ w, Φ w * Δ χ w = 0 := by
  have hvan : ∀ w : ℂ, w.im ≤ 0 → Φ w * Δ χ w = 0 := fun w hw => by
    rw [tsupport_laplacian_subset_U hχU w hw, mul_zero]
  have hconv := (integral_H (fun w => Φ w * Δ χ w) hvan).symm
  have ha := integrable_H hvan hint
  rw [hconv]
  set a : UpperHalfPlane → ℝ := fun z => Φ z * Δ χ z * (z : ℂ).im ^ 2 with ha_def
  -- a compact neighbourhood of the support
  have hUo : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hχc hUo hχU
  set K' : Set UpperHalfPlane := (↑) ⁻¹' closure V
  have hK' : IsCompact K' := isCompact_preimage_coe hVc hVU
  obtain ⟨S, hS⟩ := locally_finite hΓ hχc hχU hK'
  have hS1 : ∀ z ∈ K', ∑ g ∈ S, χ ((g • z : UpperHalfPlane) : ℂ) = 1 := fun z hz => by
    rw [← finsum_eq_sum hΓ hχc hχU hS hz, hsum]
  have hS2 : ∀ z ∈ K', ∑ g ∈ S, χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := fun z hz => by
    have h1 : ∑ᶠ g : permG (subG hΓ), χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := by
      rw [← hsum z]
      exact finsum_comp_equiv (Equiv.inv _) (f := fun g => χ ((g • z : UpperHalfPlane) : ℂ))
    rw [← h1]
    exact (finsum_eq_sum_of_support_subset _ fun g hg => (hS z hz g).2 hg).symm
  have hχb : ∃ C, ∀ w, ‖χ w‖ ≤ C := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨C, hC⟩ := hχb
  have hmeasg : ∀ g : permG (subG hΓ), AEStronglyMeasurable
      (fun z : UpperHalfPlane => χ ((g • z : UpperHalfPlane) : ℂ)) volume := fun g =>
    (hχ.continuous.measurable.comp (UpperHalfPlane.measurable_coe.comp
      (measurable_const_smul g))).aestronglyMeasurable
  -- step (i)-(ii)
  have e1 : ∀ z, a z = ∑ g ∈ S, a z * χ ((g • z : UpperHalfPlane) : ℂ) := by
    intro z
    rw [← Finset.mul_sum]
    by_cases hz : (z : ℂ) ∈ tsupport χ
    · rw [hS1 z (subset_closure (hKV hz)), mul_one]
    · have : Δ χ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (tsupport_laplacian_subset χ h))
      simp [ha_def, this]
  have hint1 : ∀ g ∈ S, Integrable fun z => a z * χ ((g • z : UpperHalfPlane) : ℂ) :=
    fun g _ => ha.mul_bdd (hmeasg g) (Eventually.of_forall fun z => hC _)
  rw [integral_congr_ae (Eventually.of_forall e1), integral_finsetSum _ hint1]
  -- step (iii)-(iv)
  have e2 : ∀ g : permG (subG hΓ), ∀ z : UpperHalfPlane,
      a (g⁻¹ • z) * χ z = Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g z
    have hdet := rep_det hΓ g⁻¹
    rw [im_sq_laplacian_comp_mob hdet hχ z.im_pos]
    simp only [ha_def]
    rw [hΦ g⁻¹ z, rep_smul g⁻¹ z, coe_smul_eq_mob hdet]
    ring
  have e3 : ∀ g : permG (subG hΓ),
      ∫ z, a z * χ ((g • z : UpperHalfPlane) : ℂ) =
        ∫ z : UpperHalfPlane, Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g
    have := integral_smul_eq_self (μ := (volume : Measure UpperHalfPlane))
      (fun z => a (g⁻¹ • z) * χ z) (g := g)
    simp only [inv_smul_smul] at this
    rw [this]
    exact integral_congr_ae (Eventually.of_forall fun z => e2 g z)
  simp_rw [e3]
  have hint2 : ∀ g ∈ S, Integrable fun z : UpperHalfPlane =>
      Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g _
    have h1 : Integrable fun z : UpperHalfPlane => a (g⁻¹ • z) :=
      ((measurePreserving_smul g⁻¹ volume).integrable_comp ha.aestronglyMeasurable).2 ha
    have h2 := h1.mul_bdd (hχ.continuous.measurable.comp
      UpperHalfPlane.measurable_coe).aestronglyMeasurable (Eventually.of_forall fun z => hC z)
    exact h2.congr (Eventually.of_forall fun z => e2 g z)
  rw [← integral_finsetSum _ hint2]
  -- step (v)-(vi)
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  by_cases hz : χ z = 0
  · simp [hz]
  · have hzV : (z : ℂ) ∈ V := hKV (subset_tsupport _ hz)
    have hsumΔ : ∑ g ∈ S, Δ (χ ∘ mob (rep g⁻¹)) z = 0 := by
      rw [← laplacian_finset_sum S (fun g => χ ∘ mob (rep g⁻¹)) z
        (fun g _ => hχ.contDiffAt.comp _
          ((analyticAt_mob _ z.im_pos).contDiffAt.restrict_scalars ℝ))]
      have hev : (fun w => ∑ g ∈ S, (χ ∘ mob (rep g⁻¹)) w) =ᶠ[𝓝 (z : ℂ)] fun _ => (1 : ℝ) := by
        filter_upwards [hVo.mem_nhds hzV] with w hw
        have hwim : 0 < w.im := hVU (subset_closure hw)
        have := hS2 ⟨w, hwim⟩ (subset_closure hw : w ∈ closure V)
        rw [← this]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [Function.comp_apply]
        rw [rep_smul_coe hΓ g⁻¹ hwim]
      rw [(laplacian_congr_nhds hev).eq_of_nhds, laplacian_const]; rfl
    rw [hsumΔ]; ring

end ValenceCocompact

/-! ### Part B5 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- The invariant `log (|F| y^m)`. -/
def PhiF (m : ℕ) (F : ℂ → ℂ) (w : ℂ) : ℝ := Real.log (‖F w‖ * w.im ^ m)

theorem phiF_invariant {m : ℕ} {F : ℂ → ℂ} {γ : GL (Fin 2) ℝ}
    (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (z : UpperHalfPlane)
    (haut : ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) :
    PhiF m F ((γ • z : UpperHalfPlane) : ℂ) = PhiF m F z := by
  unfold PhiF
  congr 1
  have him : ((γ • z : UpperHalfPlane) : ℂ).im = (γ : Matrix (Fin 2) (Fin 2) ℝ).det * (z : ℂ).im /
      ‖UpperHalfPlane.denom γ z‖ ^ 2 := by
    rw [UpperHalfPlane.coe_im, UpperHalfPlane.im_smul_eq_div_normSq, det_val_eq, abs_of_pos hγ,
      Complex.sq_norm]
    rfl
  have hd : 0 < ‖UpperHalfPlane.denom γ z‖ := norm_pos_iff.2 (UpperHalfPlane.denom_ne_zero γ z)
  rw [him, div_pow, mul_pow, ← pow_mul]
  have hd2 : 0 < ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) := pow_pos hd _
  field_simp
  linear_combination haut

theorem codiscrete_ne_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0) :
    {w | F w ≠ 0} ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [zeros_isolated hU hF hne hx] with w hw
  intro h
  exact h.2 hw

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **The valence identity** `2π Σ ord_ρ χ(ρ) = m vol(s)` for the partition function `χ`. -/
theorem main_identity {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) {m : ℕ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {w | 0 < w.im}) (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ {w | 0 < w.im}) (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1) :
    volume s ≠ ⊤ ∧
      2 * Real.pi * ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w = m * (volume s).toReal := by
  have hUo : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨hint1, hR⟩ := integral_log_norm_analytic hUo hUc hF hne hχ hχc hχU
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  have hΔU : tsupport (Δ χ) ⊆ {w | 0 < w.im} := (tsupport_laplacian_subset χ).trans hχU
  have hlogim : ContDiffOn ℝ 2 (fun w : ℂ => Real.log w.im) {w | 0 < w.im} := fun w hw =>
    ((Complex.imCLM.contDiff.contDiffAt).log (ne_of_gt hw)).contDiffWithinAt
  have hint2 : Integrable fun w : ℂ => Real.log w.im * Δ χ w :=
    integrable_mul_of hUo hlogim.continuousOn hΔ hΔc hΔU
  -- a.e. decomposition of the invariant
  have hae0 : ∀ᵐ w : ℂ, w ∈ {w : ℂ | 0 < w.im} → F w ≠ 0 := by
    have : ∀ᵐ w ∂(volume.restrict {w : ℂ | 0 < w.im}), F w ≠ 0 :=
      ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) hUo.measurableSet
        (codiscrete_ne_zero hUc hF hne)
    rwa [ae_restrict_iff' hUo.measurableSet] at this
  have hdec : (fun w => PhiF m F w * Δ χ w) =ᵐ[volume]
      fun w => Real.log ‖F w‖ * Δ χ w + m * (Real.log w.im * Δ χ w) := by
    filter_upwards [hae0] with w hw
    by_cases hwU : 0 < w.im
    · have h1 := hw hwU
      unfold PhiF
      rw [Real.log_mul (norm_ne_zero_iff.2 h1) (pow_ne_zero _ hwU.ne'), Real.log_pow]
      ring
    · rw [tsupport_laplacian_subset_U hχU w (not_lt.1 hwU)]; ring
  have hint : Integrable fun w => PhiF m F w * Δ χ w :=
    (hint1.add (hint2.const_mul _)).congr hdec.symm
  -- invariance
  have hΦ : ∀ (g : permG (subG hΓ)) (z : UpperHalfPlane),
      PhiF m F ((g • z : UpperHalfPlane) : ℂ) = PhiF m F z := by
    intro g z
    rw [rep_smul]
    exact phiF_invariant (rep_det hΓ g) z (haut _ (rep_memΓ hΓ g) z)
  have h0 := integral_invariant_laplacian hΓ hΦ hχ hχc hχU hsum hint
  rw [integral_congr_ae hdec, integral_add hint1 (hint2.const_mul _), integral_const_mul, hR] at h0
  -- the log Im term
  have hlog : ∫ w, Real.log w.im * Δ χ w = - ∫ w, χ w / w.im ^ 2 := by
    rw [integral_mul_laplacian hUo hlogim hχ hχc hχU, ← integral_neg]
    congr 1; funext w
    by_cases hw : χ w = 0
    · simp [hw]
    · have hwU : 0 < w.im := hχU (subset_tsupport _ hw)
      rw [laplacian_log_im hwU]; ring
  -- the volume
  have hvan : ∀ w : ℂ, w.im ≤ 0 → χ w / w.im ^ 2 = 0 := fun w hw => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => (not_lt.2 hw) (hχU h)), zero_div]
  have hcH := integral_H (fun w => χ w / w.im ^ 2) hvan
  have he : ∀ z : UpperHalfPlane, χ z / (z : ℂ).im ^ 2 * (z : ℂ).im ^ 2 = χ z := fun z => by
    have : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  simp_rw [he] at hcH
  have hcont : ContinuousOn (fun w : ℂ => 1 / w.im ^ 2) {w | 0 < w.im} := fun w hw =>
    (continuousAt_const.div (Complex.continuous_im.continuousAt.pow 2)
      (pow_ne_zero _ (ne_of_gt hw))).continuousWithinAt
  have hχint : Integrable fun w : ℂ => χ w / w.im ^ 2 := by
    have := integrable_mul_of hUo hcont hχ.continuous hχc hχU
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only; ring
  have hχH : Integrable fun z : UpperHalfPlane => χ z := by
    have := integrable_H hvan hχint
    exact this.congr (Eventually.of_forall he)
  have hL := lintegral_chi hΓ hs hχ.continuous hχc hχU hχ0 hsum
  have hfin : volume s ≠ ⊤ := by
    rw [← hL]; exact (hχH.lintegral_lt_top).ne
  have hvol : ∫ z : UpperHalfPlane, χ z = (volume s).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => hχ0 _)
      (hχ.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable, hL]
  refine ⟨hfin, ?_⟩
  rw [hlog, ← hcH, hvol] at h0
  linarith

end ValenceCocompact

/-! ### Part B6 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem no_lower_order {p q : ℂ → ℝ} {t : ℂ} (hp : ContinuousAt p t) (hpt : p t ≠ 0)
    (hq : ContinuousAt q t) {k : ℕ} (hk : 0 < k)
    (h : ∀ᶠ w in 𝓝[≠] t, p w = ‖w - t‖ ^ k * q w) : False := by
  have h1 : Tendsto p (𝓝[≠] t) (𝓝 (p t)) := hp.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun w => ‖w - t‖ ^ k * q w) (𝓝[≠] t) (𝓝 (‖t - t‖ ^ k * q t)) :=
    (((continuous_id.sub continuous_const).norm.pow k).continuousAt.mul hq).tendsto.mono_left
      nhdsWithin_le_nhds
  simp only [sub_self, norm_zero, zero_pow hk.ne', zero_mul] at h2
  exact hpt (tendsto_nhds_unique h1 (h2.congr' (EventuallyEq.symm h)))

/-- Two analytic functions whose norms agree up to a continuous nonvanishing factor have the same
order. -/
theorem ord_eq_of_norm {f g : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t) (hg : AnalyticAt ℂ g t)
    {c : ℂ → ℝ} (hc : ContinuousAt c t) (hct : c t ≠ 0)
    (h : ∀ᶠ w in 𝓝 t, ‖f w‖ = c w * ‖g w‖) : analyticOrderAt f t = analyticOrderAt g t := by
  have hcev : ∀ᶠ w in 𝓝 t, c w ≠ 0 := hc.eventually_ne hct
  by_cases hgt : analyticOrderAt g t = ⊤
  · rw [hgt, analyticOrderAt_eq_top]
    filter_upwards [analyticOrderAt_eq_top.1 hgt, h] with w hw hw'
    rw [hw, norm_zero, mul_zero] at hw'
    exact norm_eq_zero.1 hw'
  by_cases hft : analyticOrderAt f t = ⊤
  · rw [hft, eq_comm, analyticOrderAt_eq_top]
    filter_upwards [analyticOrderAt_eq_top.1 hft, h, hcev] with w hw hw' hc'
    rw [hw, norm_zero] at hw'
    exact norm_eq_zero.1 ((mul_eq_zero.1 hw'.symm).resolve_left hc')
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hft
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hgt
  rw [← ha, ← hb]
  obtain ⟨f1, hf1, hf1t, hff⟩ := (hf.analyticOrderAt_eq_natCast).1 ha.symm
  obtain ⟨g1, hg1, hg1t, hgg⟩ := (hg.analyticOrderAt_eq_natCast).1 hb.symm
  have hrel : ∀ᶠ w in 𝓝 t, ‖w - t‖ ^ a * ‖f1 w‖ = c w * (‖w - t‖ ^ b * ‖g1 w‖) := by
    filter_upwards [h, hff, hgg] with w hw hfw hgw
    rw [hfw, hgw, norm_smul, norm_smul, norm_pow, norm_pow] at hw
    exact hw
  have hne : ∀ᶠ w in 𝓝[≠] t, ‖w - t‖ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    refine no_lower_order (p := fun w => ‖f1 w‖) (q := fun w => c w * ‖g1 w‖)
      hf1.continuousAt.norm (norm_ne_zero_iff.2 hf1t) (hc.mul hg1.continuousAt.norm)
      (k := b - a) (Nat.sub_pos_of_lt hab) ?_
    filter_upwards [nhdsWithin_le_nhds hrel, hne] with w hw hw0
    have : ‖w - t‖ ^ b = ‖w - t‖ ^ a * ‖w - t‖ ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this] at hw
    have hpa : ‖w - t‖ ^ a ≠ 0 := pow_ne_zero _ hw0
    apply mul_left_cancel₀ hpa
    rw [hw]; ring
  · rw [hab]
  · exfalso
    refine no_lower_order (p := fun w => c w * ‖g1 w‖) (q := fun w => ‖f1 w‖)
      (hc.mul hg1.continuousAt.norm) (mul_ne_zero hct (norm_ne_zero_iff.2 hg1t))
      hf1.continuousAt.norm (k := a - b) (Nat.sub_pos_of_lt hab) ?_
    filter_upwards [nhdsWithin_le_nhds hrel, hne] with w hw hw0
    have : ‖w - t‖ ^ a = ‖w - t‖ ^ b * ‖w - t‖ ^ (a - b) := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this] at hw
    have hpa : ‖w - t‖ ^ b ≠ 0 := pow_ne_zero _ hw0
    apply mul_left_cancel₀ hpa
    rw [← mul_assoc, mul_comm (‖w - t‖ ^ b), mul_assoc, ← hw]; ring

/-- Orders are constant along `Γ`-orbits (norm automorphy suffices). -/
theorem ord_smul_eq {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {w | 0 < w.im})
    {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (haut : ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) (t : UpperHalfPlane) :
    analyticOrderAt F ((γ • t : UpperHalfPlane) : ℂ) = analyticOrderAt F t := by
  have ht := t.im_pos
  have hd : deriv (mob γ) t ≠ 0 := by
    rw [(hasDerivAt_mob γ ht).deriv]
    exact div_ne_zero (by exact_mod_cast hγ.ne') (pow_ne_zero _ (denom_ne ht))
  rw [coe_smul_eq_mob hγ, ← analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_mob γ ht) hd]
  have hmobt : 0 < (mob γ t).im := mob_im_pos hγ ht
  refine ord_eq_of_norm ((hF _ hmobt).comp (analyticAt_mob γ ht)) (hF _ ht)
    (c := fun w => ‖UpperHalfPlane.denom γ w‖ ^ (2 * m) / (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m)
    ?_ ?_ ?_
  · refine ContinuousAt.div_const ?_ _
    unfold UpperHalfPlane.denom
    fun_prop
  · exact div_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (denom_ne ht))) (pow_ne_zero _ hγ.ne')
  · have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 (t : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds ht
    filter_upwards [hU] with w hw
    have := haut ⟨w, hw⟩
    rw [coe_smul_eq_mob hγ] at this
    simp only [Function.comp_apply]
    have hdp : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m := pow_pos hγ m
    field_simp
    exact this

end ValenceCocompact

/-! ### Part B7 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- Zeros of a nonzero analytic function in a compact subset of a preconnected open set are finite. -/
theorem zeros_finite {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {w | w ∈ K ∧ F w = 0}.Finite := by
  have hcl : IsClosed {w | w ∈ K ∧ F w = 0} :=
    (hF.continuousOn.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  refine (hK.of_isClosed_subset hcl fun w hw => hw.1).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [zeros_isolated hU hF hne (hKU hx.1)] with w hw h
  exact hw h.2

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

theorem stabilizer_finite (t : UpperHalfPlane) :
    Finite (MulAction.stabilizer (permG (subG hΓ)) t) := by
  have h := finite_meet hΓ (isCompact_singleton (x := t))
  refine Set.Finite.to_subtype (h.subset ?_)
  intro g hg
  exact ⟨t, ⟨t, rfl, MulAction.mem_stabilizer_iff.1 hg⟩, rfl⟩

include hΓ in
theorem ellOrder_pos (t : UpperHalfPlane) : 0 < ellOrderOf Γ t := by
  rw [← card_stabilizer hΓ t]
  have := stabilizer_finite hΓ t
  exact Nat.card_pos

/-- **Orbit counting**: the points of the orbit of `t` where `χ ≠ 0`, weighted by `e_t`, sum to `1`. -/
theorem orbit_sum {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (t : UpperHalfPlane) :
    ∃ O : Finset ℂ, (∀ w ∈ O, χ w ≠ 0 ∧ ∃ g : permG (subG hΓ), ((g • t : UpperHalfPlane) : ℂ) = w) ∧
      (∀ g : permG (subG hΓ), χ ((g • t : UpperHalfPlane) : ℂ) ≠ 0 →
        ((g • t : UpperHalfPlane) : ℂ) ∈ O) ∧
      (ellOrderOf Γ t : ℝ) * ∑ w ∈ O, χ w = 1 := by
  classical
  set St := (support_finite hΓ hχc hχU t).toFinset
  set π : permG (subG hΓ) → ℂ := fun g => ((g • t : UpperHalfPlane) : ℂ)
  refine ⟨St.image π, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨(Set.Finite.mem_toFinset _).1 hg, g, rfl⟩
  · intro g hg
    exact Finset.mem_image_of_mem π ((Set.Finite.mem_toFinset _).2 hg)
  · have h1 : ∑ g ∈ St, χ (π g) = 1 := by
      rw [← hsum t]
      exact (finsum_eq_sum_of_support_subset _ fun g hg => (Set.Finite.mem_toFinset _).2 hg).symm
    rw [← Finset.sum_fiberwise_of_maps_to' (t := St.image π) (fun g hg => Finset.mem_image_of_mem π hg)
      χ] at h1
    rw [Finset.mul_sum, ← h1]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.1 hw
    have hg0' : χ (π g0) ≠ 0 := (Set.Finite.mem_toFinset _).1 hg0
    rw [← card_stabilizer hΓ t]
    norm_cast
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.symm
      { toFun := fun x => ⟨g0⁻¹ * x.1, by
          have hx := (Finset.mem_filter.1 x.2).2
          have e : x.1 • t = g0 • t := UpperHalfPlane.ext hx
          rw [MulAction.mem_stabilizer_iff, mul_smul, e, inv_smul_smul]⟩
        invFun := fun h => ⟨g0 * h.1, by
          have e : (g0 * h.1) • t = g0 • t := by
            rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]
          have e' : π (g0 * h.1) = π g0 := by simp only [π, e]
          refine Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ?_, e'⟩
          show χ (π (g0 * h.1)) ≠ 0
          rw [e']; exact hg0'⟩
        left_inv := fun x => by simp
        right_inv := fun h => by simp }

/-- The weighted orbit sum is bounded by the total zero count (equality when `T` covers the zeros). -/
theorem orbit_count {m : ℕ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {w | 0 < w.im}) (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖)
    {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w)) :
    ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) ≤
        ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w ∧
      (Covers Γ T F → ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
        ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w) := by
  classical
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  choose O hO1 hO2 hO3 using orbit_sum hΓ hχc hχU hsum
  set B := T.biUnion O
  set f : ℂ → ℝ := fun w => ((analyticOrderAt F w).toNat : ℝ) * χ w
  -- orders along orbits
  have hordg : ∀ (g : permG (subG hΓ)) (t : UpperHalfPlane),
      analyticOrderAt F ((g • t : UpperHalfPlane) : ℂ) = analyticOrderAt F t := by
    intro g t
    rw [rep_smul]
    exact ord_smul_eq hF (rep_det hΓ g) (haut _ (rep_memΓ hΓ g)) t
  have hterm : ∀ t : UpperHalfPlane, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
      ∑ w ∈ O t, f w := by
    intro t
    have he : (0 : ℝ) < ellOrderOf Γ t := by exact_mod_cast ellOrder_pos hΓ t
    have hsumO : ∑ w ∈ O t, χ w = 1 / (ellOrderOf Γ t : ℝ) := by
      rw [eq_div_iff he.ne', mul_comm]; exact hO3 t
    have : ∑ w ∈ O t, f w = ((analyticOrderAt F (t : ℂ)).toNat : ℝ) * ∑ w ∈ O t, χ w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨-, g, rfl⟩ := hO1 t w hw
      simp only [f, hordg]
    rw [this, hsumO]; ring
  have hdisj : (T : Set UpperHalfPlane).PairwiseDisjoint O := by
    intro t ht t' ht' hne'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨-, g, rfl⟩ := hO1 t w hw
    obtain ⟨-, g', hg'⟩ := hO1 t' _ hw'
    have e : (g'⁻¹ * g) • t = t' := by
      rw [mul_smul, UpperHalfPlane.ext hg'.symm, inv_smul_smul]
    rw [rep_smul] at e
    exact hT ht ht' hne' _ (rep_memΓ hΓ _) e
  have hsumT : ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
      ∑ w ∈ B, f w := by
    rw [Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun t _ => hterm t
  -- finiteness of the support
  have hZ : (Function.support f).Finite := by
    refine (zeros_finite hUc hF hne hχc hχU).subset ?_
    intro w hw
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero, not_or] at hw
    refine ⟨subset_tsupport _ hw.2, ?_⟩
    by_contra h
    apply hw.1
    rw [analyticOrderAt_eq_zero.2 (Or.inr h)]; simp
  have hf0 : ∀ w, 0 ≤ f w := fun w => mul_nonneg (Nat.cast_nonneg _) (hχ0 w)
  refine ⟨?_, fun hc => ?_⟩
  · rw [hsumT, finsum_eq_sum_of_support_subset f (s := B ∪ hZ.toFinset) (by
      intro w hw; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hw)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun w _ _ => hf0 w)
  · rw [hsumT, finsum_eq_sum_of_support_subset f (s := B) ?_]
    intro w hw
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero, not_or] at hw
    have hwU : 0 < w.im := hχU (subset_tsupport _ hw.2)
    have hFw : F w = 0 := by
      by_contra h
      apply hw.1
      rw [analyticOrderAt_eq_zero.2 (Or.inr h)]; simp
    obtain ⟨t, ht, γ, hγ, e⟩ := hc ⟨w, hwU⟩ hFw
    have hg : ((⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ : permG (subG hΓ)) • t : UpperHalfPlane) =
        ⟨w, hwU⟩ := e
    have := hO2 t ⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ (by rw [hg]; exact hw.2)
    rw [hg] at this
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, B]
    exact ⟨t, ht, this⟩

end ValenceCocompact

/-! ### Part B8 -/
open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal


namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

include hΓ in
/-- The zeros lie in finitely many orbits: a finite set of pairwise inequivalent representatives. -/
theorem exists_reps {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {w | 0 < w.im})
    (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) :
    ∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) ∧
      Covers Γ T F := by
  classical
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨C, hC, hcov⟩ := hΓ.cocompact
  have hC' : IsCompact (((↑) : UpperHalfPlane → ℂ) '' C) := hC.image UpperHalfPlane.continuous_coe
  have hCU : ((↑) : UpperHalfPlane → ℂ) '' C ⊆ {w | 0 < w.im} := by
    rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  have hZfin : {z : UpperHalfPlane | z ∈ C ∧ F z = 0}.Finite := by
    refine Set.Finite.of_finite_image ((zeros_finite hUc hF hne hC' hCU).subset ?_)
      UpperHalfPlane.coe_injective.injOn
    rintro _ ⟨z, ⟨hz, hFz⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, hFz⟩
  set Zc := hZfin.toFinset
  let R : UpperHalfPlane → UpperHalfPlane → Prop := fun a b => ∃ γ ∈ Γ, γ • a = b
  have Rrefl : ∀ a, R a a := fun a => ⟨1, hΓ.one_mem, one_smul _ a⟩
  have Rsymm : ∀ a b, R a b → R b a := by
    rintro a b ⟨γ, hγ, rfl⟩; exact ⟨γ⁻¹, hΓ.inv_mem _ hγ, inv_smul_smul γ a⟩
  have Rtrans : ∀ a b c, R a b → R b c → R a c := by
    rintro a b c ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
    exact ⟨δ * γ, hΓ.mul_mem _ hδ _ hγ, mul_smul δ γ a⟩
  let r : UpperHalfPlane → UpperHalfPlane := fun z => Classical.epsilon fun w => w ∈ Zc ∧ R w z
  have hr : ∀ z ∈ Zc, r z ∈ Zc ∧ R (r z) z := fun z hz =>
    Classical.epsilon_spec (p := fun w => w ∈ Zc ∧ R w z) ⟨z, hz, Rrefl z⟩
  have hr_eq : ∀ z z', R z z' → r z = r z' := by
    intro z z' h
    have : (fun w => w ∈ Zc ∧ R w z) = fun w => w ∈ Zc ∧ R w z' := by
      funext w
      apply propext
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, Rtrans _ _ _ h2 h⟩,
        fun ⟨h1, h2⟩ => ⟨h1, Rtrans _ _ _ h2 (Rsymm _ _ h)⟩⟩
    simp only [r, this]
  refine ⟨Zc.image r, ?_, ?_⟩
  · intro a ha b hb hab γ hγ e
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨z, hz, rfl⟩ := ha
    obtain ⟨z', hz', rfl⟩ := hb
    apply hab
    apply hr_eq
    exact Rtrans _ _ _ (Rsymm _ _ (hr z hz).2) (Rtrans _ _ _ ⟨γ, hγ, e⟩ (hr z' hz').2)
  · intro x hx
    obtain ⟨γ, hγ, hxC⟩ := hcov x
    have hFγ : F ((γ • x : UpperHalfPlane) : ℂ) = 0 := by
      have := haut γ hγ x
      rw [hx, norm_zero, mul_zero] at this
      have hd : (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m ≠ 0 := pow_ne_zero _ (hΓ.det_pos γ hγ).ne'
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
    have hz : γ • x ∈ Zc := (Set.Finite.mem_toFinset _).2 ⟨hxC, hFγ⟩
    refine ⟨r (γ • x), Finset.mem_image_of_mem r hz, ?_⟩
    have h1 : R (r (γ • x)) x := Rtrans _ _ _ (hr _ hz).2 (Rsymm _ _ ⟨γ, hγ, rfl⟩)
    exact h1

theorem enn_term {o : ℕ∞} (ho : o ≠ ⊤) {e : ℕ} (he : 0 < e) :
    ((o : ℕ∞) : ℝ≥0∞) / (e : ℝ≥0∞) = ENNReal.ofReal ((o.toNat : ℝ) / e) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast he)]
  conv_lhs => rw [← ENat.natCast_toNat ho]
  simp

theorem enn_rhs (m : ℕ) {v : ℝ≥0∞} (hv : v ≠ ⊤) :
    (2 * m : ℝ≥0∞) * v / ENNReal.ofReal (4 * Real.pi) =
      ENNReal.ofReal (2 * m * v.toReal / (4 * Real.pi)) := by
  have h1 : ENNReal.ofReal (2 * m * v.toReal) = 2 * m * v := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_div_of_pos (by positivity), h1]

/-- **The valence formula for a cocompact Fuchsian group** (Shimura 1971, Prop. 2.16 and Thm. 2.20),
in the equality form of the single proof. -/
theorem valenceFormulaCocompactEq_proof : HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq := by
  intro Γ hΓ s hs m F hF hne haut
  have hF' : AnalyticOnNhd ℂ F {w | 0 < w.im} := hF
  have hne' : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0 := hne
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨χ, hχ, hχc, hχU, hχ0, hsum⟩ := exists_partition hΓ
  obtain ⟨hfin, hid⟩ := main_identity hΓ hs hF' hne' haut hχ hχc hχU hχ0 hsum
  have hval : ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w =
      2 * m * (volume s).toReal / (4 * Real.pi) := by
    field_simp
    linarith
  have hconv : ∀ T : Finset UpperHalfPlane,
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) =
        ENNReal.ofReal (∑ z ∈ T, ((analyticOrderAt F (z : ℂ)).toNat : ℝ) / (ellOrderOf Γ z : ℝ)) := by
    intro T
    rw [ENNReal.ofReal_sum_of_nonneg (fun z _ => by positivity)]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact enn_term (order_ne_top hUc hF' hne' z.im_pos) (ellOrder_pos hΓ z)
  refine ⟨exists_reps hΓ hF' hne' haut, fun T hT hc => ?_, fun T hT => ?_⟩
  · rw [hconv, enn_rhs m hfin, ← hval, ((orbit_count hΓ hF' hne' haut hχc hχU hχ0 hsum T hT).2 hc)]
  · rw [hconv, enn_rhs m hfin, ← hval]
    exact ENNReal.ofReal_le_ofReal (orbit_count hΓ hF' hne' haut hχc hχU hχ0 hsum T hT).1

end ValenceCocompact

