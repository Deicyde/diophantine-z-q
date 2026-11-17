import ZInQKernel.Contrib.OneProof.ThetaDirect.Glue

/-! # theta-direct (helper): each theta constant along `Ω(τ)` is analytic on `ℍ`

Lines 139-210 of origin/wip/theta-fold (8e3dbdea) `ZInQKernel/Contrib/OneProof/LinYangPrinted.lean` (its §3,
`thetaConst_omega_analyticAt`, itself a copy of the inner step of period-map's `thetaOmegaAnalytic_of`, TailJ),
verbatim except for the namespace (`HDec.ThetaDirect` in place of theta-fold's `…ThetaPt.LinYangPrinted`). -/

noncomputable section

namespace HDec.ThetaDirect

open Complex Matrix Filter Topology
open HSyn.G0Split.FibreQM.PeriodMap (U isOpen_U thTerm qf quad_lower differentiableAt_omega summable_gb2
  norm_thTerm_le omegaSiegel_proof)

/-- Each theta constant along `Ω` is analytic on `ℍ` (copy of the inner step of period-map's
`thetaOmegaAnalytic_of`, TailJ). -/
theorem thetaConst_omega_analyticAt {τ₀ : ℂ} (hτ₀ : τ₀ ∈ U) (m : PkgI1.Char2) :
    AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
  have hS := omegaSiegel_proof
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


end HDec.ThetaDirect
