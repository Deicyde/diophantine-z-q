/-! ## period-glue: `SphereFactorAffine` (generic complex analysis, Mathlib only)

Task period-glue, 2026-11-13. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Filter Topology Set

/-- **Descent of holomorphy along a non-locally-constant analytic map (proved).** Let `F, H` be
analytic on an open `O ⊆ ℂ`, `F` nowhere locally constant on `O`, and `G (F z) = H z` on `O`.
Then `F '' O` is open and `G` is complex differentiable on it. Proof: `F` is locally open
(open mapping), so `G` is continuous on `F '' O`; off the countable set `F '' {F' = 0}` the
inverse function theorem writes `G = H ∘ F⁻¹` locally; a function continuous on a disc and
differentiable off a countable set is analytic (`hasFPowerSeriesOnBall_of_differentiable_off_countable`). -/
theorem descent {O : Set ℂ} (hO : IsOpen O) {F H G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F O) (hH : AnalyticOnNhd ℂ H O)
    (hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, F w = F z) (hGF : ∀ z ∈ O, G (F z) = H z) :
    IsOpen (F '' O) ∧ DifferentiableOn ℂ G (F '' O) := by
  have hloc : ∀ z ∈ O, 𝓝 (F z) ≤ map F (𝓝 z) := fun z hz =>
    (hF z hz).eventually_constant_or_nhds_le_map_nhds.resolve_left (hnc z hz)
  have hopen : IsOpen (F '' O) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hloc z hz (image_mem_map (hO.mem_nhds hz))
  refine ⟨hopen, ?_⟩
  -- continuity of `G` on `F '' O`
  have hcont : ∀ z ∈ O, ContinuousAt G (F z) := by
    intro z hz
    have h1 : Tendsto (G ∘ F) (𝓝 z) (𝓝 (H z)) := by
      refine ((hH z hz).continuousAt.tendsto).congr' ?_
      filter_upwards [hO.mem_nhds hz] with w hw using (hGF w hw).symm
    have h2 : Tendsto G (map F (𝓝 z)) (𝓝 (H z)) := h1
    rw [ContinuousAt, hGF z hz]
    exact h2.mono_left (hloc z hz)
  -- the critical set is countable
  set Crit : Set ℂ := {z | z ∈ O ∧ deriv F z = 0} with hCrit
  have hdisc : DiscreteTopology Crit := by
    rw [discreteTopology_subtype_iff]
    intro z ⟨hzO, hz0⟩
    rw [inf_principal_eq_bot]
    rcases ((hF z hzO).deriv).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hnc z hzO
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h (hO.mem_nhds hzO))
      have hdiff : DifferentiableOn ℂ F (Metric.ball z r) := fun w hw =>
        ((hF w (hball hw).2).differentiableAt).differentiableWithinAt
      filter_upwards [Metric.ball_mem_nhds z hr] with w hw
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected hdiff
        (fun v hv => (hball hv).1) hw (Metric.mem_ball_self hr)
    · filter_upwards [h] with w hw
      exact fun hc => hw hc.2
  have hcount : Crit.Countable :=
    (HereditarilyLindelofSpace.isLindelof Crit).countable hdisc
  -- differentiability off `F '' Crit`
  have hdiffAt : ∀ z ∈ O, deriv F z ≠ 0 → DifferentiableAt ℂ G (F z) := by
    intro z hz hne
    have hs := (hF z hz).hasStrictDerivAt
    set L := hs.localInverse F (deriv F z) z hne with hL
    have hLc : HasStrictDerivAt L (deriv F z)⁻¹ (F z) := hs.to_localInverse hne
    have hLz : L (F z) = z := (hs.eventually_left_inverse hne).self_of_nhds
    have hLt : Tendsto L (𝓝 (F z)) (𝓝 z) := by
      have := hLc.hasDerivAt.continuousAt.tendsto
      rwa [hLz] at this
    have hHL : DifferentiableAt ℂ (H ∘ L) (F z) := by
      refine DifferentiableAt.comp (F z) ?_ hLc.hasDerivAt.differentiableAt
      rw [hLz]; exact (hH z hz).differentiableAt
    refine hHL.congr_of_eventuallyEq ?_
    filter_upwards [hs.eventually_right_inverse hne, hLt (hO.mem_nhds hz)] with w hw hwO
    rw [Function.comp_apply, ← hGF _ hwO, hw]
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c hc
  set R : NNReal := ⟨ε / 2, by positivity⟩ with hR
  have hRε : (R : ℝ) < ε := show ε / 2 < ε by linarith
  have hsub : Metric.closedBall c R ⊆ F '' O := (Metric.closedBall_subset_ball hRε).trans hball
  have hps := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable (R := R) (c := c) (hcount.image F)
    (fun w hw => by
      obtain ⟨z, hz, rfl⟩ := hsub hw
      exact (hcont z hz).continuousWithinAt)
    (fun w ⟨hw, hwc⟩ => by
      obtain ⟨z, hz, rfl⟩ := hsub (Metric.ball_subset_closedBall hw)
      exact hdiffAt z hz fun h0 => hwc ⟨z, ⟨hz, h0⟩, rfl⟩)
    (NNReal.coe_pos.mp (show (0:ℝ) < ε / 2 by linarith))
  exact hps.analyticAt.differentiableAt.differentiableWithinAt

/-- **An injective analytic map has non-zero derivative (proved).** Via `descent` applied to the
inverse `g⁻¹ ∘ g = id` and the chain rule. -/
theorem deriv_ne_zero_of_injOn {g : ℂ → ℂ} {a : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 a)
    (hg : AnalyticOnNhd ℂ g U) (hinj : InjOn g U) : deriv g a ≠ 0 := by
  set O := interior U with hOdef
  have hO : IsOpen O := isOpen_interior
  have haO : a ∈ O := mem_interior_iff_mem_nhds.mpr hU
  have hOU : O ⊆ U := interior_subset
  set G := Function.invFunOn g O with hG
  have hGg : ∀ z ∈ O, G (g z) = z := fun z hz => (hinj.mono hOU).leftInvOn_invFunOn hz
  have hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, g w = g z := by
    intro z hz h
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ :=
      ((h.and (hO.mem_nhds hz)).filter_mono nhdsWithin_le_nhds |>.and
        self_mem_nhdsWithin).exists (f := 𝓝[≠] z)
    exact hw3 (hinj (hOU hw2) (hOU hz) hw1)
  obtain ⟨hopen, hdiff⟩ := descent hO (fun z hz => hg z (hOU hz)) analyticOnNhd_id hnc hGg
  have hGd : DifferentiableAt ℂ G (g a) :=
    (hdiff (g a) ⟨a, haO, rfl⟩).differentiableAt (hopen.mem_nhds ⟨a, haO, rfl⟩)
  have h1 : HasDerivAt (G ∘ g) (deriv G (g a) * deriv g a) a :=
    hGd.hasDerivAt.comp a (hg a (hOU haO)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (G ∘ g) 1 a := by
    refine (hasDerivAt_id a).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds haO] with z hz using hGg z hz
  intro h0
  have := h1.unique h2
  rw [h0, mul_zero] at this
  exact zero_ne_one this

/-- **Linear growth forces an entire function to be affine (proved; Liouville applied to
`dslope ψ 0`).** -/
theorem affine_of_growth {ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ) {C R : ℝ} (hR : 0 < R)
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → ‖ψ z‖ ≤ C * ‖z‖) : ∃ a b : ℂ, ∀ z, ψ z = a * z + b := by
  set k := dslope ψ 0 with hk
  have hkd : Differentiable ℂ k := by
    have := (differentiableOn_dslope (c := (0 : ℂ)) (s := univ) univ_mem).mpr hψ.differentiableOn
    simpa [differentiableOn_univ] using this
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hkd.continuous.continuousOn
  have hbd : Bornology.IsBounded (range k) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max M (C + ‖ψ 0‖ / R), ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ R
    · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      rw [hk, dslope_of_ne _ hz0, slope_def_field, sub_zero, norm_div]
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ hzpos]
      calc ‖ψ z - ψ 0‖ ≤ ‖ψ z‖ + ‖ψ 0‖ := norm_sub_le _ _
        _ ≤ C * ‖z‖ + ‖ψ 0‖ * (‖z‖ / R) := by
          gcongr
          · exact hb z hz.le
          · exact le_mul_of_one_le_right (norm_nonneg _) (by rw [le_div_iff₀ hR]; linarith)
        _ = (C + ‖ψ 0‖ / R) * ‖z‖ := by ring
  refine ⟨k 0, ψ 0, fun z => ?_⟩
  have h1 := sub_smul_dslope ψ 0 z
  rw [sub_zero, smul_eq_mul, ← hk, hkd.apply_eq_apply_of_bounded hbd z 0] at h1
  linear_combination -h1

end HSyn.G0Split.FibreQM.PeriodGlue

end
