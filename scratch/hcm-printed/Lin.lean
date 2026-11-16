import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! hcm-printed, glue LIN: a group homomorphism `ℂ/Λ' → ℂ/Λ''` whose Weierstrass coordinates are
holomorphic is `z ↦ αz`. Pure complex analysis over Mathlib's `PeriodPair`. -/

open Filter Topology Metric Set

noncomputable section

namespace HcmPrinted

section Lin

variable (P' P'' : PeriodPair)

theorem psi_nsmul (ψ₀ : ℂ → ℂ) (h0 : ψ₀ 0 ∈ P''.lattice)
    (hadd : ∀ z w, ψ₀ (z + w) - ψ₀ z - ψ₀ w ∈ P''.lattice) :
    ∀ (n : ℕ) (v : ℂ), ψ₀ (n * v) - n * ψ₀ v ∈ P''.lattice := by
  intro n v
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have e : ψ₀ (((n + 1 : ℕ) : ℂ) * v) - ((n + 1 : ℕ) : ℂ) * ψ₀ v =
        (ψ₀ (n * v + v) - ψ₀ (n * v) - ψ₀ v) + (ψ₀ (n * v) - n * ψ₀ v) := by
      push_cast; ring_nf
    rw [e]
    exact add_mem (hadd _ _) ih

theorem third_not_mem : P''.ω₁ / 3 ∉ P''.lattice := by
  intro h
  have : ((1 / 3 : ℚ) : ℂ) * P''.ω₁ + ((0 : ℚ) : ℂ) * P''.ω₂ ∈ P''.lattice := by
    convert h using 1; push_cast; ring
  rw [PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at this
  exact absurd this.1 (by norm_num)

theorem two_third_not_mem : P''.ω₁ / 3 - -(P''.ω₁ / 3) ∉ P''.lattice := by
  intro h
  have : ((2 / 3 : ℚ) : ℂ) * P''.ω₁ + ((0 : ℚ) : ℂ) * P''.ω₂ ∈ P''.lattice := by
    convert h using 1; push_cast; ring
  rw [PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at this
  exact absurd this.1 (by norm_num)

theorem neg_not_mem {w : ℂ} (hw : w ∉ P''.lattice) : -w ∉ P''.lattice := fun h =>
  hw (by simpa using neg_mem h)

theorem isOpen_compl_lattice (P : PeriodPair) : IsOpen ((P.lattice : Set ℂ)ᶜ) :=
  P.isClosed_lattice.isOpen_compl

/-- **LIN.** Let `ψ₀ : ℂ → ℂ` induce an injective, surjective homomorphism `ℂ/Λ' → ℂ/Λ''` whose
Weierstrass coordinates `(℘_{Λ''}(ψ₀ z), ℘'_{Λ''}(ψ₀ z)) = (F z, G z)` are holomorphic (resp.
continuous) off `Λ'`, where `(℘_{Λ''}, ℘'_{Λ''})` is injective on `(ℂ/Λ'') ∖ 0`. Then
`ψ₀ z ≡ αz (mod Λ'')` for a constant `α`. -/
theorem lin (ψ₀ F G : ℂ → ℂ)
    (hinj : ∀ a b, a ∉ P''.lattice → b ∉ P''.lattice → P''.weierstrassP a = P''.weierstrassP b →
      P''.derivWeierstrassP a = P''.derivWeierstrassP b → a - b ∈ P''.lattice)
    (hadd : ∀ z w, ψ₀ (z + w) - ψ₀ z - ψ₀ w ∈ P''.lattice)
    (hker : ∀ z, ψ₀ z ∈ P''.lattice ↔ z ∈ P'.lattice)
    (hsurj : ∀ a, ∃ z, ψ₀ z - a ∈ P''.lattice)
    (hF : ∀ z, z ∉ P'.lattice → P''.weierstrassP (ψ₀ z) = F z ∧ P''.derivWeierstrassP (ψ₀ z) = G z)
    (hFd : DifferentiableOn ℂ F (P'.lattice : Set ℂ)ᶜ) (hGc : ContinuousOn G (P'.lattice : Set ℂ)ᶜ) :
    ∃ α : ℂ, ∀ z, ψ₀ z - α * z ∈ P''.lattice := by
  set L := P''.lattice with hL
  set p := P''.weierstrassP with hp
  set dp := P''.derivWeierstrassP with hdp
  have hLo : IsOpen ((L : Set ℂ)ᶜ) := isOpen_compl_lattice P''
  have hL'o : IsOpen ((P'.lattice : Set ℂ)ᶜ) := isOpen_compl_lattice P'
  have hmem : ∀ z, z ∉ P'.lattice → (P'.lattice : Set ℂ)ᶜ ∈ 𝓝 z := fun z hz => hL'o.mem_nhds hz
  -- step a: a point with `℘' ≠ 0`
  set a₀ := P''.ω₁ / 3 with ha₀
  have ha₀L : a₀ ∉ L := third_not_mem P''
  have hda₀ : dp a₀ ≠ 0 := by
    intro h0
    refine two_third_not_mem P'' (hinj a₀ (-a₀) ha₀L (neg_not_mem P'' ha₀L) ?_ ?_)
    · rw [hp, PeriodPair.weierstrassP_neg]
    · rw [hdp, PeriodPair.derivWeierstrassP_neg, ← hdp, h0, neg_zero]
  -- step b: `z₀` with `ψ₀ z₀ ≡ a₀`
  obtain ⟨z₀, hz₀⟩ := hsurj a₀
  set w₀ := ψ₀ z₀ with hw₀
  have hw₀L : w₀ ∉ L := fun h => ha₀L (by simpa using sub_mem h hz₀)
  have hz₀L : z₀ ∉ P'.lattice := fun h => hw₀L ((hker z₀).2 h)
  have hdw₀ : dp w₀ ≠ 0 := by
    have : w₀ = a₀ + ((⟨w₀ - a₀, hz₀⟩ : L) : ℂ) := by simp
    rw [this, hdp, PeriodPair.derivWeierstrassP_add_coe]; exact hda₀
  -- step c: the local inverse of `℘` at `w₀`
  have hdiffp : ∀ w ∉ L, HasStrictDerivAt p (dp w) w := by
    intro w hw
    have h := (P''.analyticOnNhd_weierstrassP w hw).hasStrictDerivAt
    rwa [PeriodPair.deriv_weierstrassP] at h
  have hs := hdiffp w₀ hw₀L
  set φ := (hs.hasStrictFDerivAt_equiv hdw₀).toOpenPartialHomeomorph p with hφ
  have hφc : ∀ w, φ w = p w := fun w => rfl
  have hw₀s : w₀ ∈ φ.source := (hs.hasStrictFDerivAt_equiv hdw₀).mem_toOpenPartialHomeomorph_source
  have hpw₀t : p w₀ ∈ φ.target := (hs.hasStrictFDerivAt_equiv hdw₀).image_mem_toOpenPartialHomeomorph_target
  set ψ : ℂ → ℂ := fun z => φ.symm (F z) with hψ
  have hFz₀ : F z₀ = p w₀ := ((hF z₀ hz₀L).1).symm
  have hGz₀ : G z₀ = dp w₀ := ((hF z₀ hz₀L).2).symm
  have hψz₀ : ψ z₀ = w₀ := by
    simp only [hψ, hFz₀]
    rw [← hφc w₀]; exact φ.left_inv hw₀s
  have hFc : ContinuousAt F z₀ := (hFd.differentiableAt (hmem z₀ hz₀L)).continuousAt
  have hψc : ContinuousAt ψ z₀ := by
    refine (φ.symm.continuousAt ?_).comp hFc
    rw [hFz₀]; exact hpw₀t
  -- the good set near `w₀`
  set Good : Set ℂ := {w | w ∉ L ∧ dp w ≠ 0} with hGood
  have hGoodo : IsOpen Good := by
    have hc : ContinuousOn dp ((L : Set ℂ)ᶜ) :=
      fun w hw => (P''.analyticOnNhd_derivWeierstrassP w hw).continuousAt.continuousWithinAt
    exact hc.isOpen_inter_preimage hLo isOpen_compl_singleton
  have hw₀G : w₀ ∈ Good := ⟨hw₀L, hdw₀⟩
  have hdpc : ContinuousAt dp w₀ := (P''.analyticOnNhd_derivWeierstrassP w₀ hw₀L).continuousAt
  have hGc0 : ContinuousAt G z₀ := hGc.continuousAt (hmem z₀ hz₀L)
  have hsum : ContinuousAt (fun z => dp (ψ z) + G z) z₀ := by
    refine ContinuousAt.add ?_ hGc0
    refine ContinuousAt.comp (g := dp) ?_ hψc
    rw [hψz₀]; exact hdpc
  have hsum0 : dp (ψ z₀) + G z₀ ≠ 0 := by
    rw [hψz₀, hGz₀, ← two_mul]; exact mul_ne_zero two_ne_zero hdw₀
  -- eventually near `z₀`
  have hev : ∀ᶠ z in 𝓝 z₀, z ∉ P'.lattice ∧ F z ∈ φ.target ∧ ψ z ∈ Good ∧
      dp (ψ z) + G z ≠ 0 := by
    have e1 : ∀ᶠ z in 𝓝 z₀, z ∉ P'.lattice := hmem z₀ hz₀L
    have e2 : ∀ᶠ z in 𝓝 z₀, F z ∈ φ.target :=
      hFc.preimage_mem_nhds (by rw [hFz₀]; exact φ.open_target.mem_nhds hpw₀t)
    have e3 : ∀ᶠ z in 𝓝 z₀, ψ z ∈ Good :=
      hψc.preimage_mem_nhds (by rw [hψz₀]; exact hGoodo.mem_nhds hw₀G)
    have e4 : ∀ᶠ z in 𝓝 z₀, dp (ψ z) + G z ≠ 0 :=
      hsum.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hsum0)
    exact e1.and (e2.and (e3.and e4))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- on the ball: `ψ₀ ≡ ψ`, `ψ` holomorphic
  have hkey : ∀ z ∈ ball z₀ r, ψ₀ z - ψ z ∈ L ∧ HasDerivAt ψ (deriv ψ z) z ∧ ContinuousAt ψ z := by
    intro z hz
    obtain ⟨hzL, hFt, ⟨hψL, hdψ⟩, hne⟩ := hball z hz
    have hpψ : p (ψ z) = F z := φ.right_inv hFt
    obtain ⟨h1, h2⟩ := hF z hzL
    have hψ₀L : ψ₀ z ∉ L := fun h => hzL ((hker z).1 h)
    have hsq1 := P''.derivWeierstrassP_sq (ψ z) hψL
    have hsq2 := P''.derivWeierstrassP_sq (ψ₀ z) hψ₀L
    have hsq : (dp (ψ z) - G z) * (dp (ψ z) + G z) = 0 := by
      have e1 : dp (ψ z) ^ 2 = 4 * F z ^ 3 - P''.g₂ * F z - P''.g₃ := by rw [← hpψ]; exact hsq1
      have e2 : G z ^ 2 = 4 * F z ^ 3 - P''.g₂ * F z - P''.g₃ := by rw [← h1, ← h2]; exact hsq2
      linear_combination e1 - e2
    have hdeq : dp (ψ z) = G z := sub_eq_zero.1 ((mul_eq_zero.1 hsq).resolve_right hne)
    refine ⟨hinj _ _ hψ₀L hψL (by rw [h1, hpψ]) (by rw [h2, hdeq]), ?_, ?_⟩
    · have hFd' : HasDerivAt F (deriv F z) z :=
        (hFd.differentiableAt (hmem z hzL)).hasDerivAt
      have hsy : HasDerivAt φ.symm (dp (ψ z))⁻¹ (F z) := by
        refine φ.hasDerivAt_symm hFt hdψ ?_
        exact (hdiffp _ hψL).hasDerivAt
      exact ((hsy.comp z hFd').differentiableAt).hasDerivAt
    · exact (φ.symm.continuousAt hFt).comp
        (hFd.differentiableAt (hmem z hzL)).continuousAt
  -- local increments agree: for `z₁` near `z₀`, `ψ (z₁ + u) - ψ z₁ = ψ (z₀ + u) - ψ z₀`
  have hr2 : (0 : ℝ) < r / 2 := half_pos hr
  have hinc : ∀ z₁ ∈ ball z₀ (r / 2), ∀ u ∈ ball (0 : ℂ) (r / 2),
      ψ (z₁ + u) - ψ z₁ - (ψ (z₀ + u) - ψ z₀) = 0 := by
    intro z₁ hz₁ u hu
    have mem : ∀ {z₂ v : ℂ}, z₂ ∈ ball z₀ (r / 2) → v ∈ ball (0 : ℂ) (r / 2) → z₂ + v ∈ ball z₀ r := by
      intro z₂ v h1 h2
      rw [mem_ball] at h1 h2 ⊢
      rw [dist_zero_right] at h2
      calc dist (z₂ + v) z₀ ≤ dist z₂ z₀ + ‖v‖ := by
            rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add h1 h2
        _ = r := by ring
    have hz₀b : z₀ ∈ ball z₀ (r / 2) := mem_ball_self hr2
    let D : ℂ → ℂ := fun v => ψ (z₁ + v) - ψ z₁ - (ψ (z₀ + v) - ψ z₀)
    have hDL : MapsTo D (ball (0 : ℂ) (r / 2)) (L : Set ℂ) := by
      intro v hv
      have e : D v = (ψ₀ (z₀ + v) - ψ (z₀ + v)) - (ψ₀ (z₁ + v) - ψ (z₁ + v)) + (ψ₀ z₁ - ψ z₁)
          - (ψ₀ z₀ - ψ z₀) + (ψ₀ (z₁ + v) - ψ₀ z₁ - ψ₀ v) - (ψ₀ (z₀ + v) - ψ₀ z₀ - ψ₀ v) := by
        simp only [D]; ring
      rw [SetLike.mem_coe, show D v = _ from e]
      refine sub_mem (add_mem (sub_mem (add_mem (sub_mem ?_ ?_) ?_) ?_) (hadd _ _)) (hadd _ _)
      · exact (hkey _ (mem hz₀b hv)).1
      · exact (hkey _ (mem hz₁ hv)).1
      · exact (hkey _ (by simpa using mem hz₁ (mem_ball_self hr2))).1
      · exact (hkey _ (by simpa using mem hz₀b (mem_ball_self hr2))).1
    have hDc : ContinuousOn D (ball (0 : ℂ) (r / 2)) := by
      intro v hv
      refine ContinuousAt.continuousWithinAt ?_
      have c1 : ContinuousAt (fun v => ψ (z₁ + v)) v :=
        ((hkey _ (mem hz₁ hv)).2.2).comp (continuous_const.add continuous_id).continuousAt
      have c2 : ContinuousAt (fun v => ψ (z₀ + v)) v :=
        ((hkey _ (mem hz₀b hv)).2.2).comp (continuous_const.add continuous_id).continuousAt
      exact (c1.sub continuousAt_const).sub (c2.sub continuousAt_const)
    have hdisc : IsDiscrete (L : Set ℂ) := by
      rw [isDiscrete_iff_discreteTopology]; exact inferInstanceAs (DiscreteTopology L)
    have := (convex_ball (0 : ℂ) (r / 2)).isPreconnected.constant_of_mapsTo hdisc hDc hDL hu
      (mem_ball_self hr2)
    simpa [D] using this
  -- derivatives agree
  have hderiv : ∀ z₁ ∈ ball z₀ (r / 2), deriv ψ z₁ = deriv ψ z₀ := by
    intro z₁ hz₁
    have hz₁r : z₁ ∈ ball z₀ r := ball_subset_ball (half_le_self hr.le) hz₁
    have hz₀r : z₀ ∈ ball z₀ r := mem_ball_self hr
    have h1 : HasDerivAt (fun u => ψ (z₁ + u)) (deriv ψ z₁) 0 := by
      have := (hkey z₁ hz₁r).2.1
      rw [← add_zero z₁] at this
      simpa using this.comp_const_add z₁ 0
    have h0 : HasDerivAt (fun u => ψ (z₀ + u) - ψ z₀ + ψ z₁) (deriv ψ z₀) 0 := by
      have := (hkey z₀ hz₀r).2.1
      rw [← add_zero z₀] at this
      have h' := this.comp_const_add z₀ 0
      simpa using (h'.sub_const (ψ z₀)).add_const (ψ z₁)
    have heq : (fun u => ψ (z₁ + u)) =ᶠ[𝓝 0] (fun u => ψ (z₀ + u) - ψ z₀ + ψ z₁) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr2] with u hu
      have := hinc z₁ hz₁ u hu
      linear_combination this
    exact (h1.congr_of_eventuallyEq heq.symm).unique h0 |>.symm ▸ rfl
  -- `ψ` is affine near `z₀`
  set α := deriv ψ z₀ with hα
  have hdiffOn : DifferentiableOn ℂ ψ (ball z₀ (r / 2)) := fun z hz =>
    (hkey z (ball_subset_ball (half_le_self hr.le) hz)).2.1.differentiableAt.differentiableWithinAt
  obtain ⟨c, hc⟩ := (isOpen_ball (x := z₀) (ε := r / 2)).exists_eq_add_of_fderiv_eq
    (convex_ball _ _).isPreconnected hdiffOn
    ((differentiable_id.const_mul α).differentiableOn (s := ball z₀ (r / 2)))
    (fun z hz => by
      have h1 : HasDerivAt ψ α z := by
        rw [← hderiv z hz]
        exact (hkey z (ball_subset_ball (half_le_self hr.le) hz)).2.1
      rw [h1.hasFDerivAt.fderiv, ((hasDerivAt_id z).const_mul α).hasFDerivAt.fderiv]
      simp)
  -- small `u`: `ψ₀ u ≡ α u`
  have hsmall : ∀ u ∈ ball (0 : ℂ) (r / 2), ψ₀ u - α * u ∈ L := by
    intro u hu
    have hzu : z₀ + u ∈ ball z₀ (r / 2) := by
      rw [mem_ball, dist_eq_norm]; simpa using hu
    have e1 := hc hzu
    have e0 := hc (mem_ball_self hr2)
    simp only [id] at e1 e0
    have hψu : ψ (z₀ + u) - ψ z₀ = α * u := by rw [e1, e0]; ring
    have m1 := (hkey (z₀ + u) (ball_subset_ball (half_le_self hr.le) hzu)).1
    have m0 := (hkey z₀ (mem_ball_self hr)).1
    have e : ψ₀ u - α * u = (ψ₀ (z₀ + u) - ψ (z₀ + u)) - (ψ₀ z₀ - ψ z₀)
        - (ψ₀ (z₀ + u) - ψ₀ z₀ - ψ₀ u) := by rw [← hψu]; ring
    rw [e]
    exact sub_mem (sub_mem m1 m0) (hadd _ _)
  -- global
  have h0 : ψ₀ 0 ∈ L := (hker 0).2 (zero_mem _)
  refine ⟨α, fun z => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ / (r / 2))
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr2.le) hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set v := z / n with hv
  have hvb : v ∈ ball (0 : ℂ) (r / 2) := by
    rw [mem_ball, dist_zero_right, hv, norm_div, Complex.norm_natCast, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hr2, mul_comm] at hn
  have hz : z = n * v := by rw [hv]; field_simp
  have e : ψ₀ z - α * z = (ψ₀ (n * v) - n * ψ₀ v) + n * (ψ₀ v - α * v) := by rw [hz]; ring
  rw [e]
  refine add_mem (psi_nsmul P'' ψ₀ h0 hadd n v) ?_
  have := hsmall v hvb
  rw [← nsmul_eq_mul]
  exact L.nsmul_mem this n

end Lin

end HcmPrinted
#print axioms HcmPrinted.lin
