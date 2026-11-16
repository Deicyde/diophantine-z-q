import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! hcm-g1 scratch: `T5Glue.ShimuraMainCM` from a g = 1 leaf (Shimura 1971 Thm 5.4). -/

noncomputable section

namespace HcmG1

open Complex

/-- `y² = x³ − (a/4)x − b/4`, Mathlib's form of `y² = 4x³ − ax − b` (`y ↦ 2y`). -/
def wc (a b : ℂ) : WeierstrassCurve ℂ := ⟨0, 0, 0, -a / 4, -b / 4⟩

open Classical in
/-- `z ↦ (℘(z), ℘'(z)/2) ∈ W(ℂ)` (the point at infinity for `z ∈ Λ`; also `0` if the affine
point is singular on `W`, which for `W = wc g₂ g₃` the leaf `WeierstrassParam` excludes). -/
def wPtW (P : PeriodPair) (W : WeierstrassCurve ℂ) (z : ℂ) : W.toAffine.Point :=
  if h : z ∉ P.lattice ∧ W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2)
  then .some _ _ h.2 else 0

/-- The Weierstrass parametrization `ℂ → E_Λ(ℂ)` of `E_Λ : y² = 4x³ − g₂x − g₃`, in Mathlib's
normal form `wc g₂ g₃`. -/
def wPt (P : PeriodPair) (z : ℂ) : (wc P.g₂ P.g₃).toAffine.Point := wPtW P (wc P.g₂ P.g₃) z

open Classical in
/-- The properties of the Weierstrass parametrization (the content of the leaf). -/
def ParamProps (P : PeriodPair) (W : WeierstrassCurve ℂ) : Prop :=
  (∀ z w, wPtW P W (z + w) = wPtW P W z + wPtW P W w) ∧
  (∀ z, wPtW P W z = 0 ↔ z ∈ P.lattice) ∧ Function.Surjective (wPtW P W)

/-! ## `σ` on points: `W(ℂ) → W^σ(ℂ)` -/

section MapPt

open WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F)
  (f : F →+* K)

/-- The group homomorphism `W(F) → W^f(K)` induced by a field homomorphism (Mathlib's `Point.map` is
stated for algebra maps; this is the same proof with `map_addX`, `map_addY`, `map_negY`). -/
def mapPt : W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.left hxy.right]
      exact (Point.add_of_Y_eq (congr_arg _ hxy.left)
        (by rw [hxy.right, ← WeierstrassCurve.Affine.map_negY])).symm
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        rintro ⟨e1, e2⟩
        exact hxy ⟨f.injective e1, f.injective (by rw [e2, WeierstrassCurve.Affine.map_negY])⟩
      rw [Point.add_some hxy]
      show _ = Point.some _ _ _ + Point.some _ _ _
      rw [Point.add_some hxy']
      simp only [Point.some.injEq]
      rw [WeierstrassCurve.Affine.map_slope, WeierstrassCurve.Affine.map_addX,
        WeierstrassCurve.Affine.map_addY]
      exact ⟨rfl, rfl⟩

theorem mapPt_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    mapPt W f (.some x y h) = .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

theorem mapPt_injective : Function.Injective (mapPt W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h (by simp [mapPt])
  · exact absurd h (by simp [mapPt])
  · simp only [mapPt_some, Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have := f.injective e1; subst this
    have := f.injective e2; subst this
    rfl

end MapPt

theorem map_wc (σ : ℂ →+* ℂ) (a b : ℂ) : (wc a b).map σ = wc (σ a) (σ b) := by
  simp only [wc, WeierstrassCurve.map]
  congr 1 <;> simp [map_neg, map_div₀, map_ofNat]

/-! ## The conjugate abelian variety `A^σ = A ×_{ℂ,σ} ℂ` and its points -/


/-! ## Glue LIN (verbatim from scratch/hcm-printed/Lin.lean) -/

section LinSec
open Filter Topology Metric Set
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
end LinSec

/-! ## The textbook leaves -/

/-- **LEAF (textbook) `WeierstrassUniformization`.** For `a, b ∈ ℂ` with `a³ − 27b² ≠ 0` there is
a lattice `L` with `g₂(L) = a`, `g₃(L) = b`. J. Silverman, *The Arithmetic of Elliptic Curves*
(GTM 106, 2nd ed., 2009), Thm VI.5.1 (UNVERIFIED number); J.-P. Serre, *A Course in Arithmetic*,
Ch. VII §3 (UNVERIFIED). Verbatim copy of gz-weil's `GrossZagierHeegner.WeierstrassUniformization`
(origin/wip/gz-weil, `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean`). -/
def WeierstrassUniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b

/-- **LEAF (textbook) `WeierstrassParam`** (the Weierstrass parametrization). For every lattice
`Λ`: `Δ(Λ) = g₂³ − 27g₃² ≠ 0`, and `z ↦ (℘(z), ℘'(z))` is a surjective group homomorphism
`ℂ → E_Λ(ℂ)`, `E_Λ : y² = 4x³ − g₂x − g₃`, with kernel `Λ` (the points written in Mathlib's normal
form `y² = x³ − (g₂/4)x − g₃/4`, i.e. `(℘(z), ℘'(z)/2)`, with Mathlib's group law on
`WeierstrassCurve.Affine.Point`). J. Silverman, *The Arithmetic of Elliptic Curves* (GTM 106,
2nd ed.), Prop. VI.3.6 (a) (`Δ ≠ 0`) and (b) (`ℂ/Λ → E(ℂ)`, `z ↦ [℘(z), ℘'(z), 1]`, is a complex
analytic isomorphism of complex Lie groups); S. Lang, *Elliptic functions*, Ch. 1 §3; Serre,
*A Course in Arithmetic*, Ch. VII §3.2 (numbers UNVERIFIED). Weaker than the print (the analytic
clause is dropped). -/
def WeierstrassParam : Prop :=
  ∀ P : PeriodPair, T5Glue.discL P ≠ 0 ∧ ParamProps P (wc P.g₂ P.g₃)

/-! ## Helpers -/

section Helpers

theorem hom_sub {G : Type*} [Group G] {Φ : ℂ → G} (h : ∀ z w, Φ (z + w) = Φ z * Φ w) (a b : ℂ) :
    Φ (a - b) = Φ a * (Φ b)⁻¹ := by
  have := h (a - b) b
  rw [sub_add_cancel] at this
  rw [this, mul_inv_cancel_right]

theorem hom_eq_iff {G : Type*} [Group G] {Φ : ℂ → G} {L : Submodule ℤ ℂ} (h : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hk : ∀ z, Φ z = 1 ↔ z ∈ L) (a b : ℂ) : Φ a = Φ b ↔ a - b ∈ L := by
  rw [← hk, hom_sub h, mul_inv_eq_one]

theorem addHom_eq_iff {G : Type*} [AddGroup G] {Φ : ℂ → G} {L : Submodule ℤ ℂ}
    (h : ∀ z w, Φ (z + w) = Φ z + Φ w) (hk : ∀ z, Φ z = 0 ↔ z ∈ L) (a b : ℂ) :
    Φ a = Φ b ↔ a - b ∈ L := by
  have hs : Φ (a - b) = Φ a - Φ b := by
    have := h (a - b) b; rw [sub_add_cancel] at this; rw [this, add_sub_cancel_right]
  rw [← hk, hs, sub_eq_zero]

open Classical in
theorem wPtW_of_not_mem {P : PeriodPair} {W : WeierstrassCurve ℂ} (hP : ParamProps P W) {z : ℂ}
    (hz : z ∉ P.lattice) : ∃ h : W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2),
      wPtW P W z = .some _ _ h := by
  have hne : wPtW P W z ≠ 0 := fun e => hz ((hP.2.1 z).1 e)
  unfold wPtW at hne ⊢
  by_cases hc : z ∉ P.lattice ∧ W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2)
  · exact ⟨hc.2, by rw [dif_pos hc]⟩
  · rw [dif_neg hc] at hne; exact absurd rfl hne

open Classical in
theorem mapPt_surjective (W : WeierstrassCurve ℂ) (σ : ℂ ≃+* ℂ) :
    Function.Surjective (mapPt W (σ : ℂ →+* ℂ)) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have h' : (W.map (σ : ℂ →+* ℂ)).toAffine.Nonsingular ((σ : ℂ →+* ℂ) (σ.symm x))
        ((σ : ℂ →+* ℂ) (σ.symm y)) := by
      simpa using h
    have h0 := (W.toAffine.map_nonsingular (σ : ℂ →+* ℂ).injective (σ.symm x) (σ.symm y)).mp h'
    refine ⟨.some _ _ h0, ?_⟩
    rw [mapPt_some]
    simp

end Helpers

/-! ## The g = 1 leaf (Shimura 1971, Thm 5.4) -/

section Leaf

open T5Glue
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

open Classical in
/-- **Analytic isomorphism `ℂ/L ≅ E(ℂ)`** for a Weierstrass curve `E = W` over `ℂ`: `ξ : ℂ → E(ℂ)` is a
surjective group homomorphism (Mathlib's group law on `W.toAffine.Point`) with kernel `L`, whose affine
coordinates `(x(ξ z), y(ξ z))` are holomorphic functions of `z` on `ℂ ∖ L`. For a lattice `L` this is
equivalent to `ξ` inducing a biholomorphic group isomorphism `ℂ/L → E(ℂ)`: a biholomorphic map of complex tori
taking `0` to `O` is a homomorphism; conversely a bijective holomorphic map of compact Riemann surfaces is
biholomorphic, and `ξ` is holomorphic at `L` by translation (`ξ(z) = ξ(z − a) + ξ(a)`, the group law of `E` is
holomorphic). -/
def IsAnalyticIso (L : Set ℂ) (W : WeierstrassCurve ℂ) (ξ : ℂ →+ W.toAffine.Point) : Prop :=
  (∀ z, ξ z = 0 ↔ z ∈ L) ∧ Function.Surjective ξ ∧
    ∃ X Y : ℂ → ℂ, DifferentiableOn ℂ X Lᶜ ∧ DifferentiableOn ℂ Y Lᶜ ∧
      ∀ z, z ∉ L → ∃ h : W.toAffine.Nonsingular (X z) (Y z), ξ z = .some (X z) (Y z) h

open Classical in
/-- **LEAF SHIMURA-1971-5.4 (the main theorem of complex multiplication for elliptic curves, lattice form).**
Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`, `√−m ↦ i√m`), `e : Kˢ → ℚ̄` normalized (`ιC ∘ e = κ` on `K`),
`σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]` on `K^ab` (`T5Glue.ArtinCond`: on every finite abelian
`F/K` inside `Kˢ`, through `ιC ∘ e`, `σ` acts as Tau Ceti's arithmetic Artin symbol of the idele class
of `s`). Let `𝔞 ⊂ K` be a lattice (`κ(𝔞)` is the lattice of a period pair; `𝔞` may belong to any order),
`E` an elliptic curve over `ℂ` (Mathlib's `WeierstrassCurve ℂ` with `IsElliptic`) and
`ξ : ℂ/κ(𝔞) → E(ℂ)` an analytic isomorphism (`IsAnalyticIso`). Then there is an analytic isomorphism
`ξ' : ℂ/κ(s⁻¹𝔞) → E^σ(ℂ)` (`E^σ = W.map σ`, `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂ = T5Glue.sInvLat m s 𝔞`) with
`ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`, where `ξ(u)^σ` is `σ` applied to the coordinates (`mapPt`) and
`v ∈ K` represents `s⁻¹u ∈ K/s⁻¹𝔞` iff `s_f v − u ∈ 𝔞̂` (`𝔞̂` the closure of `𝔞` in `𝔸_{K,f}`).

Source: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm 5.4
(statement as recalled, UNVERIFIED number and wording: "Let `E`, `ξ`, `𝔞` as above, `σ ∈ Aut(ℂ/K)`,
`s ∈ K_A^×` with `σ = [s, K]` on `K_ab`. Then there is a unique analytic isomorphism `ξ' : ℂ/s⁻¹𝔞 → E^σ`
with `ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`"); S. Lang, *Elliptic functions*, Ch. 10 §2, Thm 3; Silverman,
*Advanced topics*, Thm II.8.2 (for `𝒪_K`). Consequence of the print: uniqueness of `ξ'` is dropped; the
analytic-isomorphism predicate is the print's notion (see `IsAnalyticIso`); `σ` fixes `K` by `ArtinCond`.
Normalization: Shimura's `[s, K]` sends a uniformizer at `𝔭` to the arithmetic Frobenius (as Tau Ceti's map
does); see the report `docs/research/hcm-g1.md` §3 for the check (pending a reading of Shimura §5.2). -/
def ShimuraThm54 : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ P : PeriodPair, (P.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (ξ : ℂ →+ W.toAffine.Point),
    IsAnalyticIso (kappa m '' 𝔞) W ξ →
    ∃ ξ' : ℂ →+ (W.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticIso (kappa m '' sInvLat m s 𝔞) (W.map (σ : ℂ →+* ℂ)) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        mapPt W (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

end Leaf

/-! ## The reduction -/

section Final

open T5Glue Classical
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

theorem delta_wc (a b : ℂ) : (wc a b).Δ = a ^ 3 - 27 * b ^ 2 := by
  simp only [wc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- The Weierstrass parametrization as an additive homomorphism. -/
def wHom (P : PeriodPair) (h : ParamProps P (wc P.g₂ P.g₃)) : ℂ →+ (wc P.g₂ P.g₃).toAffine.Point where
  toFun := wPt P
  map_zero' := (h.2.1 0).2 (zero_mem _)
  map_add' := h.1

/-- **`T5Glue.ShimuraMainCM` from the g = 1 leaf.** -/
theorem shimuraMainCM_of_g1 (hS : ShimuraThm54) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) : T5Glue.ShimuraMainCM := by
  intro m _ hsq e he σ s hs 𝔞 P P' hP hP'
  obtain ⟨hΔ, hpar⟩ := hWP P
  have : (wc P.g₂ P.g₃).IsElliptic := ⟨by rw [delta_wc]; exact isUnit_iff_ne_zero.2 hΔ⟩
  have hξ : IsAnalyticIso (kappa m '' 𝔞) (wc P.g₂ P.g₃) (wHom P hpar) := by
    rw [← hP]
    refine ⟨hpar.2.1, hpar.2.2, P.weierstrassP, fun z => P.derivWeierstrassP z / 2,
      P.differentiableOn_weierstrassP, P.differentiableOn_derivWeierstrassP.div_const 2,
      fun z hz => wPtW_of_not_mem hpar hz⟩
  obtain ⟨ξ', hξ', hrel⟩ := hS m hsq e he σ s hs 𝔞 ⟨P, hP⟩ (wc P.g₂ P.g₃) (wHom P hpar) hξ
  rw [← hP'] at hξ'
  obtain ⟨hk', hs', X, Y, hX, hY, hXY⟩ := hξ'
  -- the auxiliary lattice `Λ''` of `E_P^σ`
  have hΔσ : σ P.g₂ ^ 3 - 27 * σ P.g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero (σ : ℂ →+* ℂ)).2 hΔ
    simpa [T5Glue.discL, map_sub, map_mul, map_pow, map_ofNat] using this
  obtain ⟨P'', h2, h3⟩ := hWU _ _ hΔσ
  have hW : (wc P.g₂ P.g₃).map (σ : ℂ →+* ℂ) = wc P''.g₂ P''.g₃ := by rw [map_wc, h2, h3]; rfl
  have hpar'' : ParamProps P'' ((wc P.g₂ P.g₃).map (σ : ℂ →+* ℂ)) := by rw [hW]; exact (hWP P'').2
  choose ψ₀ hψ₀ using fun z => hpar''.2.2 (ξ' z)
  have hP''eq := addHom_eq_iff hpar''.1 hpar''.2.1
  have l_inj : ∀ a b, a ∉ P''.lattice → b ∉ P''.lattice →
      P''.weierstrassP a = P''.weierstrassP b →
      P''.derivWeierstrassP a = P''.derivWeierstrassP b → a - b ∈ P''.lattice := by
    intro a b ha hb e1 e2
    rw [← hP''eq]
    obtain ⟨ha', hA⟩ := wPtW_of_not_mem hpar'' ha
    obtain ⟨hb', hB⟩ := wPtW_of_not_mem hpar'' hb
    rw [hA, hB]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨e1, by rw [e2]⟩
  have l_add : ∀ z z', ψ₀ (z + z') - ψ₀ z - ψ₀ z' ∈ P''.lattice := by
    intro z z'
    rw [sub_sub, ← hP''eq, hpar''.1, hψ₀, hψ₀, hψ₀, map_add]
  have l_ker : ∀ z, ψ₀ z ∈ P''.lattice ↔ z ∈ P'.lattice := by
    intro z
    rw [← hpar''.2.1, hψ₀, ← SetLike.mem_coe]
    exact hk' z
  have l_surj : ∀ a, ∃ z, ψ₀ z - a ∈ P''.lattice := by
    intro a
    obtain ⟨z, hz⟩ := hs' (wPtW P'' ((wc P.g₂ P.g₃).map (σ : ℂ →+* ℂ)) a)
    exact ⟨z, by rw [← hP''eq, hψ₀, hz]⟩
  have l_F : ∀ z, z ∉ P'.lattice →
      P''.weierstrassP (ψ₀ z) = X z ∧ P''.derivWeierstrassP (ψ₀ z) = 2 * Y z := by
    intro z hz
    have hψz : ψ₀ z ∉ P''.lattice := fun hm => hz ((l_ker z).1 hm)
    obtain ⟨h2', e2⟩ := wPtW_of_not_mem hpar'' hψz
    obtain ⟨h1, e1⟩ := hXY z hz
    have := hψ₀ z
    rw [e2, e1] at this
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at this
    obtain ⟨a1, a2⟩ := this
    refine ⟨a1, ?_⟩
    linear_combination 2 * a2
  have hGc : ContinuousOn (fun z => 2 * Y z) ((P'.lattice : Set ℂ)ᶜ) :=
    (continuousOn_const.mul hY.continuousOn)
  obtain ⟨α, hα⟩ := lin P' P'' ψ₀ X (fun z => 2 * Y z) l_inj l_add l_ker l_surj l_F hX hGc
  have hα_iff : ∀ z, α * z ∈ P''.lattice ↔ z ∈ P'.lattice := fun z => by
    rw [← l_ker]
    constructor
    · intro hm; simpa using add_mem (hα z) hm
    · intro hm; simpa using sub_mem hm (hα z)
  have hα0 : α ≠ 0 := by
    intro h0
    have := (hα_iff (P'.ω₁ / 2)).1 (by rw [h0, zero_mul]; exact zero_mem _)
    exact P'.ω₁_div_two_notMem_lattice this
  have hscale : T5Glue.IsScale P'' P' α := by
    refine ⟨hα0, ?_⟩
    ext t
    simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
    constructor
    · intro ht
      refine ⟨t / α, ?_, by field_simp⟩
      rw [← hα_iff]; field_simp; exact ht
    · rintro ⟨u, hu, rfl⟩
      exact (hα_iff u).2 hu
  refine ⟨α⁻¹, ⟨inv_ne_zero hα0, ?_, ?_⟩, ?_⟩
  · show σ P.g₂ = α⁻¹ ^ 4 * P'.g₂
    rw [← h2, hscale.g₂, inv_pow]
  · show σ P.g₃ = α⁻¹ ^ 6 * P'.g₃
    rw [← h3, hscale.g₃, inv_pow]
  · intro u v hu huv
    have hr := hrel u v huv
    obtain ⟨h1, e1⟩ := wPtW_of_not_mem hpar hu
    have hξu : wHom P hpar (kappa m u) = .some _ _ h1 := e1
    rw [hξu, mapPt_some] at hr
    have hv : kappa m v ∉ P'.lattice := by
      intro hm
      have : ξ' (kappa m v) = 0 := (hk' _).2 hm
      rw [this] at hr
      exact absurd hr (by simp)
    obtain ⟨f1, f2⟩ := l_F _ hv
    obtain ⟨h4, e4⟩ := hXY _ hv
    rw [e4] at hr
    simp only [WeierstrassCurve.Affine.Point.some.injEq, RingEquiv.coe_toRingHom] at hr
    obtain ⟨a1, a2⟩ := hr
    have hper'' : P''.weierstrassP (ψ₀ (kappa m v)) = P''.weierstrassP (α * kappa m v) ∧
        P''.derivWeierstrassP (ψ₀ (kappa m v)) = P''.derivWeierstrassP (α * kappa m v) := by
      have e : ψ₀ (kappa m v) = α * kappa m v +
          ((⟨ψ₀ (kappa m v) - α * kappa m v, hα (kappa m v)⟩ : P''.lattice) : ℂ) := by simp
      rw [e, PeriodPair.weierstrassP_add_coe, PeriodPair.derivWeierstrassP_add_coe]
      exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [a1, ← f1, hper''.1, hscale.weierstrassP, inv_pow]
    · rw [map_div₀, map_ofNat] at a2
      have : σ (P.derivWeierstrassP (kappa m u)) = 2 * Y (kappa m v) := by
        linear_combination 2 * a2
      rw [this, ← f2, hper''.2, hscale.derivWeierstrassP, inv_pow]

end Final

end HcmG1

/-- info: 'HcmG1.shimuraMainCM_of_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HcmG1.shimuraMainCM_of_g1
