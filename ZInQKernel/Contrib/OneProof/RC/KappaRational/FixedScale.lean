import ZInQKernel.Contrib.OneProof.RC.ModFnField.RationalExpansion
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Tail
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.AtScale

/-! The leading cusp coefficients determine the scale at tex 1785–1787 and
1825–1828. The coefficient comparison is on-the-spot, provenance (c). -/

noncomputable section

open Filter Topology UpperHalfPlane AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ModFnField ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.KappaRational

/-- At any nonzero complex scale the width-one coordinate poles have leading
coefficients `κ⁻²` and `-κ⁻³` in the given Weierstrass model. -/
theorem coordinate_leading_terms (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (L : PeriodPair) {κ : ℂ} (hκ : κ ≠ 0) :
    ∃ X Y : ℂ → ℂ, AnalyticAt ℂ X 0 ∧ AnalyticAt ℂ Y 0 ∧
      X 0 = κ⁻¹ ^ 2 ∧ Y 0 = -(κ⁻¹ ^ 3) ∧
      ∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
        X (Function.Periodic.qParam 1 τ) =
          Function.Periodic.qParam 1 τ ^ 2 * xCoordinate E f L κ τ ∧
        Y (Function.Periodic.qParam 1 τ) =
          Function.Periodic.qParam 1 τ ^ 3 * yCoordinate E f L κ τ := by
  obtain ⟨F, hF, hFr, hF0, hF1, hFτ⟩ := primitive_rationalTaylor E f hf 1
  obtain ⟨u, hu, _, hu0, hFu⟩ := hFr.factor_at_zero hF hF0
  have hu1 : u 0 = 1 := by simpa only [Rat.cast_one] using hu0.trans hF1
  let v := fun q : ℂ => (κ * u q)⁻¹
  have huκ : AnalyticAt ℂ (fun q => κ * u q) 0 := analyticAt_const.mul hu
  have hv : AnalyticAt ℂ v 0 := huκ.inv (by simp [hu1, hκ])
  have hFκ : AnalyticAt ℂ (fun q => κ * F q) 0 := analyticAt_const.mul hF
  let A := fun q : ℂ => regularPart L (κ * F q)
  let B := fun q : ℂ => L.derivWeierstrassPExcept 0 (κ * F q)
  have hA' : AnalyticAt ℂ (regularPart L) ((fun q => κ * F q) 0) := by
    simpa [hF0] using L.analyticAt_weierstrassPExcept 0
  have hB' : AnalyticAt ℂ (L.derivWeierstrassPExcept 0) ((fun q => κ * F q) 0) := by
    simpa [hF0] using L.analyticAt_derivWeierstrassPExcept 0
  have hA : AnalyticAt ℂ A 0 :=
    AnalyticAt.comp (f := fun q => κ * F q) (x := 0) hA' hFκ
  have hB : AnalyticAt ℂ B 0 :=
    AnalyticAt.comp (f := fun q => κ * F q) (x := 0) hB' hFκ
  let X := fun q : ℂ => v q ^ 2 + q ^ 2 * (A q - (E.b₂ : ℂ) / 12)
  let Y := fun q : ℂ => (-2 * v q ^ 3 + q ^ 3 * B q -
    (E.a₁ : ℂ) * (q * X q) - (E.a₃ : ℂ) * q ^ 3) / 2
  have hX : AnalyticAt ℂ X 0 := (hv.pow 2).add ((analyticAt_id.pow 2).mul (hA.sub analyticAt_const))
  have hY : AnalyticAt ℂ Y 0 :=
    ((((analyticAt_const.mul (hv.pow 3)).add ((analyticAt_id.pow 3).mul hB)).sub
      (analyticAt_const.mul (analyticAt_id.mul hX))).sub
      (analyticAt_const.mul (analyticAt_id.pow 3))).div_const
  refine ⟨X, Y, hX, hY, by simp [X, v, hu1], by simp [Y, v, hu1]; ring, ?_⟩
  have huN : ∀ᶠ q : ℂ in 𝓝 0, u q ≠ 0 := hu.continuousAt (isOpen_ne.mem_nhds (by simp [hu1]))
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp
    ((qParam_tendsto_atImInfty zero_lt_one).eventually (hFu.and huN))
  refine ⟨T, fun τ hτ => ?_⟩
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hqu : F q = q * u q ∧ u q ≠ 0 := hT τ hτ.le
  have huτ : scaledPrimitive f κ τ = κ * F q := by
    rw [hFτ τ]
    simp [scaledPrimitive]
  have hx : X q = q ^ 2 * xCoordinate E f L κ τ := by
    simp only [X, v, xCoordinate, huτ, weierstrassP_split, A, hqu.1]
    field_simp [hq, hqu.2, hκ]
    ring
  refine ⟨hx, ?_⟩
  change Y q = q ^ 3 * yCoordinate E f L κ τ
  simp only [Y, v, B, hx, yCoordinate, huτ, derivWeierstrassP_split, hqu.1]
  field_simp [hq, hqu.2, hκ]
  ring

/-- Away from the cusp itself, the primitive on a sufficiently high tail
avoids the lattice, so both affine coordinates there are genuine. -/
theorem scaledPrimitive_off_lattice_on_tail (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (L : PeriodPair) {κ : ℂ} (hκ : κ ≠ 0) :
    ∃ T : ℝ, ∀ τ : ℍ, T < τ.im → scaledPrimitive f κ τ ∉ L.lattice := by
  obtain ⟨F, hF, hFr, hF0, hF1, hFτ⟩ := primitive_rationalTaylor E f hf 1
  obtain ⟨u, hu, _, hu0, hFu⟩ := hFr.factor_at_zero hF hF0
  have hu1 : u 0 = 1 := by simpa only [Rat.cast_one] using hu0.trans hF1
  have huN : ∀ᶠ q : ℂ in 𝓝 0, u q ≠ 0 := hu.continuousAt (isOpen_ne.mem_nhds (by simp [hu1]))
  have hnear : ∀ᶠ q : ℂ in 𝓝 0, κ * F q ∈ (L.lattice : Set ℂ)ᶜ ∪ {0} := by
    have hcont : Tendsto (fun q : ℂ => κ * F q) (𝓝 0) (𝓝 0) := by
      have hFκ : AnalyticAt ℂ (fun q => κ * F q) 0 := analyticAt_const.mul hF
      simpa [hF0] using hFκ.continuousAt.tendsto
    have hsmall : (L.lattice : Set ℂ)ᶜ ∪ {0} ∈ 𝓝 (0 : ℂ) := by
      simpa only [Set.compl_sdiff, Set.union_comm] using
        L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)
    exact (tendsto_def.mp hcont) _ hsmall
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp
    ((qParam_tendsto_atImInfty zero_lt_one).eventually (hFu.and (huN.and hnear)))
  refine ⟨T, fun τ hτ => ?_⟩
  obtain ⟨he, hne, hm⟩ := hT τ hτ.le
  have heq : scaledPrimitive f κ τ = κ * F (Function.Periodic.qParam 1 τ) := by
    rw [hFτ τ]
    simp [scaledPrimitive]
  rw [heq]
  rcases hm with hm | hm
  · exact hm
  · rw [Set.mem_singleton_iff, he] at hm
    exact (mul_ne_zero hκ (mul_ne_zero (Function.Periodic.qParam_ne_zero _) hne) hm).elim

private theorem leading_coefficient {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (d : ℕ) {g : ℍ → ℂ} {T S : ℝ}
    (hval : ∀ τ : ℍ, T < τ.im →
      F (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ ^ d * g τ)
    (a : LaurentSeries ℚ)
    (ha : ∀ τ : ℍ, S < τ.im →
      HasSum (fun m : ℤ => (a.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m) (g τ)) :
    (a.coeff (-(d : ℤ)) : ℂ) = F 0 := by
  obtain ⟨r, hr⟩ := hF.hasFPowerSeriesAt
  let p : PowerSeries ℂ := PowerSeries.mk fun n => iteratedDeriv n F 0 / n.factorial
  let b : LaurentSeries ℂ := HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ p
  let c : LaurentSeries ℂ := a.map (Rat.castHom ℂ)
  obtain ⟨U, hU⟩ := (atImInfty_mem _).mp
    ((qParam_tendsto_atImInfty zero_lt_one) (Metric.eball_mem_nhds _ hr.r_pos))
  have hcb : c = b := by
    refine laurent_unique_of_tail (T := max (max U T) S) (g := g) (fun τ hτ => ?_) (fun τ hτ => ?_)
    · simpa [c] using ha τ ((le_max_right _ _).trans_lt hτ)
    · let q := Function.Periodic.qParam 1 (τ : ℂ)
      have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
      have hsmall : q ∈ Metric.eball 0 r := hU τ
        ((le_max_left _ _).trans ((le_max_left _ _).trans hτ.le))
      have hqval := hval τ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hτ))
      change HasSum (fun m : ℤ => b.coeff m * q ^ m) (g τ)
      apply hasSum_laurent_shift (RingHom.id ℂ) p d hq
      rw [← hqval]
      simpa only [RingHom.id_apply, p, PowerSeries.coeff_mk, sub_zero,
        FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hr.hasSum_sub hsmall
  have he := congrArg (fun z : LaurentSeries ℂ => z.coeff (-(d : ℤ))) hcb
  change (a.coeff (-(d : ℤ)) : ℂ) = b.coeff (-(d : ℤ)) at he
  rw [he, HahnSeries.coeff_single_mul, one_mul, sub_self]
  change (HahnSeries.ofPowerSeries ℤ ℂ p).coeff ((0 : ℕ) : ℤ) = F 0
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
  simp

/-- Rational width-one Laurent expansions of both fixed analytic coordinates
force a rational scale: the negative ratio of their leading coefficients is
the scale itself. -/
theorem rational_of_coordinate_expansions (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (L : PeriodPair) {κ : ℂ} (hκ : κ ≠ 0)
    (x y : LaurentSeries ℚ) (T : ℝ)
    (hxy : ∀ τ : ℍ, T < τ.im →
      HasSum (fun m : ℤ => (x.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m)
        (xCoordinate E f L κ τ) ∧
      HasSum (fun m : ℤ => (y.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m)
        (yCoordinate E f L κ τ)) :
    ∃ c : ℚ, (c : ℂ) = κ := by
  obtain ⟨X, Y, hX, hY, hX0, hY0, S, hS⟩ := coordinate_leading_terms E f hf L hκ
  have hx : (x.coeff (-2) : ℂ) = κ⁻¹ ^ 2 :=
    (leading_coefficient hX 2 (fun τ hτ => (hS τ hτ).1) x (fun τ hτ => (hxy τ hτ).1)).trans hX0
  have hy : (y.coeff (-3) : ℂ) = -(κ⁻¹ ^ 3) :=
    (leading_coefficient hY 3 (fun τ hτ => (hS τ hτ).2) y (fun τ hτ => (hxy τ hτ).2)).trans hY0
  refine ⟨-x.coeff (-2) / y.coeff (-3), ?_⟩
  rw [Rat.cast_div, Rat.cast_neg, hx, hy]
  field_simp [hκ]

/-- A rational map agreeing with the fixed analytic parametrization on the
width-one cusp tail determines the fixed scale. Only the indicated local
agreement is used; no comparison at another cusp is required. -/
theorem rational_of_projective_values_on_tail (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℂ} (hκ : κ ≠ 0)
    (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ)
    (T : ℝ) (hmatch : ∀ τ : ℍ, T < τ.im →
      projectiveValue ((X.complexPoint τ).comp π hQ).val = phiAn E f L κ τ) :
    ∃ c : ℚ, (c : ℂ) = κ := by
  classical
  let := X.integral
  obtain ⟨S, hS⟩ := scaledPrimitive_off_lattice_on_tail E f hf L hκ
  let U := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
  let V := π ⁻¹ᵁ U
  have hval (τ : ℍ) (hτ : max T S < τ.im) :
      ∃ hv : (X.complexPoint τ).val default ∈ V,
        (X.complexPoint τ).evalSection V hv (π.app U (sectionXOverZ E)) =
          xCoordinate E f L κ τ ∧
        (X.complexPoint τ).evalSection V hv (π.app U (sectionYOverZ E)) =
          yCoordinate E f L κ τ := by
    let u := (X.complexPoint τ).comp π hQ
    have hlat := hS τ ((le_max_right _ _).trans_lt hτ)
    have hn := Affine.equation_iff_nonsingular.mp (coordinates_equation E f hL κ hlat)
    have hphi : phiAn E f L κ τ = .some _ _ hn := by
      have harg : κ * eichlerPotential f τ = scaledPrimitive f κ τ := by simp [scaledPrimitive]
      rw [phiAn, weierPt, harg, ite_eq_right hlat]
      change (if h : (E.baseChange ℂ).toAffine.Nonsingular (xCoordinate E f L κ τ)
          (yCoordinate E f L κ τ) then Affine.Point.some _ _ h else 0) = _
      rw [dite_eq_left hn]
    have hm := (hmatch τ ((le_max_left _ _).trans_lt hτ)).trans hphi
    have ho : u.val default ≠ pointO E := by
      intro hh
      change projectiveValue u.val = _ at hm
      rw [projectiveValue, dite_eq_left hh] at hm
      cases hm
    have hu : u.val default ∈ U := by
      rw [Proj.mem_basicOpen]
      intro hZ
      exact ho (eq_pointO_of_coord_mem E _ (coord_zero_mem_of_coord_two_mem E _ hZ) hZ)
    obtain ⟨_, hcoord⟩ := ModFnClassify.projectiveValue_on_affine E u ho hu
    change projectiveValue u.val = _ at hm
    have hei := hcoord.symm.trans hm
    injection hei with hx hy
    refine ⟨hu, ?_, ?_⟩
    · rw [← evalSection_comp (X.complexPoint τ) π hQ U hu]
      exact hx
    · rw [← evalSection_comp (X.complexPoint τ) π hQ U hu]
      exact hy
  have : Nonempty V := by
    let τ : ℍ := ⟨⟨0, max (max T S) 0 + 1⟩, by
      change 0 < max (max T S) 0 + 1
      have := le_max_right (max T S) (0 : ℝ)
      linarith⟩
    have hτ : max T S < τ.im := by
      change max T S < max (max T S) 0 + 1
      have := le_max_left (max T S) (0 : ℝ)
      linarith
    exact ⟨⟨_, (hval τ hτ).choose⟩⟩
  let rx := π.app U (sectionXOverZ E)
  let ry := π.app U (sectionYOverZ E)
  obtain ⟨Gx, Tx, _, hsx, hvx⟩ := X.sectionExpansion V rx
  obtain ⟨Gy, Ty, _, hsy, hvy⟩ := X.sectionExpansion V ry
  refine rational_of_coordinate_expansions E f hf L hκ
    (X.functionField (X.X.germToFunctionField V rx))
    (X.functionField (X.X.germToFunctionField V ry))
    (max (max T S) (max Tx Ty)) (fun τ hτ => ?_)
  obtain ⟨hv, hx, hy⟩ := hval τ ((le_max_left _ _).trans_lt hτ)
  constructor
  · rw [← hx, (hvx τ hv).2]
    simp only [ModFnClassify.qParam_one_zpow]
    exact hsx τ ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hτ))
  · rw [← hy, (hvy τ hv).2]
    simp only [ModFnClassify.qParam_one_zpow]
    exact hsy τ ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hτ))

/-- For the constructed curve, rationality is precisely the obstruction to
the interior map at the specified scale. The converse uses only a cusp tail.

The → direction must not be cited as the source of κ ∈ ℚ (circularity rule). -/
theorem algebraicParametrizationAtScale_iff (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [NeZero (newformLevel E)] (X : X0Model (newformLevel E))
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℂ} (hκ : IsParamScale (newformLevel E) f L κ) :
    AlgebraicParametrizationAtScale E X f L κ ↔ ∃ c : ℚ, (c : ℂ) = κ := by
  constructor
  · rintro ⟨π, hQ, _, hp⟩
    exact rational_of_projective_values_on_tail E X f hf hL hκ.1 π hQ 0 (fun τ _ => hp τ)
  · exact ModFnClassify.algebraicParametrizationAtScale E X f hf hL hκ


end ZInQ.Manuscript.RC.KappaRational
