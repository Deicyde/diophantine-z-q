import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeierstrassPeriods
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LimitUniqueness

/-! Compare the period quotient with the complex topology of the indicated
Proj model, including at its section at infinity. On the spot (c),
tex 1785–1787 and 1825–1828. -/

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Limits PkgI3 WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.IsogenyScheme
open scoped Topology PeriodPair

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

private def complexProjection (E : WeierstrassCurve ℚ) :
    Point ℂ (complexBaseChange.obj (projectiveTarget E)) ≃
      (Spec (.of ℂ) ⟶ Proj E.toProjective.grading) where
  toFun p := p.left ≫ pullback.fst _ _
  invFun p := complexLift (Over.homMk p (maps_to_rat_unique _ _))
  left_inv p := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w p).symm
  right_inv _ := pullback.lift_fst _ _ _

private theorem complexProjection_lift (E : WeierstrassCurve ℚ)
    (p : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E) :
    complexProjection E (complexLift p) = p.left := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  let p' : Spec (.of ℂ) ⟶ Proj E.toProjective.grading := p.left
  have hp : p' ≫ projectiveOverQ E = (𝟙 (Spec (.of ℂ))) ≫ f := by
    simpa [p', f, AbVar.ptObj] using Over.w p
  change pullback.lift p' (𝟙 _) hp ≫ pullback.fst (projectiveOverQ E) f = p'
  exact pullback.lift_fst p' _ hp

private def complexProjectiveValues (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Point ℂ (complexBaseChange.obj (projectiveTarget E)) ≃
      (E.baseChange ℂ).toAffine.Point :=
  (complexProjection E).trans (Equiv.ofBijective _ (projectiveValue_bijective E ℂ))

/-- The evaluation of the fixed complex projective curve in the chosen
period quotient, defined by its Weierstrass coordinates. -/
def projectiveTorusValue (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat)
    (p : Point ℂ (complexBaseChange.obj (projectiveTarget E))) :
    ℂ ⧸ Lat.lattice.toAddSubgroup :=
  (weierstrassPeriodEquiv E Lat hLat).symm
    (projectiveValue (p.left ≫ pullback.fst _ _))

theorem projectiveTorusValue_lift (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat)
    (p : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E) :
    projectiveTorusValue E Lat hLat (complexLift p) =
      (weierstrassPeriodEquiv E Lat hLat).symm (projectiveValue p.left) := by
  change (weierstrassPeriodEquiv E Lat hLat).symm
    (projectiveValue (complexProjection E (complexLift p))) = _
  rw [complexProjection_lift]

/-- A projective evaluation in the chosen period coordinates gives the
class of the same representative in the period quotient. -/
theorem projectiveTorusValue_lift_of_eval (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat)
    (p : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E) (z : ℂ)
    (h : projectiveValue p.left = weierPt E Lat z) :
    projectiveTorusValue E Lat hLat (complexLift p) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup z := by
  rw [projectiveTorusValue_lift, h, ← weierstrassPeriodEquiv_mk E Lat hLat,
    AddEquiv.symm_apply_apply]

private theorem projectiveTarget_t2 (E : WeierstrassCurve ℚ) :
    T2Space (Point ℂ (complexBaseChange.obj (projectiveTarget E))) := by
  let X := projectiveTarget E
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  let k : (complexBaseChange.obj X).left ⟶ X.left := pullback.fst X.hom f
  letI : IsAffineHom k := isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback X.hom f).flip inferInstance
  let A := E.toProjective.grading
  let Y := E.toProjective.coord 1
  let Z := E.toProjective.coord 2
  have hY : Y ∈ A 1 := E.toProjective.coord_mem_grading 1
  have hZ : Z ∈ A 1 := E.toProjective.coord_mem_grading 2
  have hOZ : Z ∈ (pointO E).asHomogeneousIdeal :=
    (mem_pointO_iff E hZ).mpr (by rw [evalZero_coord]; decide)
  have hOY : Y ∉ (pointO E).asHomogeneousIdeal := by
    rw [mem_pointO_iff E hY, evalZero_coord]
    decide
  have hO (P : Proj A) (hP : P ≠ pointO E) : Z ∉ P.asHomogeneousIdeal := fun h =>
    hP (eq_pointO_of_coord_mem E P (coord_zero_mem_of_coord_two_mem E P h) h)
  apply t2_of_affine_pair
  intro x y
  let p := k x.underlying
  let q := k y.underlying
  suffices ∃ a : E.toProjective.CoordinateRing, a ∈ A 1 ∧
      a ∉ p.asHomogeneousIdeal ∧ a ∉ q.asHomogeneousIdeal by
    obtain ⟨a, ha, hp, hq⟩ := this
    let U := Proj.basicOpen A a
    refine ⟨⟨k ⁻¹ᵁ U, (Proj.isAffineOpen_basicOpen A a ha zero_lt_one).preimage k⟩, ?_, ?_⟩
    · exact (Proj.mem_basicOpen _ _ _).mpr hp
    · exact (Proj.mem_basicOpen _ _ _).mpr hq
  have hpair (t : Proj A) :
      ∃ a : E.toProjective.CoordinateRing, a ∈ A 1 ∧
        a ∉ (pointO E).asHomogeneousIdeal ∧ a ∉ t.asHomogeneousIdeal := by
    by_cases ht : Y ∈ t.asHomogeneousIdeal
    · have ht' : t ≠ pointO E := fun e => hOY (e ▸ ht)
      refine ⟨Y + Z, add_mem hY hZ, ?_, ?_⟩
      · intro he
        have he' : Y + Z ∈ (pointO E).asHomogeneousIdeal.toIdeal := he
        have hz' : Z ∈ (pointO E).asHomogeneousIdeal.toIdeal := hOZ
        exact hOY (show Y ∈ (pointO E).asHomogeneousIdeal.toIdeal from by
          simpa using sub_mem he' hz')
      · intro he
        have he' : Y + Z ∈ t.asHomogeneousIdeal.toIdeal := he
        have ht'' : Y ∈ t.asHomogeneousIdeal.toIdeal := ht
        exact hO t ht' (show Z ∈ t.asHomogeneousIdeal.toIdeal from by
          simpa [add_comm Y Z] using sub_mem he' ht'')
    · exact ⟨Y, hY, hOY, ht⟩
  by_cases hp : p = pointO E
  · simpa only [hp] using hpair q
  by_cases hq : q = pointO E
  · obtain ⟨a, ha, haO, hap⟩ := hpair p
    exact ⟨a, ha, hap, by simpa only [hq] using haO⟩
  exact ⟨Z, hZ, hO p hp, hO q hq⟩

private theorem periodQuotient_compact (Lat : PeriodPair) :
    CompactSpace (ℂ ⧸ Lat.lattice.toAddSubgroup) := by
  let m := QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
  have hcompact : IsCompact (Set.range m) :=
    IsZLattice.isCompact_range_of_periodic Lat.lattice m QuotientAddGroup.continuous_mk
      (fun z w hw => by rw [map_add, show m w = 0 from (QuotientAddGroup.eq_zero_iff w).mpr hw,
        add_zero])
  have hm : Set.range m = Set.univ :=
    (QuotientAddGroup.mk'_surjective Lat.lattice.toAddSubgroup).range_eq
  exact ⟨hm ▸ hcompact⟩

section Analytic

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (Lat : PeriodPair) (hLat : IsLatticeOf E Lat)

private def periodX (z : ℂ) : ℂ := Lat.weierstrassP z - (E.b₂ : ℂ) / 12
private def periodY (z : ℂ) : ℂ :=
  (Lat.derivWeierstrassP z - (E.a₁ : ℂ) * periodX E Lat z - (E.a₃ : ℂ)) / 2

private def pointVector (u : ℂˣ) : (E.baseChange ℂ).toAffine.Point → Fin 3 → ℂ
  | .zero => ![0, -1, 0]
  | .some x y _ => (u : ℂ) • ![x, y, 1]

private theorem pointVector_equation (u : ℂˣ) (p : (E.baseChange ℂ).toAffine.Point) :
    (E.baseChange ℂ).toProjective.Equation (pointVector E u p) := by
  cases p with
  | zero => simp [pointVector, Projective.equation_iff]
  | some x y h =>
    rw [pointVector, Projective.equation_smul _ u.isUnit, Projective.equation_iff]
    simpa [Affine.equation_iff'] using h.1

private theorem pointVector_ne_zero (u : ℂˣ) (p : (E.baseChange ℂ).toAffine.Point) :
    pointVector E u p ≠ 0 := by
  cases p with
  | zero =>
    intro h
    have := congrFun h (1 : Fin 3)
    norm_num [pointVector] at this
  | some x y h =>
    intro he
    have := congrFun he (2 : Fin 3)
    simpa [pointVector, u.ne_zero] using this

private theorem pointVector_evaluates (u : ℂˣ) (p : (E.baseChange ℂ).toAffine.Point) :
    projectiveValue (projectiveVectorPoint E (pointVector_equation E u p)
      (pointVector_ne_zero E u p)).left = p := by
  cases p with
  | zero => exact projectiveValue_vector_origin E _ _ (by simp [pointVector]) (by simp [pointVector])
  | some x y h =>
    have hz : pointVector E u (.some x y h) 2 ≠ 0 := by simp [pointVector, u.ne_zero]
    have hx : pointVector E u (.some x y h) 0 / pointVector E u (.some x y h) 2 = x := by
      simp [pointVector, mul_comm (u : ℂ) x, u.ne_zero]
    have hy : pointVector E u (.some x y h) 1 / pointVector E u (.some x y h) 2 = y := by
      simp [pointVector, mul_comm (u : ℂ) y, u.ne_zero]
    rw [projectiveValue_vector_affine E _ _ hz (by simpa only [hx, hy] using h),
      Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

private theorem complexProjectiveValues_vector (u : ℂˣ) (p : (E.baseChange ℂ).toAffine.Point) :
    (complexProjectiveValues E).symm p =
      complexLift (projectiveVectorPoint E (pointVector_equation E u p) (pointVector_ne_zero E u p)) := by
  apply (complexProjectiveValues E).injective
  rw [Equiv.apply_symm_apply]
  change p = projectiveValue (complexProjection E (complexLift _))
  rw [complexProjection_lift, pointVector_evaluates]

private theorem weierPt_at_lattice {z : ℂ} (hz : z ∈ Lat.lattice) :
    weierPt E Lat z = 0 := by simp [weierPt, hz]

private theorem weierPt_off_lattice {z : ℂ} (hz : z ∉ Lat.lattice) :
    weierPt E Lat z = .some _ _ (weierstrassCoordinates_nonsingular E Lat hLat hz) := by
  rw [weierPt, ite_eq_right hz, dite_eq_left (weierstrassCoordinates_nonsingular E Lat hLat hz)]

/-- The affine chart varies holomorphically off the lattice. At a lattice point
the homogeneous vector scaled by `(z - z₀)^3` has value `[0:-1:0]`. -/
private theorem periodToProjective_continuous (hLat : IsLatticeOf E Lat) :
    Continuous (fun z => (complexProjectiveValues E).symm (weierPt E Lat z)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases hz₀ : z₀ ∈ Lat.lattice
  · rw [continuousAt_iff_punctured_nhds]
    let u (z : ℂ) : ℂˣ := if hz : z = z₀ then 1
      else Units.mk0 ((z - z₀)^3) (pow_ne_zero _ (sub_ne_zero.mpr hz))
    let p (z : ℂ) := weierPt E Lat z
    let P (z : ℂ) := pointVector E (u z) (p z)
    have hout : ∀ᶠ z in 𝓝[≠] z₀, z ∉ Lat.lattice := by
      filter_upwards [nhdsWithin_le_nhds (Lat.compl_lattice_sdiff_singleton_mem_nhds z₀),
        self_mem_nhdsWithin] with z h hz
      exact fun hl => h ⟨hl, hz⟩
    let s (z : ℂ) := z - z₀
    let X (z : ℂ) := s z + s z ^ 3 * (℘[Lat - z₀] z - 1 / z₀ ^ 2 - (E.b₂ : ℂ) / 12)
    let Y (z : ℂ) := (s z ^ 3 * ℘'[Lat - z₀] z - 2 - (E.a₁ : ℂ) * X z -
        s z ^ 3 * (E.a₃ : ℂ)) / 2
    have hx : ContinuousAt X z₀ := by
      have h := (Lat.analyticAt_weierstrassPExcept z₀).continuousAt
      unfold X s
      fun_prop
    have hy : ContinuousAt Y z₀ := by
      have h := (Lat.analyticAt_derivWeierstrassPExcept z₀).continuousAt
      unfold Y s
      fun_prop
    have hv : ∀ᶠ z in 𝓝[≠] z₀, P z = ![X z, Y z, s z ^ 3] := by
      filter_upwards [hout, self_mem_nhdsWithin] with z hz hn
      have hs : s z ≠ 0 := sub_ne_zero.mpr hn
      have hp : ℘[Lat - z₀] z + (1 / s z ^ 2 - 1 / z₀ ^ 2) = Lat.weierstrassP z :=
        Lat.weierstrassPExcept_add ⟨z₀, hz₀⟩ z
      have hd : ℘'[Lat - z₀] z - 2 / s z ^ 3 = Lat.derivWeierstrassP z :=
        Lat.derivWeierstrassPExcept_sub ⟨z₀, hz₀⟩ z
      have hcX : s z ^ 3 * (1 / s z ^ 2) = s z := by
        field_simp <;> ring
      have hcY : s z ^ 3 * (2 / s z ^ 3) = 2 := by
        field_simp
      have hX : s z ^ 3 * periodX E Lat z = X z := by
        rw [periodX, ← hp]
        dsimp only [X]
        simp only [mul_sub, mul_add, hcX]
        ring
      have hY : s z ^ 3 * periodY E Lat z = Y z := by
        rw [periodY, ← hd]
        dsimp only [Y]
        rw [← hX, ← mul_div_assoc]
        simp only [mul_sub, hcY]
        ring
      dsimp [P, p]
      rw [weierPt_off_lattice E Lat hLat hz, pointVector]
      dsimp only [u]
      have hne : z ≠ z₀ := hn
      rw [dite_eq_right hne]
      ext i
      fin_cases i
      · simpa [s, periodX] using hX
      · simpa [s, periodX, periodY] using hY
      · simp [s]
    have hp0 : P z₀ = ![0, -1, 0] := by simp [P, p, weierPt_at_lattice E Lat hz₀, pointVector]
    have hlim : ∀ i, Tendsto (fun z => P z i) (𝓝[≠] z₀) (𝓝 (P z₀ i)) := by
      intro i
      rw [hp0]
      have hX : Tendsto X (𝓝[≠] z₀) (𝓝 0) := by
        simpa [X, s] using hx.tendsto.mono_left nhdsWithin_le_nhds
      have hY : Tendsto Y (𝓝[≠] z₀) (𝓝 (-1)) := by
        simpa [Y, X, s] using hy.tendsto.mono_left nhdsWithin_le_nhds
      have hZ : Tendsto (fun z => s z ^ 3) (𝓝[≠] z₀) (𝓝 0) := by
        have h : ContinuousAt (fun z => s z ^ 3) z₀ := by unfold s; fun_prop
        simpa [s] using h.tendsto.mono_left nhdsWithin_le_nhds
      refine Tendsto.congr' (hv.mono fun z h => (congrFun h i).symm) ?_
      fin_cases i
      · simpa using hX
      · simpa using hY
      · simpa using hZ
    simpa only [← complexProjectiveValues_vector E] using
      tendsto_projectiveVectorPoint E (pointVector_equation E (u z₀) (p z₀))
        P (fun z => pointVector_equation E (u z) (p z))
        (fun z => pointVector_ne_zero E (u z) (p z)) (pointVector_ne_zero E (u z₀) (p z₀)) hlim
  · let P (z : ℂ) := pointVector E 1 (weierPt E Lat z)
    have hout := Lat.isClosed_lattice.isOpen_compl.mem_nhds hz₀
    have hX : ContinuousAt (periodX E Lat) z₀ :=
      ((Lat.analyticOnNhd_weierstrassP z₀ hz₀).sub analyticAt_const).continuousAt
    have hY : ContinuousAt (periodY E Lat) z₀ := by
      have := (Lat.analyticOnNhd_derivWeierstrassP z₀ hz₀).continuousAt
      unfold periodY
      fun_prop
    have hEq : ∀ᶠ z in 𝓝 z₀, P z = ![periodX E Lat z, periodY E Lat z, 1] := by
      filter_upwards [hout] with z hz
      simp [P, weierPt_off_lattice E Lat hLat hz, pointVector, periodX, periodY]
    have hlim (i : Fin 3) : Tendsto (fun z => P z i) (𝓝 z₀) (𝓝 (P z₀ i)) := by
      dsimp only [P]
      rw [weierPt_off_lattice E Lat hLat hz₀, pointVector, Units.val_one, one_smul]
      refine Tendsto.congr' (hEq.mono fun z h => (congrFun h i).symm) ?_
      fin_cases i
      · change Tendsto (periodX E Lat) (𝓝 z₀) (𝓝 (periodX E Lat z₀))
        exact hX.tendsto
      · change Tendsto (periodY E Lat) (𝓝 z₀) (𝓝 (periodY E Lat z₀))
        exact hY.tendsto
      · simp
    simpa only [ContinuousAt, ← complexProjectiveValues_vector E] using
      tendsto_projectiveVectorPoint E (pointVector_equation E 1 (weierPt E Lat z₀))
        P (fun z => pointVector_equation E 1 (weierPt E Lat z))
        (fun z => pointVector_ne_zero E 1 (weierPt E Lat z))
        (pointVector_ne_zero E 1 (weierPt E Lat z₀)) hlim

/-- The homeomorphism from the chosen period torus to the complex points of
the fixed projective curve. The inverse uses `projectiveValue`. -/
def projectivePeriodHomeomorph :
    (ℂ ⧸ Lat.lattice.toAddSubgroup) ≃ₜ Point ℂ (complexBaseChange.obj (projectiveTarget E)) := by
  letI := periodQuotient_compact Lat
  letI := projectiveTarget_t2 E
  let e := (weierstrassPeriodEquiv E Lat hLat).toEquiv.trans (complexProjectiveValues E).symm
  have h : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk Lat.lattice.toAddSubgroup).continuous_iff.mpr
    change Continuous (fun z => (complexProjectiveValues E).symm
      (weierstrassPeriodEquiv E Lat hLat (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup z)))
    simpa only [weierstrassPeriodEquiv_mk] using periodToProjective_continuous E Lat hLat
  exact h.homeoOfEquivCompactToT2

theorem continuous_projectiveTorusValue :
    Continuous (projectiveTorusValue E Lat hLat) :=
  (projectivePeriodHomeomorph E Lat hLat).continuous_symm

end Analytic


end ZInQ.Manuscript.RC.J0Cusps
