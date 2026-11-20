import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAbelian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.AffineLimit

/-! Field points on the fixed Proj model, including its rational section at
infinity. On the spot (c), tex 1785–1787. -/

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj WeierstrassCurve HomogeneousLocalization Filter PkgI3
open scoped Topology
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

open PreparedParam

private abbrev coordAway (E : WeierstrassCurve ℚ) (i : Fin 3) :=
  Away E.toProjective.grading (E.toProjective.coord i)

private def evalAway {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (f : E.toProjective.CoordinateRing) (g : E.toProjective.CoordinateRing →+* F)
    (hf : g f ≠ 0) : Away E.toProjective.grading f →+* F :=
  (IsLocalization.Away.lift (S := Localization.Away f)
    _ (isUnit_iff_ne_zero.mpr hf)).comp (algebraMap _ _)

private theorem evalAway_mk {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (f : E.toProjective.CoordinateRing) (g : E.toProjective.CoordinateRing →+* F)
    (hf : g f ≠ 0) {d : ℕ} (hd : f ∈ E.toProjective.grading d) (n : ℕ)
    (a : E.toProjective.CoordinateRing) (ha : a ∈ E.toProjective.grading (n • d)) :
    evalAway f g hf (Away.mk E.toProjective.grading hd n a ha) = g a / g f ^ n := by
  simp only [evalAway, RingHom.coe_comp, Function.comp_apply]
  change (Localization.awayLift g f _) (Localization.mk a ⟨f ^ n, ⟨n, rfl⟩⟩) = _
  rw [Localization.awayLift_mk g f a (g f)⁻¹ (mul_inv_cancel₀ hf), div_eq_mul_inv, inv_pow]

private def onChart (E : WeierstrassCurve ℚ) (i : Fin 3) {F : Type} [Field F]
    (g : coordAway E i →+* F) : Spec (.of F) ⟶ Proj E.toProjective.grading :=
  Spec.map (CommRingCat.ofHom g) ≫
    Proj.awayι _ _ (E.toProjective.coord_mem_grading i) (by decide)

private theorem chart_mem_iff (E : WeierstrassCurve ℚ) (i : Fin 3) {F : Type} [Field F]
    (g : coordAway E i →+* F) (n : ℕ) (a : E.toProjective.CoordinateRing)
    (ha : a ∈ E.toProjective.grading (n • (1 : ℕ))) :
    a ∈ (onChart E i g default).asHomogeneousIdeal ↔
      g (Away.mk _ (E.toProjective.coord_mem_grading i) n a ha) = 0 := by
  let A := E.toProjective.grading
  let f := E.toProjective.coord i
  let d := E.toProjective.coord_mem_grading i
  let b := Proj.basicOpenIsoSpec A f d (by decide)
  let x := b.inv (Spec.map (CommRingCat.ofHom g) default)
  have he : (Proj.basicOpenToSpec A f).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec A f := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply A x
    ⟨n • (1 : ℕ), ⟨a, ha⟩, ⟨f ^ n, SetLike.pow_mem_graded n d⟩, ⟨n, rfl⟩⟩
  rw [← he] at h
  change _ ∈ ((Proj.basicOpenToSpec A f) x).asIdeal ↔ _ at h
  have hx : Proj.basicOpenToSpec A f x = Spec.map (CommRingCat.ofHom g) default := by
    change b.hom (b.inv _) = _
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hx] at h
  refine h.symm.trans ?_
  change Away.mk A d n a ha ∈ ((Spec.map (CommRingCat.ofHom g)) default).asIdeal ↔ _
  rw [Spec.map_apply]
  change Away.mk A d n a ha ∈ (default : Spec (.of F)).asIdeal.comap g ↔ _
  rw [Ideal.mem_comap, Scheme.default_asIdeal, Ideal.mem_bot]

private theorem evalZero_Y (E : WeierstrassCurve ℚ) :
    E.toProjective.evalZero (E.toProjective.coord 1) ≠ 0 := by
  rw [evalZero_coord]
  decide

/-- The rational section of the indicated Proj model at `[0:1:0]`. -/
def weierstrassOrigin (E : WeierstrassCurve ℚ) :
    Spec (.of ℚ) ⟶ Proj E.toProjective.grading :=
  onChart E 1 (evalAway (E.toProjective.coord 1) E.toProjective.evalZero.toRingHom (evalZero_Y E))

theorem weierstrassOrigin_point (E : WeierstrassCurve ℚ) :
    weierstrassOrigin E default = pointO E := by
  apply eq_pointO_of_coord_mem
  all_goals
    rw [weierstrassOrigin, chart_mem_iff E 1 _ 1 _ (by simpa using E.toProjective.coord_mem_grading _),
      evalAway_mk _ _ _ (E.toProjective.coord_mem_grading 1)]
    simp

private theorem unique_over_origin {E : WeierstrassCurve ℚ} {F : Type} [Field F] [Algebra ℚ F]
    (u : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (hu : u default = pointO E) :
    u = Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ weierstrassOrigin E := by
  let X := Proj E.toProjective.grading
  let R := X.residueField (pointO E)
  let t := Scheme.SpecToEquivOfField ℚ X (weierstrassOrigin E)
  have ht : t.1 = pointO E :=
    (congrArg (weierstrassOrigin E) (Subsingleton.elim (IsLocalRing.closedPoint ℚ) (default : Spec (.of ℚ)))).trans
      (weierstrassOrigin_point E)
  let g : R ⟶ CommRingCat.of ℚ := (X.residueFieldCongr ht).inv ≫ t.2
  let i : CommRingCat.of ℚ ⟶ R :=
    (Scheme.Spec.residueFieldIsoOfField (projectiveOverQ E (pointO E))).inv ≫
      (projectiveOverQ E).residueFieldMap (pointO E)
  have hg : Function.Surjective g.hom :=
    Function.RightInverse.surjective fun q : ℚ =>
      DFunLike.congr_fun
        (Subsingleton.elim (g.hom.comp i.hom) (RingHom.id ℚ)) q
  let e := Scheme.SpecToEquivOfField F X
  have he (p : Spec (.of F) ⟶ X) (hp : p default = pointO E) :
      e p = ⟨pointO E, g ≫ CommRingCat.ofHom (algebraMap ℚ F)⟩ := by
    apply Scheme.SpecToEquivOfField_eq_iff.mpr
    have hp' : (e p).1 = pointO E :=
      (congrArg p (Subsingleton.elim (IsLocalRing.closedPoint F) (default : Spec (.of F)))).trans hp
    refine ⟨hp', ?_⟩
    let eg := RingEquiv.ofBijective g.hom ⟨g.hom.injective, hg⟩
    letI : Subsingleton (R →+* F) := ⟨fun f k => by
      apply RingHom.ext
      intro a
      obtain ⟨q, rfl⟩ := eg.symm.surjective a
      exact DFunLike.congr_fun
        (Subsingleton.elim (f.comp eg.symm.toRingHom) (k.comp eg.symm.toRingHom)) q⟩
    apply (cancel_epi (X.residueFieldCongr hp').inv).mp
    rw [Iso.inv_hom_id_assoc]
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)
  let w := Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ weierstrassOrigin E
  have hw : w default = pointO E := by
    dsimp only [w]
    rw [Scheme.Hom.comp_apply, Subsingleton.elim (Spec.map _ default) (default : Spec (.of ℚ))]
    exact weierstrassOrigin_point E
  exact e.injective ((he u hu).trans (he w hw).symm)

private abbrev zOpen (E : WeierstrassCurve ℚ) : (Proj E.toProjective.grading).Opens :=
  Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)

private def zIso (E : WeierstrassCurve ℚ) :
    (zOpen E).toScheme ≅ Spec (.of E.toAffine.CoordinateRing) :=
  Proj.basicOpenIsoSpec _ _ (E.toProjective.coord_mem_grading 2) (by decide) ≪≫
    Scheme.Spec.mapIso (affineEquivZChart E).toCommRingCatIso.op

private theorem zOpen_ne_origin {E : WeierstrassCurve ℚ}
    {v : Proj E.toProjective.grading} : v ∈ zOpen E ↔ v ≠ pointO E := by
  rw [zOpen, Proj.mem_basicOpen]
  constructor
  · rintro hv rfl
    exact hv ((mem_pointO_iff E (E.toProjective.coord_mem_grading 2)).mpr
      (by rw [evalZero_coord]; decide))
  · intro hv hz
    exact hv (eq_pointO_of_coord_mem E v (coord_zero_mem_of_coord_two_mem E v hz) hz)

private theorem range_zOpen {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (p : Spec (.of F) ⟶ Proj E.toProjective.grading) (hp : p default ≠ pointO E) :
    Set.range p ⊆ Set.range (zOpen E).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x (default : Spec (.of F))]
  exact ⟨⟨_, zOpen_ne_origin.mpr hp⟩, rfl⟩

private def pointInZ {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (p : Spec (.of F) ⟶ Proj E.toProjective.grading) (hp : p default ≠ pointO E) :
    Spec (.of F) ⟶ Spec (.of E.toAffine.CoordinateRing) :=
  IsOpenImmersion.lift (zOpen E).ι p (range_zOpen p hp) ≫ (zIso E).hom

private def zRingMap {E : WeierstrassCurve ℚ} {F : Type} [Field F] [Algebra ℚ F]
    (p : Spec (.of F) ⟶ Spec (.of E.toAffine.CoordinateRing)) : E.toAffine.CoordinateRing →ₐ[ℚ] F :=
  { toRingHom := ((Scheme.ΓSpecIso (.of E.toAffine.CoordinateRing)).inv ≫ p.appTop ≫
      (Scheme.ΓSpecIso (.of F)).hom).hom
    commutes' := fun x => DFunLike.congr_fun (Subsingleton.elim
      (((Scheme.ΓSpecIso (.of E.toAffine.CoordinateRing)).inv ≫ p.appTop ≫
        (Scheme.ΓSpecIso (.of F)).hom).hom.comp
        (algebraMap ℚ E.toAffine.CoordinateRing)) (algebraMap ℚ F)) x }

private theorem zRingMap_toRingHom {E : WeierstrassCurve ℚ} {F : Type} [Field F] [Algebra ℚ F]
    (p : Spec (.of F) ⟶ Spec (.of E.toAffine.CoordinateRing)) :
    (zRingMap p).toRingHom = (Spec.homEquiv p).hom := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective p
  change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map g).appTop ≫ (Scheme.ΓSpecIso _).hom).hom =
    (Spec.homEquiv (Spec.map g)).hom
  simp [Scheme.ΓSpecIso_naturality]

private theorem value_ne_origin {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {F : Type} [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (hp : p default ≠ pointO E) :
    let g := zRingMap (pointInZ p hp)
    projectiveValue p = .some (g (AdjoinRoot.of E.toAffine.polynomial Polynomial.X))
      (g (AdjoinRoot.root E.toAffine.polynomial))
      (Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom g)) := by
  classical
  rw [projectiveValue, dite_eq_right hp]
  rfl

/-- The projective identity is characterized by the zero value in every
extension field. -/
theorem projectiveValue_eq_zero_iff {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {F : Type} [Field F] [Algebra ℚ F] (p : Spec (.of F) ⟶ Proj E.toProjective.grading) :
    projectiveValue p = 0 ↔ p default = pointO E := by
  classical
  by_cases hp : p default = pointO E
  · simp [projectiveValue, hp]
  · rw [value_ne_origin p hp, iff_false_intro hp]
    constructor
    · intro h
      cases h
    · exact False.elim

private theorem pointInZ_factor {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (p : Spec (.of F) ⟶ Proj E.toProjective.grading) (hp : p default ≠ pointO E) :
    pointInZ p hp ≫ (zIso E).inv ≫ (zOpen E).ι = p := by
  simp [pointInZ]

/-- Evaluation on the fixed projective curve identifies its field points with
the usual Weierstrass points. At infinity it uses the rational section. -/
theorem projectiveValue_bijective (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (F : Type) [Field F] [Algebra ℚ F] :
    Function.Bijective
      (projectiveValue (E := E) : (Spec (.of F) ⟶ Proj E.toProjective.grading) →
        (E.baseChange F).toAffine.Point) := by
  classical
  constructor
  · intro p q he
    by_cases hp : p default = pointO E <;> by_cases hq : q default = pointO E
    · rw [unique_over_origin p hp, unique_over_origin q hq]
    · rw [projectiveValue, dite_eq_left hp, value_ne_origin q hq] at he
      cases he
    · rw [value_ne_origin p hp, projectiveValue, dite_eq_left hq] at he
      cases he
    · rw [value_ne_origin p hp, value_ne_origin q hq] at he
      have hxy := Affine.Point.some.inj he
      have hg := Affine.CoordinateRing.algHom_ext hxy.1 hxy.2
      have hz : pointInZ p hp = pointInZ q hq :=
        Spec.homEquiv.injective (CommRingCat.hom_ext (by
          simpa only [zRingMap_toRingHom] using congrArg AlgHom.toRingHom hg))
      rw [← pointInZ_factor p hp, ← pointInZ_factor q hq, hz]
  · intro v
    cases v with
    | zero =>
      refine ⟨Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ weierstrassOrigin E, ?_⟩
      have h : (Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ weierstrassOrigin E)
          default = pointO E := by
        rw [Scheme.Hom.comp_apply, Subsingleton.elim (Spec.map _ default) (default : Spec (.of ℚ))]
        exact weierstrassOrigin_point E
      rw [projectiveValue, dite_eq_left h]
      rfl
    | some x y h =>
      let g : E.toAffine.CoordinateRing →ₐ[ℚ] F := Affine.CoordinateRing.evalAlgHom h.1
      let s := Spec.map (CommRingCat.ofHom g.toRingHom)
      let p := s ≫ (zIso E).inv ≫ (zOpen E).ι
      have hp : p default ≠ pointO E :=
        zOpen_ne_origin.mp ((zIso E).inv (s default)).2
      have hel : pointInZ p hp = s := by
        apply (cancel_mono ((zIso E).inv ≫ (zOpen E).ι)).mp
        exact pointInZ_factor p hp
      have hg : zRingMap (pointInZ p hp) = g := by
        rw [hel]
        apply AlgHom.toRingHom_injective
        change (zRingMap s).toRingHom = g.toRingHom
        rw [zRingMap_toRingHom]
        exact congrArg CommRingCat.Hom.hom
          (Spec.homEquiv.apply_symm_apply (CommRingCat.ofHom g.toRingHom))
      refine ⟨p, ?_⟩
      rw [value_ne_origin p hp]
      congr 1
      · rw [hg, Affine.CoordinateRing.evalAlgHom_of_X]
      · rw [hg, Affine.CoordinateRing.evalAlgHom_root]


/-- A multiplication inducing Weierstrass addition on complex points forces
the rational identity to be the specified projective origin. -/
theorem projectiveGroup_origin (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [GrpObj (projectiveTarget E)]
    (hAdd : ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E,
      PreparedParam.projectiveValue (p * q).left =
        PreparedParam.projectiveValue p.left + PreparedParam.projectiveValue q.left) :
    (η[projectiveTarget E]).left = weierstrassOrigin E := by
  let X := projectiveTarget E
  let p : AbVar.ptObj (K := ℚ) ℂ ⟶ X := 1
  have h := hAdd p p
  rw [show p * p = p from mul_one p] at h
  have hp : PreparedParam.projectiveValue p.left = 0 := by
    have he : PreparedParam.projectiveValue p.left + 0 =
        PreparedParam.projectiveValue p.left + PreparedParam.projectiveValue p.left := by
      rwa [add_zero]
    exact (add_left_cancel he).symm
  let b : AbVar.ptObj (K := ℚ) ℂ ⟶ 𝟙_ (Over (Spec (.of ℚ))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) (maps_to_rat_unique _ _)
  have hb : b ≫ η[X] = p := MonObj.comp_one b
  let e : Spec (.of ℚ) ⟶ Proj E.toProjective.grading := (η[projectiveTarget E]).left
  let o : Spec (.of ℚ) := default
  have hs : e o = pointO E := by
    have ho := (projectiveValue_eq_zero_iff p.left).mp hp
    rw [← hb, Over.comp_left] at ho
    change (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) ≫ e) default = pointO E at ho
    rw [Scheme.Hom.comp_apply, Subsingleton.elim (Spec.map _ default) o] at ho
    exact ho
  change e = weierstrassOrigin E
  apply (projectiveValue_bijective E ℚ).1
  rw [(projectiveValue_eq_zero_iff e).mpr hs,
    (projectiveValue_eq_zero_iff (weierstrassOrigin E)).mpr (weierstrassOrigin_point E)]


section Vectors

variable (E : WeierstrassCurve ℚ)
variable {v : Fin 3 → ℂ} (hv : (E.baseChange ℂ).toProjective.Equation v)

private def vectorEval : E.toProjective.CoordinateRing →+* ℂ :=
  E.toProjective.evalHom (algebraMap ℚ ℂ) hv

private theorem vectorEval_coord (i : Fin 3) : vectorEval E hv (E.toProjective.coord i) = v i :=
  congrFun (E.toProjective.evalHom_comp_coord _ hv) i

private def vectorOnChart (i : Fin 3) (hi : v i ≠ 0) :
    Spec (.of ℂ) ⟶ Proj E.toProjective.grading :=
  onChart E i (evalAway _ (vectorEval E hv) (by rwa [vectorEval_coord]))

private theorem evalAway_overlap {f g : E.toProjective.CoordinateRing}
    (hf : f ∈ E.toProjective.grading (1 : ℕ))
    (hg : g ∈ E.toProjective.grading (1 : ℕ))
    (k : E.toProjective.CoordinateRing →+* ℂ)
    (hf' : k f ≠ 0) (hg' : k g ≠ 0)
    {w : E.toProjective.CoordinateRing} (hw : w = f * g) :
    (evalAway w k (by rw [hw, map_mul]; exact mul_ne_zero hf' hg')).comp
        (awayMap E.toProjective.grading hg hw) = evalAway f k hf' := by
  ext s
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective E.toProjective.grading hf s
  simp only [RingHom.comp_apply, awayMap_mk]
  rw [evalAway_mk _ _ _ (hw ▸ SetLike.mul_mem_graded hf hg), evalAway_mk _ _ _ hf, hw,
    map_mul, map_pow, map_mul, mul_pow]
  field_simp

private theorem vectorOnChart_independent (i j : Fin 3) (hi : v i ≠ 0) (hj : v j ≠ 0) :
    vectorOnChart E hv i hi = vectorOnChart E hv j hj := by
  have hi' : vectorEval E hv (E.toProjective.coord i) ≠ 0 := by rwa [vectorEval_coord]
  have hj' : vectorEval E hv (E.toProjective.coord j) ≠ 0 := by rwa [vectorEval_coord]
  have ei := evalAway_overlap E (E.toProjective.coord_mem_grading i)
    (E.toProjective.coord_mem_grading j) (vectorEval E hv) hi' hj' rfl
  have ej := evalAway_overlap E (E.toProjective.coord_mem_grading j)
    (E.toProjective.coord_mem_grading i) (vectorEval E hv) hj' hi' (mul_comm _ _)
  unfold vectorOnChart onChart
  rw [← ei, ← ej]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

private theorem exists_nonzero_coord (hn : v ≠ 0) : ∃ i, v i ≠ 0 := by
  by_contra! hz
  exact hn (funext hz)

/-- The scheme point of a nonzero coordinate vector satisfying the fixed
homogeneous equation. The choice of a nonzero coordinate does not matter. -/
def projectiveVectorPoint (hn : v ≠ 0) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E :=
  let i := (exists_nonzero_coord hn).choose
  Over.homMk (vectorOnChart E hv i (exists_nonzero_coord hn).choose_spec)
    (maps_to_rat_unique _ _)

private theorem projectiveVectorPoint_left (hn : v ≠ 0) (i : Fin 3) (hi : v i ≠ 0) :
    (projectiveVectorPoint E hv hn).left = vectorOnChart E hv i hi :=
  vectorOnChart_independent E hv _ i (exists_nonzero_coord hn).choose_spec hi

theorem projectiveValue_vector_affine [E.IsElliptic] (hn : v ≠ 0) (hz : v 2 ≠ 0)
    (h : (E.baseChange ℂ).toAffine.Nonsingular (v 0 / v 2) (v 1 / v 2)) :
    projectiveValue (projectiveVectorPoint E hv hn).left =
      .some (v 0 / v 2) (v 1 / v 2) h := by
  rw [projectiveVectorPoint_left E hv hn 2 hz]
  let p := vectorOnChart E hv 2 hz
  have hp : p default ≠ pointO E := zOpen_ne_origin.mp (by
    change ((Proj.basicOpenIsoSpec _ _ (E.toProjective.coord_mem_grading 2) (by decide)).inv
      (Spec.map (CommRingCat.ofHom _) default)).1 ∈ _
    exact Subtype.property _)
  let g := evalAway (E.toProjective.coord 2) (vectorEval E hv) (by rwa [vectorEval_coord])
  have hring : zRingMap (pointInZ p hp) =
    { toRingHom := g.comp (affineEquivZChart E).toRingHom
      commutes' := fun a => DFunLike.congr_fun
        (Subsingleton.elim (((g.comp (affineEquivZChart E).toRingHom).comp
          (algebraMap ℚ E.toAffine.CoordinateRing))) (algebraMap ℚ ℂ)) a } := by
    have hh : pointInZ p hp =
        Spec.map (CommRingCat.ofHom (g.comp (affineEquivZChart E).toRingHom)) := by
      apply (cancel_mono ((zIso E).inv ≫ (zOpen E).ι)).mp
      rw [pointInZ_factor p hp]
      let a := (affineEquivZChart E).toCommRingCatIso
      let b := Proj.basicOpenIsoSpec _ _ (E.toProjective.coord_mem_grading 2) zero_lt_one
      change p = Spec.map (a.hom ≫ CommRingCat.ofHom g) ≫
        (Spec.map a.inv ≫ b.inv) ≫ (zOpen E).ι
      simp only [Spec.map_comp, Category.assoc]
      rw [← Category.assoc (Spec.map a.hom) (Spec.map a.inv), ← Spec.map_comp,
        a.inv_hom_id, Spec.map_id, Category.id_comp] <;> rfl
    rw [hh]
    apply AlgHom.toRingHom_injective
    change (zRingMap _).toRingHom = g.comp (affineEquivZChart E).toRingHom
    rw [zRingMap_toRingHom]
    exact congrArg CommRingCat.Hom.hom (Spec.homEquiv.apply_symm_apply _)
  change projectiveValue p = _
  rw [value_ne_origin p hp]
  congr 1
  · rw [hring]
    change g (affineToZChart E (AdjoinRoot.of _ Polynomial.X)) = _
    rw [affineToZChart_of_X, zChartX, evalAway_mk _ _ _ (E.toProjective.coord_mem_grading 2)]
    simp [vectorEval_coord]
  · rw [hring]
    change g (affineToZChart E (AdjoinRoot.root _)) = _
    rw [affineToZChart_root, zChartY, evalAway_mk _ _ _ (E.toProjective.coord_mem_grading 2)]
    simp [vectorEval_coord]

theorem projectiveValue_vector_origin [E.IsElliptic] (hn : v ≠ 0)
    (hx : v 0 = 0) (hz : v 2 = 0) :
    projectiveValue (projectiveVectorPoint E hv hn).left = 0 := by
  classical
  have hy : v 1 ≠ 0 := by
    intro hy
    apply hn
    funext i
    fin_cases i <;> assumption
  rw [projectiveVectorPoint_left E hv hn 1 hy, projectiveValue]
  refine dite_eq_left (eq_pointO_of_coord_mem E _ ?_ ?_)
  · rw [vectorOnChart, chart_mem_iff E 1 _ 1 _ (by simpa using E.toProjective.coord_mem_grading 0),
      evalAway_mk _ _ _ (E.toProjective.coord_mem_grading 1), vectorEval_coord, hx, zero_div]
  · rw [vectorOnChart, chart_mem_iff E 1 _ 1 _ (by simpa using E.toProjective.coord_mem_grading 2),
      evalAway_mk _ _ _ (E.toProjective.coord_mem_grading 1), vectorEval_coord, hz, zero_div]

/-- The complex points of the fixed Proj model vary continuously with
nonzero coordinate vectors in its homogeneous equation. -/
theorem tendsto_projectiveVectorPoint {I : Type} {l : Filter I} (P : I → Fin 3 → ℂ)
    (hP : ∀ t, (E.baseChange ℂ).toProjective.Equation (P t)) (hPn : ∀ t, P t ≠ 0)
    (hn : v ≠ 0) (hl : ∀ i, Tendsto (fun t => P t i) l (𝓝 (v i))) :
    Tendsto (fun t => complexLift (projectiveVectorPoint E (hP t) (hPn t))) l
      (𝓝 (complexLift (projectiveVectorPoint E hv hn))) := by
  classical
  obtain ⟨i, hi⟩ := exists_nonzero_coord hn
  let R := coordAway E i
  let j : Spec (.of R) ⟶ Proj E.toProjective.grading :=
    Proj.awayι _ _ (E.toProjective.coord_mem_grading i) zero_lt_one
  letI : Algebra ℚ R := (Spec.homEquiv (j ≫ projectiveOverQ E)).hom.toAlgebra
  let jQ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ R))) ⟶ projectiveTarget E :=
    Over.homMk j (Spec.map_preimage _).symm
  let g := evalAway (E.toProjective.coord i) (vectorEval E hv) (by rwa [vectorEval_coord])
  let f (t : I) : R →+* ℂ := if ht : P t i ≠ 0 then
    evalAway (E.toProjective.coord i) (vectorEval E (hP t))
      (by rwa [vectorEval_coord]) else g
  have htail : ∀ᶠ t in l, P t i ≠ 0 := (hl i) (isOpen_ne.mem_nhds hi)
  have heval (a : E.toProjective.CoordinateRing) :
      Tendsto (fun t => vectorEval E (hP t) a) l (𝓝 (vectorEval E hv a)) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Tendsto (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℂ) (P t) p) l
      (𝓝 (MvPolynomial.eval₂ (algebraMap ℚ ℂ) v p))
    induction p using MvPolynomial.induction_on with
    | C c => simpa using (tendsto_const_nhds : Tendsto (fun _ : I => (c : ℂ)) l (𝓝 (c : ℂ)))
    | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
    | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (hl i)
  have hh (s : R) : Tendsto (fun t => f t s) l (𝓝 (g s)) := by
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective E.toProjective.grading (E.toProjective.coord_mem_grading i) s
    dsimp only [g]
    rw [evalAway_mk _ _ _ (E.toProjective.coord_mem_grading i), vectorEval_coord]
    refine ((heval a).div ((hl i).pow n) (pow_ne_zero _ hi)).congr' ?_
    filter_upwards [htail] with t ht
    dsimp only [f]
    rw [dite_eq_left ht, evalAway_mk _ _ _ (E.toProjective.coord_mem_grading i), vectorEval_coord]
    rfl
  have hlim := (Point.continuous_map (complexBaseChange.map jQ)).continuousAt.tendsto.comp
    (tendsto_specPoint f g hh)
  let q (k : R →+* ℂ) : AbVar.ptObj (K := ℚ) ℂ ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ R))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom k)) (maps_to_rat_unique _ _)
  change Tendsto (fun t => Point.map (complexBaseChange.map jQ) (complexLift (q (f t)))) l
    (𝓝 (Point.map (complexBaseChange.map jQ) (complexLift (q g)))) at hlim
  have hg : q g ≫ jQ = projectiveVectorPoint E hv hn :=
    Over.OverMorphism.ext ((projectiveVectorPoint_left E hv hn i hi).symm)
  rw [← complexLift_comp, hg] at hlim
  refine hlim.congr' ?_
  filter_upwards [htail] with t ht
  rw [← complexLift_comp]
  congr 1
  apply Over.OverMorphism.ext
  rw [projectiveVectorPoint_left E (hP t) (hPn t) i ht]
  change (Spec.map (CommRingCat.ofHom (f t))) ≫ j = _
  dsimp only [f]
  rw [dite_eq_left ht] <;> rfl


end Vectors

end ZInQ.Manuscript.RC.J0Cusps
