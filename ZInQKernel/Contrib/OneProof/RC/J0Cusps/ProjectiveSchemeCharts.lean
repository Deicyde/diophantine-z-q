import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-! Normalized homogeneous coordinates on the affine charts of the fixed
Weierstrass Proj, and the maps out of affine schemes that they define.
On the spot (c), tex 1785–1787. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

namespace ZInQ.Manuscript.RC.J0Cusps

abbrev ProjectiveChart (E : WeierstrassCurve ℚ) (i : Fin 3) :=
  Away E.toProjective.grading (E.toProjective.coord i)

instance projectiveChartAlgebra (E : WeierstrassCurve ℚ) (i : Fin 3) :
    Algebra ℚ (ProjectiveChart E i) :=
  ((fromZeroRingHom E.toProjective.grading (Submonoid.powers (E.toProjective.coord i))).comp
    { toFun := fun r => ⟨algebraMap ℚ E.toProjective.CoordinateRing r,
        E.toProjective.mk_mem_grading (isHomogeneous_C (Fin 3) r)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }).toAlgebra

abbrev projectiveChartInclusion (E : WeierstrassCurve ℚ) (i : Fin 3) :
    Spec (.of (ProjectiveChart E i)) ⟶ (projectiveTarget E).left :=
  Proj.awayι _ _ (E.toProjective.coord_mem_grading i) zero_lt_one

def projectiveChartRatio (E : WeierstrassCurve ℚ) (i j : Fin 3) : ProjectiveChart E i :=
  Away.mk _ (E.toProjective.coord_mem_grading i) 1 _ (coord_mem_grading_smul E j)

private abbrev ChartLocalization (E : WeierstrassCurve ℚ) (i : Fin 3) :=
  Localization.Away (E.toProjective.coord i)

private def denominatorUnit (E : WeierstrassCurve ℚ) (i : Fin 3) : (ChartLocalization E i)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := ChartLocalization E i)
    (E.toProjective.coord i)).unit

private theorem denominatorUnit_val (E : WeierstrassCurve ℚ) (i : Fin 3) :
    (denominatorUnit E i : ChartLocalization E i) =
      algebraMap _ _ (E.toProjective.coord i) :=
  IsUnit.unit_spec _

private theorem chartFraction_val (E : WeierstrassCurve ℚ) (i : Fin 3) (n : ℕ)
    (a : E.toProjective.CoordinateRing) (ha : a ∈ E.toProjective.grading (n • (1 : ℕ))) :
    (Away.mk _ (E.toProjective.coord_mem_grading i) n a ha).val =
      ((denominatorUnit E i)⁻¹ : (ChartLocalization E i)ˣ).val ^ n * algebraMap _ _ a := by
  rw [Away.val_mk, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_iff_eq_mul (S := ChartLocalization E i)).2
  change algebraMap _ _ a = _ * algebraMap _ _ (E.toProjective.coord i ^ n)
  rw [map_pow, ← denominatorUnit_val E i, mul_comm (_ ^ n * _), ← mul_assoc,
    ← mul_pow, Units.mul_inv, one_pow, one_mul]

private theorem chartRatio_val (E : WeierstrassCurve ℚ) (i j : Fin 3) :
    (projectiveChartRatio E i j).val =
      ((denominatorUnit E i)⁻¹ : (ChartLocalization E i)ˣ).val *
        algebraMap _ _ (E.toProjective.coord j) := by
  simpa only [projectiveChartRatio, pow_one] using
    chartFraction_val E i 1 (E.toProjective.coord j) (coord_mem_grading_smul E j)

theorem projectiveChartRatio_self (E : WeierstrassCurve ℚ) (i : Fin 3) :
    projectiveChartRatio E i i = 1 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (E.toProjective.coord i))
  rw [chartRatio_val, ← denominatorUnit_val E i, Units.inv_mul, HomogeneousLocalization.val_one]

/-- Dehomogenizing a form of degree `n` gives the fraction with denominator
the `n`th power of the chosen coordinate. -/
theorem projectiveChart_dehomogenize (E : WeierstrassCurve ℚ) (i : Fin 3) {n : ℕ}
    (p : MvPolynomial (Fin 3) ℚ) (hp : p.IsHomogeneous n) :
    eval₂ (algebraMap ℚ (ProjectiveChart E i)) (projectiveChartRatio E i) p =
      Away.mk _ (E.toProjective.coord_mem_grading i) n (Ideal.Quotient.mk _ p)
        (by simpa using E.toProjective.mk_mem_grading hp) := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (E.toProjective.coord i))
  change algebraMap (ProjectiveChart E i) (ChartLocalization E i) _ = _
  rw [eval₂_comp_left, chartFraction_val]
  have hc : (algebraMap (ProjectiveChart E i) (ChartLocalization E i)).comp
      (algebraMap ℚ (ProjectiveChart E i)) = algebraMap ℚ (ChartLocalization E i) :=
    Subsingleton.elim _ _
  rw [hc]
  have hv : (algebraMap (ProjectiveChart E i) (ChartLocalization E i) ∘
      projectiveChartRatio E i) = fun j =>
        ((denominatorUnit E i)⁻¹ : (ChartLocalization E i)ˣ).val *
          algebraMap E.toProjective.CoordinateRing (ChartLocalization E i)
            (E.toProjective.coord j) := funext (chartRatio_val E i)
  rw [hv, eval₂_mul_left_of_isHomogeneous _ hp, mk_eq_eval₂_coord, eval₂_comp_left]
  rw [show (algebraMap E.toProjective.CoordinateRing (ChartLocalization E i)).comp
      (algebraMap ℚ E.toProjective.CoordinateRing) = algebraMap ℚ (ChartLocalization E i)
      from Subsingleton.elim _ _]
  rfl

theorem projectiveChart_equation (E : WeierstrassCurve ℚ) (i : Fin 3) :
    (E.toProjective.map (algebraMap ℚ (ProjectiveChart E i))).Equation
      (projectiveChartRatio E i) := by
  rw [Projective.equation_map_iff_aeval, aeval_def,
    projectiveChart_dehomogenize E i _ E.toProjective.isHomogeneous_polynomial]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (E.toProjective.coord i))
  rw [chartFraction_val, Ideal.Quotient.mk_singleton_self, map_zero, mul_zero, HomogeneousLocalization.val_zero]

theorem projectiveChart_ringHom_ext (E : WeierstrassCurve ℚ) (i : Fin 3)
    {R : Type} [CommRing R] (f g : ProjectiveChart E i →+* R)
    (h : ∀ j, f (projectiveChartRatio E i j) = g (projectiveChartRatio E i j)) :
    f = g := by
  ext a : 1
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective E.toProjective.grading (E.toProjective.coord_mem_grading i) a
  obtain ⟨p, hp, rfl⟩ := E.toProjective.mem_grading_iff.mp
    (show a ∈ E.toProjective.grading n by simpa using ha)
  rw [← projectiveChart_dehomogenize E i p hp, eval₂_comp_left, eval₂_comp_left]
  rw [show f.comp (algebraMap ℚ (ProjectiveChart E i)) =
      g.comp (algebraMap ℚ (ProjectiveChart E i)) from Subsingleton.elim _ _,
    show f ∘ projectiveChartRatio E i = g ∘ projectiveChartRatio E i from funext h]

private def projectiveEvalAway (E : WeierstrassCurve ℚ)
    (f : E.toProjective.CoordinateRing) {R : Type} [CommRing R]
    (g : E.toProjective.CoordinateRing →+* R) (hg : IsUnit (g f)) :
    Away E.toProjective.grading f →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hg).comp (algebraMap _ _)

private theorem projectiveEvalAway_fraction (E : WeierstrassCurve ℚ)
    (f : E.toProjective.CoordinateRing) {R : Type} [CommRing R]
    (g : E.toProjective.CoordinateRing →+* R) (hg : IsUnit (g f))
    {d : ℕ} (hf : f ∈ E.toProjective.grading d)
    (n : ℕ) (a : E.toProjective.CoordinateRing) (ha : a ∈ E.toProjective.grading (n • d)) :
    g f ^ n * projectiveEvalAway E f g hg (Away.mk _ hf n a ha) = g a := by
  simp only [projectiveEvalAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.mk_eq_mk']
  let t : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  let hu (y : Submonoid.powers f) : IsUnit (g y) := by
    obtain ⟨m, hm⟩ := y.2
    rw [← hm, map_pow]
    exact hg.pow m
  let z := (IsLocalization.lift (S := Localization.Away f) hu)
    (IsLocalization.mk' (Localization.Away f) a t)
  change g f ^ n * z = _
  have he := (IsLocalization.lift_mk'_spec (S := Localization.Away f) hu a z t).mp rfl
  simpa [t] using he.symm

/-- A solution vector with a unit coordinate defines a ring map from its
projective affine chart. -/
def projectiveChartEval (E : WeierstrassCurve ℚ) {R : Type} [CommRing R] [Algebra ℚ R]
    (v : Fin 3 → R) (hv : (E.toProjective.map (algebraMap ℚ R)).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) : ProjectiveChart E i →+* R :=
  let ev := E.toProjective.evalHom (algebraMap ℚ R) hv
  let hi' : IsUnit (ev (E.toProjective.coord i)) := by
    have h : ev (E.toProjective.coord i) = v i :=
      congrFun (E.toProjective.evalHom_comp_coord _ hv) i
    rwa [h]
  (IsLocalization.Away.lift (S := ChartLocalization E i) _ hi').comp (algebraMap _ _)

theorem projectiveChartEval_ratio (E : WeierstrassCurve ℚ) {R : Type} [CommRing R] [Algebra ℚ R]
    (v : Fin 3 → R) (hv : (E.toProjective.map (algebraMap ℚ R)).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) (j : Fin 3) :
    v i * projectiveChartEval E v hv i hi (projectiveChartRatio E i j) = v j := by
  let ev := E.toProjective.evalHom (algebraMap ℚ R) hv
  have h (k : Fin 3) : ev (E.toProjective.coord k) = v k :=
    congrFun (E.toProjective.evalHom_comp_coord _ hv) k
  have hu : IsUnit (ev (E.toProjective.coord i)) := (h i).symm ▸ hi
  have he := projectiveEvalAway_fraction E (E.toProjective.coord i) ev hu
    (E.toProjective.coord_mem_grading i) 1 (E.toProjective.coord j)
    (coord_mem_grading_smul E j)
  change ev (E.toProjective.coord i) ^ 1 *
    projectiveChartEval E v hv i hi (projectiveChartRatio E i j) = _ at he
  simpa [h] using he

/-- A vector with a unit coordinate defines a morphism on the corresponding
affine piece of the source. -/
def projectiveChartMorphism (E : WeierstrassCurve ℚ) {R : Type} [CommRing R] [Algebra ℚ R]
    (v : Fin 3 → R) (hv : (E.toProjective.map (algebraMap ℚ R)).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) :
    Spec (.of R) ⟶ (projectiveTarget E).left :=
  Spec.map (CommRingCat.ofHom (projectiveChartEval E v hv i hi)) ≫
    projectiveChartInclusion E i

/-- The affine piece of the morphism commutes with any rational algebra
map, in particular with taking the coordinates in a residue field. -/
theorem projectiveChartMorphism_map (E : WeierstrassCurve ℚ) {R S : Type}
    [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (v : Fin 3 → R) (hv : (E.toProjective.map (algebraMap ℚ R)).Equation v)
    (i : Fin 3) (hi : IsUnit (v i)) (f : R →+* S)
    (hw : (E.toProjective.map (algebraMap ℚ S)).Equation (f ∘ v)) :
    Spec.map (CommRingCat.ofHom f) ≫ projectiveChartMorphism E v hv i hi =
      projectiveChartMorphism E (f ∘ v) hw i (hi.map f) := by
  unfold projectiveChartMorphism
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply projectiveChart_ringHom_ext
  intro j
  apply (hi.map f).mul_left_cancel
  change f (v i) * f (projectiveChartEval E v hv i hi (projectiveChartRatio E i j)) = _
  rw [← map_mul, projectiveChartEval_ratio E v hv i hi j]
  exact (projectiveChartEval_ratio E (f ∘ v) hw i (hi.map f) j).symm

private theorem projectiveEvalAway_overlap (E : WeierstrassCurve ℚ)
    {f g : E.toProjective.CoordinateRing}
    (hf : f ∈ E.toProjective.grading (1 : ℕ)) (hg : g ∈ E.toProjective.grading (1 : ℕ))
    {R : Type} [CommRing R] (k : E.toProjective.CoordinateRing →+* R)
    (hf' : IsUnit (k f)) (hg' : IsUnit (k g))
    {w : E.toProjective.CoordinateRing} (hw : w = f * g) :
    (projectiveEvalAway E w k (by rw [hw, map_mul]; exact hf'.mul hg')).comp
        (awayMap E.toProjective.grading hg hw) = projectiveEvalAway E f k hf' := by
  ext s : 1
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective E.toProjective.grading hf s
  simp only [RingHom.comp_apply, awayMap_mk]
  apply ((hf'.pow n).mul (hg'.pow n)).mul_left_cancel
  calc
    _ = k (a * g ^ n) := by
      simpa only [hw, map_mul, mul_pow] using
        projectiveEvalAway_fraction E w k _ (hw ▸ SetLike.mul_mem_graded hf hg) n
          (a * g ^ n) _
    _ = _ := by
      rw [map_mul, map_pow, mul_comm (k f ^ n), mul_assoc, projectiveEvalAway_fraction]
      ac_rfl

/-- Changing the unit coordinate used in the target produces the very
same morphism to Proj. -/
theorem projectiveChartMorphism_independent (E : WeierstrassCurve ℚ)
    {R : Type} [CommRing R] [Algebra ℚ R] (v : Fin 3 → R)
    (hv : (E.toProjective.map (algebraMap ℚ R)).Equation v)
    (i j : Fin 3) (hi : IsUnit (v i)) (hj : IsUnit (v j)) :
    projectiveChartMorphism E v hv i hi = projectiveChartMorphism E v hv j hj := by
  let k := E.toProjective.evalHom (algebraMap ℚ R) hv
  have hi' : IsUnit (k (E.toProjective.coord i)) := by
    have h : k (E.toProjective.coord i) = v i :=
      congrFun (E.toProjective.evalHom_comp_coord _ hv) i
    rwa [h]
  have hj' : IsUnit (k (E.toProjective.coord j)) := by
    have h : k (E.toProjective.coord j) = v j :=
      congrFun (E.toProjective.evalHom_comp_coord _ hv) j
    rwa [h]
  have ei := projectiveEvalAway_overlap E (E.toProjective.coord_mem_grading i)
    (E.toProjective.coord_mem_grading j) k hi' hj' rfl
  have ej := projectiveEvalAway_overlap E (E.toProjective.coord_mem_grading j)
    (E.toProjective.coord_mem_grading i) k hj' hi' (mul_comm _ _)
  change Spec.map (CommRingCat.ofHom (projectiveEvalAway E _ k hi')) ≫
    projectiveChartInclusion E i = Spec.map (CommRingCat.ofHom (projectiveEvalAway E _ k hj')) ≫
    projectiveChartInclusion E j
  rw [← ei, ← ej]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

private theorem zChartInclusion_point_ne_origin (E : WeierstrassCurve ℚ)
    {F : Type} [Field F] (f : ProjectiveChart E 2 →+* F) :
    (Spec.map (CommRingCat.ofHom f) ≫ projectiveChartInclusion E 2) default ≠ pointO E := by
  intro e
  have h : (Spec.map (CommRingCat.ofHom f) ≫ projectiveChartInclusion E 2) default ∈
    Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := by
    change ((Proj.basicOpenIsoSpec _ _ (E.toProjective.coord_mem_grading 2) zero_lt_one).inv
      (Spec.map (CommRingCat.ofHom f) default)).1 ∈ _
    exact Subtype.property _
  rw [e, Proj.mem_basicOpen] at h
  apply h
  rw [mem_pointO_iff E (E.toProjective.coord_mem_grading 2)]
  simp


private theorem chartCoord_mem_iff {F : Type} [Field F] (E : WeierstrassCurve ℚ)
    (i j : Fin 3) (g : ProjectiveChart E i →+* F) :
    E.toProjective.coord j ∈
        ((Spec.map (CommRingCat.ofHom g) ≫ projectiveChartInclusion E i) default).asHomogeneousIdeal
      ↔ g (projectiveChartRatio E i j) = 0 := by
  let A := E.toProjective.grading
  let f := E.toProjective.coord i
  let d := E.toProjective.coord_mem_grading i
  let b := Proj.basicOpenIsoSpec A f d zero_lt_one
  let x := b.inv (Spec.map (CommRingCat.ofHom g) default)
  have he : (Proj.basicOpenToSpec A f).toLRSHom = ProjectiveSpectrum.Proj.toSpec A f := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply A x
    ⟨1 • (1 : ℕ), ⟨E.toProjective.coord j, coord_mem_grading_smul E j⟩,
      ⟨f ^ 1, SetLike.pow_mem_graded 1 d⟩, ⟨1, rfl⟩⟩
  rw [← he] at h
  change _ ∈ ((Proj.basicOpenToSpec A f) x).asIdeal ↔ _ at h
  have hx : Proj.basicOpenToSpec A f x = Spec.map (CommRingCat.ofHom g) default := by
    change b.hom (b.inv _) = _
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hx] at h
  refine h.symm.trans ?_
  change projectiveChartRatio E i j ∈ ((Spec.map (CommRingCat.ofHom g)) default).asIdeal ↔ _
  rw [Spec.map_apply]
  change projectiveChartRatio E i j ∈ (default : Spec (.of F)).asIdeal.comap g ↔ _
  rw [Ideal.mem_comap, Scheme.default_asIdeal, Ideal.mem_bot]

/-- The normalized projective vector attached via a chart computes the
existing field point evaluation, including at infinity. -/
theorem projectiveValue_chartMorphism (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {F : Type} [Field F] [Algebra ℚ F] (v : Fin 3 → F)
    (hv : (E.baseChange F).toProjective.Nonsingular v) (i : Fin 3) (hi : IsUnit (v i)) :
    PreparedParam.projectiveValue (projectiveChartMorphism E v hv.1 i hi) =
      Projective.Point.toAffine (E.baseChange F).toProjective v := by
  classical
  by_cases hz : v 2 = 0
  · rw [Projective.Point.toAffine_of_Z_eq_zero hz]
    apply (projectiveValue_eq_zero_iff _).2
    apply eq_pointO_of_coord_mem E
    · apply (chartCoord_mem_iff E i 0 _).2
      apply hi.mul_left_cancel
      rw [mul_zero]
      exact (projectiveChartEval_ratio E v hv.1 i hi 0).trans (Projective.X_eq_zero_of_Z_eq_zero hv.1 hz)
    · apply (chartCoord_mem_iff E i 2 _).2
      apply hi.mul_left_cancel
      rw [mul_zero]
      exact (projectiveChartEval_ratio E v hv.1 i hi 2).trans hz
  · rw [projectiveChartMorphism_independent E v hv.1 i 2 hi (isUnit_iff_ne_zero.mpr hz),
      Projective.Point.toAffine_of_Z_ne_zero hv hz]
    let f := projectiveChartEval E v hv.1 2 (isUnit_iff_ne_zero.mpr hz)
    let p := Spec.map (CommRingCat.ofHom f) ≫ projectiveChartInclusion E 2
    have hp : p default ≠ pointO E := zChartInclusion_point_ne_origin E f
    change PreparedParam.projectiveValue p = _
    simp only [PreparedParam.projectiveValue, dite_eq_right hp]
    let U := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
    let b := Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
      (E.toProjective.coord_mem_grading 2) zero_lt_one
    let a := (affineEquivZChart E).toCommRingCatIso
    have hchart (h : Set.range p ⊆ Set.range U.ι) :
        IsOpenImmersion.lift U.ι p h ≫ b.hom ≫ Spec.map a.hom =
          Spec.map (a.hom ≫ CommRingCat.ofHom f) := by
      have eq : IsOpenImmersion.lift U.ι p h = Spec.map (CommRingCat.ofHom f) ≫ b.inv := by
        apply (cancel_mono U.ι).1
        rw [IsOpenImmersion.lift_fac]
        rfl
      rw [eq, Category.assoc, Iso.inv_hom_id_assoc, Spec.map_comp]
    rw [Affine.Point.some.injEq]
    have hratio (j : Fin 3) : f (projectiveChartRatio E 2 j) = v j / v 2 := by
      rw [eq_div_iff hz, mul_comm]
      exact projectiveChartEval_ratio E v hv.1 2 (isUnit_iff_ne_zero.mpr hz) j
    have ringEq (h : Set.range p ⊆ Set.range U.ι) :
        (Scheme.ΓSpecIso (.of E.toAffine.CoordinateRing)).inv ≫
          (IsOpenImmersion.lift U.ι p h ≫ b.hom ≫ Spec.map a.hom).appTop ≫
          (Scheme.ΓSpecIso (.of F)).hom =
        a.hom ≫ CommRingCat.ofHom f := by
      rw [hchart]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    constructor
    · change (((Scheme.ΓSpecIso _).inv ≫ (IsOpenImmersion.lift U.ι p _ ≫
            b.hom ≫ Spec.map a.hom).appTop ≫ (Scheme.ΓSpecIso _).hom).hom)
          (AdjoinRoot.of E.toAffine.polynomial Polynomial.X) = _
      rw [ringEq]
      change f (affineToZChart E (AdjoinRoot.of _ Polynomial.X)) = _
      rw [affineToZChart_of_X]
      exact hratio 0
    · change (((Scheme.ΓSpecIso _).inv ≫ (IsOpenImmersion.lift U.ι p _ ≫
            b.hom ≫ Spec.map a.hom).appTop ≫ (Scheme.ΓSpecIso _).hom).hom)
          (AdjoinRoot.root E.toAffine.polynomial) = _
      rw [ringEq]
      change f (affineToZChart E (AdjoinRoot.root _)) = _
      rw [affineToZChart_root]
      exact hratio 1

theorem projectiveValue_fromChart (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {F : Type} [Field F] [Algebra ℚ F] (i : Fin 3) (g : ProjectiveChart E i →+* F)
    (hn : (E.baseChange F).toProjective.Nonsingular (g ∘ projectiveChartRatio E i)) :
    PreparedParam.projectiveValue (Spec.map (CommRingCat.ofHom g) ≫ projectiveChartInclusion E i) =
      Projective.Point.toAffine _ (g ∘ projectiveChartRatio E i) := by
  let v := g ∘ projectiveChartRatio E i
  have hi : v i = 1 := by simp [v, projectiveChartRatio_self]
  have hu : IsUnit (v i) := hi ▸ isUnit_one
  have e : projectiveChartEval E v hn.1 i hu = g := by
    apply projectiveChart_ringHom_ext
    intro j
    have eq := projectiveChartEval_ratio E v hn.1 i hu j
    rwa [hi, one_mul] at eq
  have hv := projectiveValue_chartMorphism E v hn i hu
  simpa only [projectiveChartMorphism, e] using hv










end ZInQ.Manuscript.RC.J0Cusps
