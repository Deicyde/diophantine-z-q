import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import Mathlib.AlgebraicGeometry.ResidueField

/-! Read the affine chart of the fixed projective Weierstrass model,
and identify field points by their readings. Tex 2943–2946, on the spot (c). -/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.AtkinRational

variable (E : WeierstrassCurve ℚ)

abbrev ellipticAffineOpen := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)

def ellipticAffineIso : (ellipticAffineOpen E).toScheme ≅ Spec (.of E.toAffine.CoordinateRing) :=
  Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
      (E.toProjective.coord_mem_grading 2) (by norm_num) ≪≫
    (Scheme.Spec.mapIso (affineEquivZChart E).toCommRingCatIso.op)

def ellipticAffineInclusion : Spec (.of E.toAffine.CoordinateRing) ⟶
    Proj E.toProjective.grading :=
  (ellipticAffineIso E).inv ≫ (ellipticAffineOpen E).ι

instance : IsOpenImmersion (ellipticAffineInclusion E) := by
  unfold ellipticAffineInclusion
  infer_instance

theorem range_ellipticAffineInclusion :
    Set.range (ellipticAffineInclusion E) = ellipticAffineOpen E := by
  rw [ellipticAffineInclusion]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((ellipticAffineIso E).inv y).property
  · intro hx
    obtain ⟨y, hy⟩ := (ellipticAffineIso E).inv.homeomorph.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem mem_ellipticAffineOpen_iff (p : Proj E.toProjective.grading) :
    p ∈ ellipticAffineOpen E ↔ p ≠ pointO E := by
  constructor
  · intro h hp
    subst p
    exact ((Proj.mem_basicOpen _ _ _).1 h)
      ((mem_pointO_iff E (E.toProjective.coord_mem_grading 2)).2 (by rw [evalZero_coord]; rfl))
  · intro h
    exact (Proj.mem_basicOpen _ _ _).2 fun hz =>
      h (eq_pointO_of_coord_mem E p (coord_zero_mem_of_coord_two_mem E p hz) hz)

def ellipticAffineLift {S : Scheme.{0}} (u : S ⟶ Proj E.toProjective.grading)
    (hu : Set.range u ⊆ ellipticAffineOpen E) : S ⟶ Spec (.of E.toAffine.CoordinateRing) :=
  IsOpenImmersion.lift (ellipticAffineOpen E).ι u (hu.trans Subtype.range_val.ge) ≫
    (ellipticAffineIso E).hom

@[reassoc (attr := simp)]
theorem ellipticAffineLift_fac {S : Scheme.{0}} (u : S ⟶ Proj E.toProjective.grading)
    (hu : Set.range u ⊆ ellipticAffineOpen E) :
    ellipticAffineLift E u hu ≫ ellipticAffineInclusion E = u := by
  simp [ellipticAffineLift, ellipticAffineInclusion]

def affineRingMap {R : Type} [CommRing R] [Algebra ℚ R]
    (u : Spec (.of R) ⟶ Spec (.of E.toAffine.CoordinateRing)) :
    E.toAffine.CoordinateRing →ₐ[ℚ] R where
  __ := ((Scheme.ΓSpecIso _).inv ≫ u.appTop ≫ (Scheme.ΓSpecIso _).hom).hom
  commutes' r := DFunLike.congr_fun
    (RingHom.ext_rat (((Scheme.ΓSpecIso _).inv ≫ u.appTop ≫ (Scheme.ΓSpecIso _).hom).hom.comp
      (algebraMap ℚ E.toAffine.CoordinateRing)) (algebraMap ℚ R)) r

@[simp] theorem affineRingMap_Spec {R : Type} [CommRing R] [Algebra ℚ R]
    (f : E.toAffine.CoordinateRing →ₐ[ℚ] R) :
    affineRingMap E (Spec.map (CommRingCat.ofHom f.toRingHom)) = f := by
  apply AlgHom.toRingHom_injective
  change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso _).hom).hom = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

theorem affineRingMap_injective {R : Type} [CommRing R] [Algebra ℚ R] :
    Function.Injective (affineRingMap E (R := R)) := by
  intro u v h
  obtain ⟨a, rfl⟩ := Spec.map_surjective u
  obtain ⟨b, rfl⟩ := Spec.map_surjective v
  let a' : E.toAffine.CoordinateRing →ₐ[ℚ] R :=
    { __ := a.hom, commutes' := DFunLike.congr_fun <|
      (RingHom.ext_rat (a.hom.comp (algebraMap ℚ E.toAffine.CoordinateRing)) (algebraMap ℚ R)) }
  let b' : E.toAffine.CoordinateRing →ₐ[ℚ] R :=
    { __ := b.hom, commutes' := DFunLike.congr_fun <|
      (RingHom.ext_rat (b.hom.comp (algebraMap ℚ E.toAffine.CoordinateRing)) (algebraMap ℚ R)) }
  change affineRingMap E (Spec.map (CommRingCat.ofHom a'.toRingHom)) =
    affineRingMap E (Spec.map (CommRingCat.ofHom b'.toRingHom)) at h
  simp only [affineRingMap_Spec] at h
  exact congrArg (fun f : E.toAffine.CoordinateRing →ₐ[ℚ] R =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h

theorem projectiveValue_eq_some_of_affine [E.IsElliptic] {F : Type} [Field F] [Algebra ℚ F]
    (u : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (hu : Set.range u ⊆ ellipticAffineOpen E) :
    let a := affineRingMap E (ellipticAffineLift E u hu)
    projectiveValue u = .some (a (AdjoinRoot.of E.toAffine.polynomial Polynomial.X))
      (a (AdjoinRoot.root E.toAffine.polynomial))
      (Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom a)) := by
  have h := (mem_ellipticAffineOpen_iff E _).1 (hu (Set.mem_range_self default))
  simp only [projectiveValue, dite_eq_right h]
  rfl

theorem projectiveValue_affine_spec [E.IsElliptic] {F : Type} [Field F] [Algebra ℚ F]
    (a : E.toAffine.CoordinateRing →ₐ[ℚ] F) :
    projectiveValue (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ ellipticAffineInclusion E) =
      .some (a (AdjoinRoot.of E.toAffine.polynomial Polynomial.X))
        (a (AdjoinRoot.root E.toAffine.polynomial))
        (Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom a)) := by
  have hu : Set.range (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ ellipticAffineInclusion E) ⊆
      ellipticAffineOpen E := by
    rw [← range_ellipticAffineInclusion]
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have h := projectiveValue_eq_some_of_affine E _ hu
  dsimp only at h
  have hs : ellipticAffineLift E _ hu = Spec.map (CommRingCat.ofHom a.toRingHom) := by
    rw [← cancel_mono (ellipticAffineInclusion E), ellipticAffineLift_fac]
  simpa only [hs, affineRingMap_Spec] using h

theorem projectiveValue_eq_zero_iff [E.IsElliptic] {F : Type} [Field F] [Algebra ℚ F]
    (u : Spec (.of F) ⟶ Proj E.toProjective.grading) :
    projectiveValue u = 0 ↔ u default = pointO E := by
  classical
  unfold projectiveValue
  split <;> simp_all

theorem projectiveValue_eq_of_affine [E.IsElliptic] {F : Type} [Field F] [Algebra ℚ F]
    (u v : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (hu : Set.range u ⊆ ellipticAffineOpen E) (hv : Set.range v ⊆ ellipticAffineOpen E)
    (h : projectiveValue u = projectiveValue v) : u = v := by
  rw [projectiveValue_eq_some_of_affine E u hu, projectiveValue_eq_some_of_affine E v hv] at h
  have ⟨hx, hy⟩ := Affine.Point.some.inj h
  have he := affineRingMap_injective E (Affine.CoordinateRing.algHom_ext hx hy)
  rw [← ellipticAffineLift_fac E u hu, ← ellipticAffineLift_fac E v hv, he]

private theorem uniq_homs_of_rat_embedding {K F : Type} [Field K] [Field F]
    (a : K →+* ℚ) (b c : K →+* F) : b = c := by
  let : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℚ) (by
    simpa only [map_natCast] using congrArg a h)⟩
  have hs : Function.Surjective (Rat.castHom K) := fun x =>
    ⟨a x, a.injective (by simp [map_ratCast])⟩
  exact RingHom.ext fun x => by
    obtain ⟨r, rfl⟩ := hs x
    exact DFunLike.congr_fun (RingHom.ext_rat (b.comp (Rat.castHom K)) (c.comp (Rat.castHom K))) r

/-- The point reading on the fixed projective model is faithful once its
rational origin is supplied. The affine coordinates determine a ring map.
At the origin its rational point gives an embedding of the residue field
into `ℚ`, so any embedding into the point field is unique. -/
theorem projectiveValue_injective_of_origin [E.IsElliptic]
    (o : Spec (.of ℚ) ⟶ Proj E.toProjective.grading) (ho : projectiveValue o = 0)
    {F : Type} [Field F] [Algebra ℚ F] :
    Function.Injective (projectiveValue (E := E) (F := F)) := by
  intro u v h
  by_cases h0 : projectiveValue u = 0
  · let Y := Proj E.toProjective.grading
    let eU := Scheme.SpecToEquivOfField F Y u
    let eV := Scheme.SpecToEquivOfField F Y v
    let eO := Scheme.SpecToEquivOfField ℚ Y o
    have hU : eU.1 = pointO E := by
      change u (IsLocalRing.closedPoint F) = _
      rw [Subsingleton.elim (IsLocalRing.closedPoint F : Spec (.of F)) (default : Spec (.of F))]
      exact (projectiveValue_eq_zero_iff E u).1 h0
    have hV : eV.1 = pointO E := by
      change v (IsLocalRing.closedPoint F) = _
      rw [Subsingleton.elim (IsLocalRing.closedPoint F : Spec (.of F)) (default : Spec (.of F))]
      exact (projectiveValue_eq_zero_iff E v).1 (h.symm.trans h0)
    have hO : eO.1 = pointO E := by
      change o (IsLocalRing.closedPoint ℚ) = _
      rw [Subsingleton.elim (IsLocalRing.closedPoint ℚ : Spec (.of ℚ)) (default : Spec (.of ℚ))]
      exact (projectiveValue_eq_zero_iff E o).1 ho
    apply (Scheme.SpecToEquivOfField F Y).injective
    change eU = eV
    refine Scheme.SpecToEquivOfField_eq_iff.mpr ⟨hU.trans hV.symm, ?_⟩
    apply CommRingCat.hom_ext
    exact uniq_homs_of_rat_embedding
      (((Y.residueFieldCongr (hU.trans hO.symm)).hom ≫ eO.2).hom) _ _
  · have mem (t : Spec (.of F) ⟶ Proj E.toProjective.grading) (ht : projectiveValue t ≠ 0) :
        Set.range t ⊆ ellipticAffineOpen E := by
      rintro _ ⟨x, rfl⟩
      rw [Subsingleton.elim x (default : Spec (.of F))]
      apply (mem_ellipticAffineOpen_iff E _).2
      exact mt (projectiveValue_eq_zero_iff E t).2 ht
    exact projectiveValue_eq_of_affine E u v (mem u h0) (mem v (h ▸ h0)) h

/-- Affine coordinates realize every nonzero point, with zero supplied by
base change of the rational origin. -/
theorem projectiveValue_surjective_of_origin [E.IsElliptic]
    (o : Spec (.of ℚ) ⟶ Proj E.toProjective.grading) (ho : projectiveValue o = 0)
    {F : Type} [Field F] [Algebra ℚ F] :
    Function.Surjective (projectiveValue (E := E) (F := F)) := by
  intro P
  cases P with
  | zero =>
    let ι := Algebra.ofId ℚ F
    refine ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ o, ?_⟩
    rw [← projectiveValue_map ι o, ho, map_zero]
    rfl
  | some x y h =>
    let a : E.toAffine.CoordinateRing →ₐ[ℚ] F := Affine.CoordinateRing.evalAlgHom h.1
    refine ⟨Spec.map (CommRingCat.ofHom a.toRingHom) ≫ ellipticAffineInclusion E, ?_⟩
    rw [projectiveValue_affine_spec]
    simp only [a, Affine.CoordinateRing.evalAlgHom_of_X, Affine.CoordinateRing.evalAlgHom_root]


end ZInQ.Manuscript.RC.AtkinRational
