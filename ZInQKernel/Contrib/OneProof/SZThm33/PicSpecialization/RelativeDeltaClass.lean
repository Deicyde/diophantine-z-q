import AllFieldNativeCube
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativePicard
import ZInQKernel.Contrib.OneProof.NeronDVR.LocalPicard
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

section Class

variable {S : Scheme.{0}} {G P Q : Over S} [GrpObj G]

/-- The line bundle of the polarization on two variable points, with its
neutral-point correction. -/
def deltaClass (x y : P ⟶ G) (L : G.left.Pic) : P.left.Pic :=
  Scheme.Pic.map (x * y).left L * Scheme.Pic.map (1 : P ⟶ G).left L *
    (Scheme.Pic.map x.left L * Scheme.Pic.map y.left L)⁻¹

@[simp] theorem deltaClass_one_left (y : P ⟶ G) (L : G.left.Pic) :
    deltaClass 1 y L = 1 := by
  rw [deltaClass, one_mul, mul_comm (Scheme.Pic.map y.left L), mul_inv_cancel]

@[simp] theorem deltaClass_one_right (x : P ⟶ G) (L : G.left.Pic) :
    deltaClass x 1 L = 1 := by simp [deltaClass]

theorem deltaClass_comm [IsCommMonObj G] (x y : P ⟶ G) (L : G.left.Pic) :
    deltaClass x y L = deltaClass y x L := by simp [deltaClass, mul_comm]

theorem map_deltaClass (a : Q ⟶ P) (x y : P ⟶ G) (L : G.left.Pic) :
    Scheme.Pic.map a.left (deltaClass x y L) = deltaClass (a ≫ x) (a ≫ y) L := by
  let φ := Scheme.Pic.mapHom a.left
  change φ (deltaClass x y L) = _
  simp only [deltaClass, map_mul, map_inv, φ, Scheme.Pic.mapHom_apply,
    ← Scheme.Pic.map_comp, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one]

set_option backward.isDefEq.respectTransparency false in
theorem map_deltaClass_baseChange {T : Scheme.{0}} (i : T ⟶ S)
    (x y : P ⟶ G) (L : G.left.Pic) :
    let F := Over.pullback i
    letI : GrpObj (F.obj G) := Functor.grpObjObj
    Scheme.Pic.map (pullback.fst P.hom i) (deltaClass x y L) =
      deltaClass (F.map x) (F.map y) (Scheme.Pic.map (pullback.fst G.hom i) L) := by
  let F := Over.pullback i
  let : GrpObj (F.obj G) := Functor.grpObjObj
  have natural (a : P ⟶ G) :
      (F.map a).left ≫ pullback.fst G.hom i = pullback.fst P.hom i ≫ a.left := by
    simp [F, Over.pullback_map_left]
  let φ := Scheme.Pic.mapHom (pullback.fst P.hom i)
  change φ (deltaClass x y L) = deltaClass (F.map x) (F.map y) _
  simp only [deltaClass, map_mul, map_inv, φ, Scheme.Pic.mapHom_apply,
    ← Scheme.Pic.map_comp, ← natural, Functor.map_mul, Functor.map_one]

end Class

section Field

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {P : Over (Spec (.of K))}

theorem deltaClass_mul_left (x z y : P ⟶ A.X) (L : A.X.left.Pic) :
    deltaClass (x * z) y L = deltaClass x y L * deltaClass z y L := by
  have : Subsingleton (𝟙_ (Over (Spec (.of K)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of K)).Pic)
  have hOne : Scheme.Pic.map (1 : P ⟶ A.X).left L = 1 := by
    rw [CategoryTheory.Hom.one_def, Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one _ _ _
  have h := H5OriginalDVR.Lane2.AllFieldNativeCube.nativeCubeRelation A P x z y L
  let c := fun (a : P ⟶ A.X) => Scheme.Pic.map a.left L
  change c (x * z * y) * c x * c z * c y = c (x * z) * c (x * y) * c (z * y) at h
  simp only [deltaClass, hOne, mul_one]
  change c (x * z * y) * (c (x * z) * c y)⁻¹ =
    (c (x * y) * (c x * c y)⁻¹) * (c (z * y) * (c z * c y)⁻¹)
  let u := c (x * z) * c y
  let v := c x * c y
  let w := c z * c y
  let d := u * v * w
  apply mul_left_cancel (a := d)
  calc
    d * (c (x * z * y) * u⁻¹) = (u * u⁻¹) * (c (x * z * y) * v * w) := by
      dsimp only [d]
      ac_rfl
    _ = c (x * z * y) * c x * c z * c y * c y := by
      rw [mul_inv_cancel, one_mul]
      dsimp only [v, w]
      ac_rfl
    _ = c (x * z) * c (x * y) * c (z * y) * c y := by rw [h]
    _ = (v * v⁻¹) * (w * w⁻¹) * (u * c (x * y) * c (z * y)) := by
      simp only [mul_inv_cancel, one_mul]
      dsimp only [u]
      ac_rfl
    _ = d * ((c (x * y) * v⁻¹) * (c (z * y) * w⁻¹)) := by
      dsimp only [d]
      ac_rfl

theorem deltaClass_pow_left_over_field (x y : P ⟶ A.X) (L : A.X.left.Pic) (n : ℕ) :
    deltaClass (x ^ n) y L = deltaClass x y L ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [pow_succ, deltaClass_mul_left A, h, pow_succ]

end Field

set_option backward.isDefEq.respectTransparency false in
/-- The generic theorem of the cube gives the integral [n]-power identity
for the normalized polarization class. The section can lie on either axis. -/
theorem deltaClass_pow_left_dvr
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {G P : Over (Spec (.of R))} [GrpObj G]
    [Smooth G.hom] [GeometricallyIntegral G.hom] [Smooth P.hom] [GeometricallyIntegral P.hom]
    [IsProper (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (s : 𝟙_ (Over (Spec (.of R))) ⟶ P) (x y : P ⟶ G)
    (hs : s ≫ x = 1 ∨ s ≫ y = 1) (L : G.left.Pic) (n : ℕ) :
    deltaClass (x ^ n) y L = deltaClass x y L ^ n := by
  let S := Spec (.of R)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F := Over.pullback j
  let : GrpObj (F.obj G) := Functor.grpObjObj
  have : IsProper (F.obj G).hom := show IsProper (pullback.snd G.hom j) from inferInstance
  have : GeometricallyIntegral (F.obj G).hom :=
    show GeometricallyIntegral (pullback.snd G.hom j) from inferInstance
  let A : PkgI3.AbVar K :=
    { X := F.obj G
      grp := Functor.grpObjObj
      proper := inferInstance
      smooth := inferInstance
      geomInt := inferInstance }
  let Lη : A.X.left.Pic := Scheme.Pic.map (pullback.fst G.hom j) L
  let C : P.left.Pic := deltaClass (x ^ n) y L * (deltaClass x y L ^ n)⁻¹
  have hK : Scheme.Pic.map (pullback.fst P.hom j) C = 1 := by
    simp only [C, ← Scheme.Pic.mapHom_apply, map_mul, map_inv, map_pow]
    simp only [Scheme.Pic.mapHom_apply, map_deltaClass_baseChange]
    change deltaClass (F.map (x ^ n)) (F.map y) Lη *
      (deltaClass (F.map x) (F.map y) Lη ^ n)⁻¹ = 1
    have hpow : F.map (x ^ n) = F.map x ^ n :=
      map_pow (Functor.homMonoidHom F) x n
    rw [hpow, deltaClass_pow_left_over_field A, mul_inv_cancel]
  have hS : Scheme.Pic.map s.left C = 1 := by
    simp only [C, ← Scheme.Pic.mapHom_apply, map_mul, map_inv, map_pow]
    simp only [Scheme.Pic.mapHom_apply, map_deltaClass, MonObj.comp_pow]
    rcases hs with h | h
    · simp only [h, one_pow, deltaClass_one_left, inv_one, mul_one]
    · simp only [h, deltaClass_one_right, one_pow, inv_one, mul_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsIntegral P.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian P.hom
  have hc : C = 1 :=
    NeronDVR.GenericFrame.pic_eq_one_of_fractionField_and_section (𝟙 S) P.hom s.left
      (Over.w s) π hπ C (by rw [Category.comp_id]; exact hK) hS
  exact mul_inv_eq_one.mp hc

end ZInQ.ToricOrthogonality
