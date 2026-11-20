import AllFieldNativeCube
import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudR2Poincare.L5.C1MultiplicativeSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L2.SeesawFiniteness
import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmpleBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

open PkgI3 ZInQ.Contrib.CloudR2Poincare

universe u

private theorem tr_eq_translate {k : Type} [Field k] {X : AbVar k} (x : AC.Kpt X) :
    AC.tr x = L1.translate X.X x := by
  have : IsCommMonObj X.X := isCommMonObj_of_isProper_of_geometricallyIntegral X.X
  rw [L1.translate, mul_comm, CategoryTheory.Hom.mul_def]
  rfl

theorem native_square : MumfordSquareAC := by
  intro k _ _ X c x y
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
  let a := toUnit X.X ≫ x
  let b := toUnit X.X ≫ y
  have Ha : Scheme.Pic.map a.left c = 1 := by
    change Scheme.Pic.map ((toUnit X.X ≫ x).left) c = 1
    rw [Over.comp_left]
    exact L6.pic_map_comp_eq_one _ _ _
  have Hb : Scheme.Pic.map b.left c = 1 := by
    change Scheme.Pic.map ((toUnit X.X ≫ y).left) c = 1
    rw [Over.comp_left]
    exact L6.pic_map_comp_eq_one _ _ _
  have Hab : a * b = toUnit X.X ≫ (x * y) := (MonObj.comp_mul _ _ _).symm
  have Hmap : Scheme.Pic.map (a * b).left c = 1 := by
    rw [Hab, Over.comp_left]
    exact L6.pic_map_comp_eq_one _ _ _
  have Hx : 𝟙 X.X * a = AC.tr x := rfl
  have Hy : 𝟙 X.X * b = AC.tr y := rfl
  have Hxy : 𝟙 X.X * a * b = AC.tr (x * y) := by
    rw [_root_.mul_assoc, Hab]
    rfl
  have h := H5OriginalDVR.Lane2.AllFieldNativeCube.nativeCubeRelation X X.X (𝟙 _) a b c
  rw [Hxy] at h
  simpa only [Over.id_left, Scheme.Pic.map_id, Ha, Hb, Hx, Hy, Hmap, _root_.mul_one] using h

/-- For an invariant Picard class, pulling back along the product of two maps
is the tensor product of its two pullbacks. -/
theorem map_mul_of_translationInvariant {k : Type} [Field k] [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (ht : AC.IsTI c)
    {P : Over (Spec (.of k))} (f g : P ⟶ X.X) :
    Scheme.Pic.map (f * g).left c = Scheme.Pic.map f.left c * Scheme.Pic.map g.left c := by
  have ht' : L3.TranslationInvariant X c := by
    intro x
    rw [← tr_eq_translate x]
    exact ht x
  have hn := L5.mul_pullback_class_of_translationInvariant L1.ReducedGlobalNormalizedSeesaw_proof
    X c ht'
  let F := lift f g
  have hh := congrArg (Scheme.Pic.map F.left) hn
  simp only [Scheme.Pic.map_mul, ← Scheme.Pic.map_comp, ← Over.comp_left] at hh
  simpa only [F, lift_fst, lift_snd, CategoryTheory.Hom.mul_def] using hh

/-- Invertible sheaves in the translation-invariant Picard subgroup admit the
multiplication pullback formula independently of Picard representability. -/
theorem native_mul_pullback : MumfordMulNPicZeroAC := by
  intro k _ _ X c ht n
  induction n with
  | zero =>
    have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
      inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
    change Scheme.Pic.map ((𝟙 X.X : X.X ⟶ X.X) ^ 0).left c = c ^ 0
    rw [pow_zero, pow_zero, CategoryTheory.Hom.one_def, Over.comp_left]
    exact L6.pic_map_comp_eq_one _ _ _
  | succ n ih =>
    change Scheme.Pic.map ((𝟙 X.X : X.X ⟶ X.X) ^ n).left c = c ^ n at ih
    change Scheme.Pic.map ((𝟙 X.X : X.X ⟶ X.X) ^ (n + 1)).left c = c ^ (n + 1)
    rw [pow_succ, map_mul_of_translationInvariant X c ht, ih, Over.id_left, Scheme.Pic.map_id,
      pow_succ]

/-- Polarization by a line bundle takes values in the literal invariant
Picard subgroup. -/
theorem phi_is_translationInvariant {k : Type} [Field k] [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (x : AC.Kpt X) :
    AC.IsTI (AC.phi c x) := by
  intro y
  simp only [AC.phi, Scheme.Pic.map_mul, L1.pic_map_inv, ← Scheme.Pic.map_comp, ← Over.comp_left,
    AC.tr_comp_tr]
  have h := native_square k X c y x
  let u := Scheme.Pic.map (AC.tr (y * x)).left c
  let v := Scheme.Pic.map (AC.tr y).left c
  let w := Scheme.Pic.map (AC.tr x).left c
  change u * v⁻¹ = w * c⁻¹
  change u * c = v * w at h
  calc
    u * v⁻¹ = (u * c) * (c⁻¹ * v⁻¹) := by rw [_root_.mul_assoc, mul_inv_cancel_left]
    _ = (v * w) * (c⁻¹ * v⁻¹) := by rw [h]
    _ = (v * v⁻¹) * (w * c⁻¹) := by ac_rfl
    _ = w * c⁻¹ := by rw [mul_inv_cancel, _root_.one_mul]

/-- The polarization on rational points, with actual Picard classes as its target. -/
def phiHom {k : Type} [Field k] [IsAlgClosed k] (X : AbVar k) (c : X.X.left.Pic) :
    AC.Kpt X →* X.X.left.Pic where
  toFun := AC.phi c
  map_one' := by
    rw [AC.phi, tr_eq_translate, L1.translate_one, Over.id_left, Scheme.Pic.map_id, mul_inv_cancel]
  map_mul' x y := by
    simp only [AC.phi]
    have h := native_square k X c x y
    calc
      _ = (Scheme.Pic.map (AC.tr (x * y)).left c * c) * (c⁻¹ * c⁻¹) := by
        rw [_root_.mul_assoc, mul_inv_cancel_left]
      _ = _ := by rw [h]; ac_rfl

/-- A very ample invertible sheaf gives a finite kernel for this literal
polarization on points. -/
theorem finite_kernel_veryAmple {k : Type} [Field k] [IsAlgClosed k]
    (X : AbVar k) (M : X.X.left.Modules) (hM : L2.VeryAmple X.X.hom M) :
    letI : M.IsInvertible := hM.isInvertible
    {x : AC.Kpt X | AC.phi (Scheme.Pic.mk M) x = 1}.Finite := by
  let : M.IsInvertible := hM.isInvertible
  apply (L2.finite_translationStabilizer_of_globalSeesaw L1.ReducedGlobalNormalizedSeesaw_proof
    X M hM).subset
  intro x hx
  show Scheme.Pic.map (L1.translate X.X x).left (Scheme.Pic.mk M) = Scheme.Pic.mk M
  rw [← tr_eq_translate x]
  exact mul_inv_eq_one.mp hx

/-- Every abelian variety admits a very ample invertible sheaf over its own field. -/
theorem exists_veryAmple {k : Type} [Field k] (X : AbVar k) :
    ∃ M : X.X.left.Modules, L2.VeryAmple X.X.hom M := by
  obtain ⟨coords, hfinite, i, hi, he⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral X.X
  have : Finite coords := hfinite
  have : IsImmersion i := hi
  have : IsProper (i ≫ ℙ(coords; Spec (.of k)) ↘ Spec (.of k)) := by
    rw [he]
    infer_instance
  have : IsProper i := IsProper.of_comp i (ℙ(coords; Spec (.of k)) ↘ Spec (.of k))
  have hclosed : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range
  exact ⟨ProjectiveSpace.twistRestrict i 1, coords, hfinite, i, hclosed, he, ⟨Iso.refl _⟩⟩

end PicDict.DirectPairing
