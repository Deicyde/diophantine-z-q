import ZInQKernel.Contrib.CMSerreTateSupport.AllFieldNativeCube
import ZInQKernel.Contrib.OneProof.NeronDVR.GroupAmple
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback

/-!
# The square class for varying translations

The class includes the unit correction so it is normalized on the
identity slice. It is functorial under restriction and base change, and
the theorem of the cube makes it trivial over an abelian variety's field.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace NeronDVR

variable {S : Scheme.{u}} {G P Q : Over S} [GrpObj G]

/-- The relative square class with the constant unit factors included.
It restricts trivially when the translating point is the unit. -/
def translationSquareClass (f a : P ⟶ G) (L : G.left.Pic) : P.left.Pic :=
  Scheme.Pic.map (a * f).left L * Scheme.Pic.map (a⁻¹ * f).left L *
    Scheme.Pic.map (1 : P ⟶ G).left L ^ 2 *
    (Scheme.Pic.map f.left L ^ 2 * Scheme.Pic.map a.left L * Scheme.Pic.map a⁻¹.left L)⁻¹

@[simp]
theorem translationSquareClass_one (f : P ⟶ G) (L : G.left.Pic) :
    translationSquareClass f 1 L = 1 := by
  simp only [translationSquareClass, inv_one, one_mul, pow_two]
  group

/-- Restriction of the relative square class is restriction of its two
parameters. -/
theorem map_translationSquareClass (g : Q ⟶ P) (f a : P ⟶ G) (L : G.left.Pic) :
    Scheme.Pic.map g.left (translationSquareClass f a L) =
      translationSquareClass (g ≫ f) (g ≫ a) L := by
  have hInv : g ≫ a⁻¹ = (g ≫ a)⁻¹ := by simp [Hom.inv_def]
  let φ := Scheme.Pic.mapHom g.left
  change φ (translationSquareClass f a L) = _
  simp only [translationSquareClass, map_mul, map_pow, map_inv, φ,
    Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, ← Over.comp_left,
    MonObj.comp_mul, MonObj.comp_one, hInv]

/-- At a point of a field-valued test scheme, the cube formula for the two
inverse parameters gives the trivial relative square class. -/
theorem translationSquareClass_eq_one_of_cube
    (f a : P ⟶ G) (L : G.left.Pic)
    (hOne : Scheme.Pic.map (1 : P ⟶ G).left L = 1)
    (hCube : Scheme.Pic.map (a * a⁻¹ * f).left L * Scheme.Pic.map a.left L *
        Scheme.Pic.map a⁻¹.left L * Scheme.Pic.map f.left L =
      Scheme.Pic.map (a * a⁻¹).left L *
        Scheme.Pic.map (a * f).left L * Scheme.Pic.map (a⁻¹ * f).left L) :
    translationSquareClass f a L = 1 := by
  simp only [mul_inv_cancel, one_mul, hOne] at hCube
  have hprod : Scheme.Pic.map (a * f).left L * Scheme.Pic.map (a⁻¹ * f).left L =
      Scheme.Pic.map f.left L ^ 2 * Scheme.Pic.map a.left L * Scheme.Pic.map a⁻¹.left L := by
    rw [← hCube, pow_two]
    ac_rfl
  rw [translationSquareClass, hOne, one_pow, mul_one, hprod, mul_inv_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- Base change of the square class is the square class of the
base-changed group, parameters and line. -/
theorem map_translationSquareClass_baseChange
    {T : Scheme.{u}} (j : T ⟶ S) (f a : P ⟶ G) (L : G.left.Pic) :
    let F := Over.pullback j
    letI : GrpObj (F.obj G) := Functor.grpObjObj
    Scheme.Pic.map (pullback.fst P.hom j) (translationSquareClass f a L) =
      translationSquareClass (F.map f) (F.map a) (Scheme.Pic.map (pullback.fst G.hom j) L) := by
  let F := Over.pullback j
  let : GrpObj (F.obj G) := Functor.grpObjObj
  have natural (u₀ : P ⟶ G) :
      (F.map u₀).left ≫ pullback.fst G.hom j = pullback.fst P.hom j ≫ u₀.left := by
    simp [F, Over.pullback_map_left]
  let φ := Scheme.Pic.mapHom (pullback.fst P.hom j)
  change φ (translationSquareClass f a L) =
    translationSquareClass (F.map f) (F.map a) _
  simp only [translationSquareClass, map_mul, map_pow, map_inv, φ, Scheme.Pic.mapHom_apply,
    ← Scheme.Pic.map_comp, ← natural, Functor.map_mul, Functor.map_inv', Functor.map_one]

theorem translationSquareClass_eq_one_over_field
    {K : Type u} [Field K] (A : PkgI3.AbVar K)
    (P : Over (Spec (CommRingCat.of K))) (f a : P ⟶ A.X) (L : A.X.left.Pic) :
    letI := A.grp
    translationSquareClass f a L = 1 := by
  let := A.grp
  apply translationSquareClass_eq_one_of_cube f a L
  · have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of K)))).left.Pic :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)).Pic)
    change Scheme.Pic.map ((toUnit P ≫ η[A.X]).left) L = 1
    rw [Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one _ _ _
  · exact H5OriginalDVR.Lane2.AllFieldNativeCube.nativeCubeRelation A P a a⁻¹ f L


/-- An open subgroup containing the closed value of a section over a local
ring also contains the entire section. -/
theorem exists_section_of_closed_mem_open_subgroup
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H G : Over (Spec (CommRingCat.of R))}
    (i : H ⟶ G) [IsOpenImmersion i.left]
    (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (ha : a.left (IsLocalRing.closedPoint R) ∈ Set.range i.left) :
    ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H, b ≫ i = a := by
  have hRange : Set.range a.left ⊆ Set.range i.left := by
    rintro _ ⟨x, rfl⟩
    have hx : x ⤳ IsLocalRing.closedPoint R :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
    exact (hx.map a.left.continuous).mem_open i.left.isOpenEmbedding.isOpen_range ha
  let b := IsOpenImmersion.lift i.left a.left hRange
  have hb : b ≫ i.left = a.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk b ?_, Over.OverMorphism.ext hb⟩
  rw [← Over.w i, ← Category.assoc, hb, Over.w a]

/-- The square class on the product with an open subgroup is normalized
on the slice at the identity. -/
theorem map_translationSquareClass_identitySlice {S : Scheme.{u}}
    (G H : Over S) [GrpObj G] [GrpObj H] (i : H ⟶ G) [IsMonHom i]
    (L : G.left.Pic) :
    Scheme.Pic.map (lift (𝟙 G) (toUnit G ≫ η[H])).left
        (translationSquareClass (fst G H) (snd G H ≫ i) L) = 1 := by
  rw [map_translationSquareClass, lift_fst, lift_snd_assoc, Category.assoc]
  simp [← Hom.one_def]

set_option backward.isDefEq.respectTransparency false in
/-- Triviality of the square class for varying translations implies the
Picard square for any section of the translating subgroup. -/
theorem picard_square_of_translationSquareClass_eq_one
    {S : Scheme.{0}} [Subsingleton S.Pic] (G H : Over S) [GrpObj G] [GrpObj H]
    (i : H ⟶ G) (L : G.left.Pic)
    (h : translationSquareClass (fst G H) (snd G H ≫ i) L = 1)
    (a : 𝟙_ (Over S) ⟶ H) :
    Scheme.Pic.map (leftTranslationIso G (a ≫ i)).hom.left L *
      Scheme.Pic.map (leftTranslationIso G (a ≫ i)).inv.left L = L ^ 2 := by
  let j : G ⟶ G ⊗ H := lift (𝟙 G) (toUnit G ≫ a)
  have h' := congrArg (Scheme.Pic.map j.left) h
  rw [map_translationSquareClass, Scheme.Pic.map_one] at h'
  have hj : j ≫ fst G H = 𝟙 G := lift_fst _ _
  have hj' : j ≫ snd G H ≫ i = toUnit G ≫ (a ≫ i) := by
    rw [show j ≫ snd G H ≫ i = (j ≫ snd G H) ≫ i from (Category.assoc _ _ _).symm,
      show j ≫ snd G H = toUnit G ≫ a from lift_snd _ _, Category.assoc]
  rw [hj, hj'] at h'
  have : Subsingleton (𝟙_ (Over S)).left.Pic := inferInstanceAs (Subsingleton S.Pic)
  have hConst (b : 𝟙_ (Over S) ⟶ G) : Scheme.Pic.map (toUnit G ≫ b).left L = 1 := by
    rw [Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one _ _ _
  have hOne : Scheme.Pic.map (1 : G ⟶ G).left L = 1 := hConst (η[G])
  have hi : (toUnit G ≫ (a ≫ i))⁻¹ = toUnit G ≫ (a ≫ i)⁻¹ := by
    simp [Hom.inv_def]
  apply mul_inv_eq_one.mp
  simpa only [translationSquareClass, hOne, hConst, hi, Over.id_left, Scheme.Pic.map_id,
    one_pow, mul_one, leftTranslationIso, ZInQ.Contrib.CloudR2Poincare.L1.translate] using h'

end NeronDVR
