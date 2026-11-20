import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_of_flat

/-! The scheme-theoretic image of a group homomorphism over a field is a closed group subscheme. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.SemiAbDescend
open ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace ZInQ.FaltingsRestate

universe u

variable {k : Type u} [Field k]
local notation "Sch" => Over (Spec (CommRingCat.of k))

set_option backward.isDefEq.respectTransparency false in
private theorem isMonHom_of_pointwise_mul
    {A B : Sch} [GrpObj A] [GrpObj B] (j : A ⟶ B)
    (ht : ∀ (T : Sch) (x y : T ⟶ A), (x * y) ≫ j = (x ≫ j) * (y ≫ j)) :
    IsMonHom j := by
  constructor
  · have he := ht (𝟙_ Sch) 1 1
    rw [_root_.one_mul] at he
    let a : (𝟙_ Sch) ⟶ B := (1 : (𝟙_ Sch) ⟶ A) ≫ j
    have h : a = 1 := mul_left_cancel (he.symm.trans (_root_.mul_one a).symm)
    exact h
  · have he := ht (A ⊗ A) (fst A A) (snd A A)
    change (lift (fst A A) (snd A A) ≫ μ[A]) ≫ j =
      lift (fst A A ≫ j) (snd A A ≫ j) ≫ μ[B] at he
    rw [lift_fst_snd, Category.id_comp] at he
    have hl : lift (fst A A ≫ j) (snd A A ≫ j) = j ⊗ₘ j := by
      apply hom_ext <;> simp
    rwa [hl] at he

set_option backward.isDefEq.respectTransparency false in
/-- The relative point-law compatibility gives a morphism of group objects. -/
theorem isMonHom_of_relativeGroupLaw_mul (Y X : Sch) [GrpObj Y]
    (LX : RelativeGroupLaw k X.hom) (f : X ⟶ Y)
    (h : letI : GrpObj (Over.mk Y.hom) := inferInstanceAs (GrpObj Y)
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (x y : SchemeHomOver t X.hom),
        NeronModelInfra.schemeHomOverComp (LX.mul t x y) ⟨f.left, Over.w f⟩ =
          (relativeGroupLawOfGrpObj k Y.hom).mul t
            (NeronModelInfra.schemeHomOverComp x ⟨f.left, Over.w f⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨f.left, Over.w f⟩)) :
    letI : GrpObj X := LX.grpObjOverMk
    IsMonHom f := by
  letI : GrpObj X := LX.grpObjOverMk
  letI : GrpObj (Over.mk Y.hom) := inferInstanceAs (GrpObj Y)
  apply isMonHom_of_pointwise_mul
  intro T x y
  apply Over.OverMorphism.ext
  have hh := h T.hom (overHomEquivSchemeHomOver T X.hom x)
    (overHomEquivSchemeHomOver T X.hom y)
  have hm := LX.overHomEquivSchemeHomOver_mul T x y
  rw [← hm] at hh
  exact congrArg Subtype.val hh

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-compact group homomorphism has its actual scheme image as a
closed group subscheme, with a dominant factorization. -/
theorem exists_group_scheme_image
    {X Y : Sch} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f]
    [QuasiCompact f.left] :
    ∃ (Z : Sch) (_ : GrpObj Z) (i : Z ⟶ Y) (_ : IsMonHom i)
      (_ : IsClosedImmersion i.left) (q : X ⟶ Z) (_ : IsMonHom q)
      (_ : IsDominant q.left) (_ : QuasiCompact q.left),
      q ≫ i = f := by
  letI : GrpObj (Over.mk X.hom) := inferInstanceAs (GrpObj X)
  letI : GrpObj (Over.mk Y.hom) := inferInstanceAs (GrpObj Y)
  let σ : SchemeHomOver X.hom Y.hom := ⟨f.left, Over.w f⟩
  let LX := relativeGroupLawOfGrpObj k X.hom
  let LY := relativeGroupLawOfGrpObj k Y.hom
  let Z := Over.mk (f.left.imageι ≫ Y.hom)
  let i : Z ⟶ Y := Over.homMk f.left.imageι rfl
  let q : X ⟶ Z := Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Over.w])
  have hqi : q ≫ i = f := Over.OverMorphism.ext (Scheme.Hom.toImage_imageι _)
  have hσ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (x y : SchemeHomOver t X.hom) :
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        LY.mul t (NeronModelInfra.schemeHomOverComp x σ)
          (NeronModelInfra.schemeHomOverComp y σ) := by
    apply Subtype.ext
    let a := schemeHomOverToOverHom x
    let b := schemeHomOverToOverHom y
    exact congrArg CommaMorphism.left (MonObj.mul_comp a b f)
  obtain ⟨LZ, hmul, _⟩ :=
    LY.exists_relativeGroupLaw_image_of_homomorphism_of_flat LX σ hσ
  letI : GrpObj Z := LZ.grpObjOverMk
  haveI : IsMonHom i := isMonHom_of_relativeGroupLaw_mul Y Z LZ i hmul
  haveI : IsClosedImmersion i.left := show IsClosedImmersion f.left.imageι by infer_instance
  haveI : IsDominant q.left := show IsDominant f.left.toImage by infer_instance
  haveI : QuasiCompact q.left := show QuasiCompact f.left.toImage by infer_instance
  haveI : Mono i := Over.mono_of_mono_left i
  haveI : IsMonHom (q ≫ i) := hqi ▸ inferInstance
  haveI : IsMonHom q := isMonHom_of_comp_mono q i
  exact ⟨Z, inferInstance, i, inferInstance, inferInstance, q, inferInstance, inferInstance,
    inferInstance, hqi⟩

end ZInQ.FaltingsRestate
