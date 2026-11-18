import ZInQKernel.Contrib.CloudR2Poincare.L1.DualInterface
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.BaseChange.GroupPoints

/-!
# The actual field-extension translation bridge

The Spec Ω test formulation of K(L) is identified with translation on the
actual base-changed group scheme A_Ω. The point correspondence is the actual
restriction/pullback adjunction, and its multiplication is the proved
baseChangeHomMulEquiv, not an assumed preservation of terminal objects.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L1

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

abbrev extendedGroup (A : CommGrp (Over (Spec (.of k)))) : CommGrp (Over (Spec (.of Ω))) :=
  (baseChange k Ω).mapCommGrp.obj A

@[simp]
theorem extendedGroup_hom (A : CommGrp (Over (Spec (.of k)))) :
    (extendedGroup (Ω := Ω) A).X.hom = pullback.snd A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := rfl

@[simp]
theorem extendedGroup_left (A : CommGrp (Over (Spec (.of k)))) :
    (extendedGroup (Ω := Ω) A).X.left = pullback A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := rfl

/-- The identity map on Spec Ω compares the unit over Ω with the original field test. -/
def fieldUnitComparison : fieldTest k Ω ⟶
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj
      (𝟙_ (Over (Spec (.of Ω)))) :=
  Over.homMk (𝟙 (Spec (.of Ω))) (by simp [fieldTest])

/-- An actual Ω-rational point as a Spec Ω test point over k. -/
def originalFieldPoint (A : CommGrp (Over (Spec (.of k))))
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) : fieldTest k Ω ⟶ A.X :=
  fieldUnitComparison ≫ baseChangeHomMulEquiv A (𝟙_ (Over (Spec (.of Ω)))) a

@[simp]
theorem originalFieldPoint_left (A : CommGrp (Over (Spec (.of k))))
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) :
    (originalFieldPoint A a).left = a.left ≫ pullback.fst A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  simp only [originalFieldPoint, fieldUnitComparison, Over.comp_left, Over.homMk_left,
    baseChangeHomMulEquiv_apply_left]
  change 𝟙 (Spec (.of Ω)) ≫ (a.left ≫ pullback.fst A.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) = _
  exact Category.id_comp _

/-- The actual point correspondence is injective. -/
theorem originalFieldPoint_injective (A : CommGrp (Over (Spec (.of k)))) :
    Function.Injective (originalFieldPoint (Ω := Ω) A) := by
  intro a b h
  apply (baseChangeHomMulEquiv A (𝟙_ (Over (Spec (.of Ω))))).injective
  apply Over.OverMorphism.ext
  have hleft := congrArg (fun point : fieldTest k Ω ⟶ A.X ↦ point.left) h
  simpa only [originalFieldPoint_left, baseChangeHomMulEquiv_apply_left] using hleft

@[simp]
theorem originalFieldPoint_one (A : CommGrp (Over (Spec (.of k)))) :
    originalFieldPoint (Ω := Ω) A 1 = 1 := by
  rw [originalFieldPoint, map_one]
  exact MonObj.comp_one _

theorem originalFieldPoint_eq_one_iff (A : CommGrp (Over (Spec (.of k))))
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) :
    originalFieldPoint A a = 1 ↔ a = 1 := by
  constructor
  · intro h
    exact originalFieldPoint_injective A (h.trans (originalFieldPoint_one A).symm)
  · intro h
    rw [h, originalFieldPoint_one]

/-- The correspondence respects the actual base change of a group homomorphism. -/
theorem originalFieldPoint_postcomp {A B : CommGrp (Over (Spec (.of k)))}
    (f : A ⟶ B) (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) :
    originalFieldPoint B
        (a ≫ ((baseChange k Ω).mapCommGrp.map f).hom.hom.hom) =
      originalFieldPoint A a ≫ f.hom.hom.hom := by
  unfold originalFieldPoint
  rw [baseChangeHomMulEquiv_postcomp, Category.assoc]

/-- The varying-point translation on A×Spec Ω is the actual translation on A_Ω. -/
theorem field_translation_left (A : CommGrp (Over (Spec (.of k))))
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) :
    (translate (extendedGroup A).X a).left =
      (familyTranslate A.X (originalFieldPoint A a)).left := by
  let AΩ : Over (Spec (.of Ω)) := (extendedGroup (Ω := Ω) A).X
  let q := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let e := baseChangeHomMulEquiv A AΩ
  have hmul : e (translate AΩ a) =
      ((Over.map q).map (toUnit AΩ) ≫
        baseChangeHomMulEquiv A (𝟙_ (Over (Spec (.of Ω)))) a) * e (𝟙 AΩ) := by
    change (baseChangeHomMulEquiv A AΩ) ((toUnit AΩ ≫ a) * 𝟙 AΩ) = _
    rw [map_mul, baseChangeHomMulEquiv_naturality_left]
  apply pullback.hom_ext
  · have hfamily : (familyTranslate A.X (originalFieldPoint A a)).left ≫
        pullback.fst A.X.hom q = (translationAction A.X (originalFieldPoint A a)).left := by
      simpa only [Over.comp_left, Over.fst_left, fieldTest, Over.mk_hom, Over.mk_left, q] using
        congrArg (fun arrow : A.X ⊗ fieldTest k Ω ⟶ A.X ↦ arrow.left)
          (familyTranslate_fst A.X (originalFieldPoint A a))
    rw [hfamily]
    have hleft := congrArg (fun arrow : (Over.map q).obj AΩ ⟶ A.X ↦ arrow.left) hmul
    simpa only [e, AΩ, q, baseChangeHomMulEquiv_apply_left, Hom.mul_def,
      Over.comp_left, Over.lift_left, Over.map_map_left, Over.map_obj_left, Over.toUnit_left,
      Over.pullback_obj_hom, Over.id_left, Category.id_comp, Category.assoc,
      translationAction, originalFieldPoint_left, Over.snd_left, Over.fst_left,
      fieldTest, Over.mk_hom, Over.mk_left, extendedGroup_hom, extendedGroup_left] using hleft
  · have hfamily : (familyTranslate A.X (originalFieldPoint A a)).left ≫
        pullback.snd A.X.hom q = pullback.snd A.X.hom q := by
      simpa only [Over.comp_left, Over.snd_left, fieldTest, Over.mk_hom, Over.mk_left, q] using
        congrArg (fun arrow : A.X ⊗ fieldTest k Ω ⟶ fieldTest k Ω ↦ arrow.left)
          (familyTranslate_snd A.X (originalFieldPoint A a))
    have h := Over.w (translate AΩ a)
    change (translate AΩ a).left ≫ pullback.snd A.X.hom q = pullback.snd A.X.hom q at h
    exact h.trans hfamily.symm

/-- The stabilizer test is literally invariance of the base-changed line bundle. -/
theorem field_stabilizer_iff (A : CommGrp (Over (Spec (.of k)))) (L : A.X.left.Pic)
    (a : 𝟙_ (Over (Spec (.of Ω))) ⟶ (extendedGroup A).X) :
    originalFieldPoint A a ∈ stabilizerSubgroup A.X L (fieldTest k Ω) ↔
      Scheme.Pic.map (translate (extendedGroup A).X a).left
        (Scheme.Pic.map (pullback.fst A.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) L) =
        Scheme.Pic.map (pullback.fst A.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) L := by
  change Scheme.Pic.map (familyTranslate A.X (originalFieldPoint A a)).left
      (parameterLineClass A.X L (fieldTest k Ω)) = parameterLineClass A.X L (fieldTest k Ω) ↔ _
  rw [← field_translation_left]
  rfl

end ZInQ.Contrib.CloudR2Poincare.L1
