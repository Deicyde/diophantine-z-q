import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# av-glue, part B: `ImageFactorization` from Cartier's theorem

Check with `lake env lean scratch/av-glue/ImageFact.lean`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AVGlue

/-! ## §1. Scheme-level lemmas on scheme-theoretic images -/

section SchemeLevel

variable {X Y : Scheme.{0}}

/-- The morphism to the scheme-theoretic image has trivial kernel. -/
theorem ker_toImage (f : X ⟶ Y) [QuasiCompact f] : f.toImage.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => (⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩ : f.image.affineOpens))
    ?_ ?_
  · simp only
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

instance (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage :=
  ⟨ker_toImage f⟩

/-- If `d` is scheme-theoretically dominant and `d ≫ g` factors through a closed immersion `i`,
then the kernel of `i` is contained in that of `g`. -/
theorem ker_le_of_dominant {V W Y' Z : Scheme.{0}} (d : V ⟶ W) [IsSchemeTheoreticallyDominant d]
    (g : W ⟶ Z) (i : Y' ⟶ Z) (a : V ⟶ Y') (h : d ≫ g = a ≫ i) : i.ker ≤ g.ker := by
  have h1 : g.ker = (d ≫ g).ker := by
    rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rw [h1, h, Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot i]
  exact Scheme.IdealSheafData.map_mono i bot_le

/-- The morphism to the image is surjective for a proper map. -/
theorem surjective_toImage (f : X ⟶ Y) [IsProper f] : Surjective f.toImage := by
  have : IsProper (f.toImage ≫ f.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  refine ⟨?_⟩
  rw [← Set.range_eq_univ, ← f.toImage.isClosedMap.isClosed_range.closure_eq]
  exact f.toImage.denseRange.closure_eq

end SchemeLevel

/-! ## §2. A subobject of a group object closed under the group law is a group object -/

section Transport

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G Y : C} [GrpObj G]

/-- The group object structure on a subobject `i : Y ↪ G` closed under the group law. -/
@[reducible] noncomputable def grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) : GrpObj Y where
  one := oneY
  mul := mulY
  one_mul := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, hone, leftUnitor_hom]
    rw [show fst (𝟙_ C) Y ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.one_mul]
  mul_one := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, hone, rightUnitor_hom]
    rw [show snd Y (𝟙_ C) ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.mul_one]
  mul_assoc := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc]
    rw [_root_.mul_assoc]
  inv := invY
  left_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [inv_mul_cancel, Hom.one_def]
  right_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [mul_inv_cancel, Hom.one_def]

/-- The inclusion is a homomorphism for `grpObjOfMono`. -/
theorem isMonHom_grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) :
    letI := grpObjOfMono i mulY hmul oneY hone invY hinv
    IsMonHom i := by
  letI := grpObjOfMono i mulY hmul oneY hone invY hinv
  refine ⟨hone, ?_⟩
  change mulY ≫ i = _
  rw [hmul, Hom.mul_def, ← lift_fst_comp_snd_comp]

/-- If `i` is a monic homomorphism and `π ≫ i` is a homomorphism, so is `π`. -/
theorem isMonHom_of_comp_mono {M : C} [MonObj M] [MonObj Y] (π : M ⟶ Y) (i : Y ⟶ G) [Mono i]
    [IsMonHom i] [IsMonHom (π ≫ i)] : IsMonHom π := by
  refine ⟨?_, ?_⟩
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

end Transport

end AVGlue
