import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Homology.Embedding.Map
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Native extension coherence used by the Čech face chain promotion

This is the existing native mapExtendIso naturality, promoted to an equality
of full maps. It can be checked independently while L1 finishes its section
helper. No provider or L1 source is edited or compiled by this module.
-/

noncomputable section
open CategoryTheory Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native scalar extension commutes with the actual extension of chain maps;
this is the native mapExtendIso naturality, including all integer degrees. -/
theorem mapExtend_hom_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (φ : C ⟶ D) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) ≫
      (D.mapExtendIso ComplexShape.embeddingUpNat
        (ModuleCat.extendScalars (algebraMap A B))).hom =
    (C.mapExtendIso ComplexShape.embeddingUpNat
        (ModuleCat.extendScalars (algebraMap A B))).hom ≫
      HomologicalComplex.extendMap
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).map φ)
        ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact HomologicalComplex.mapExtensIso_hom_f_naturality φ ComplexShape.embeddingUpNat
    (ModuleCat.extendScalars (algebraMap A B)) n

/-- A proved Nat square promotes through the actual native mapExtendIso. This
helper is instantiated with the proven geometric Nat square; no square
premise is added to the final geometric theorem. -/
theorem extend_proved_Nat_square
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ}
    {CB DB : CochainComplex (ModuleCat.{u} B) ℕ}
    (φ : C ⟶ D) (φB : CB ⟶ DB)
    (EC : (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).obj C) ≅ CB)
    (ED : (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).obj D) ≅ DB)
    (h : EC.hom ≫ φB =
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℕ)).map φ) ≫ ED.hom) :
    (C.mapExtendIso ComplexShape.embeddingUpNat
        (ModuleCat.extendScalars (algebraMap A B))).hom ≫
      HomologicalComplex.extendMap EC.hom ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap φB ComplexShape.embeddingUpNat =
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) ≫
      (D.mapExtendIso ComplexShape.embeddingUpNat
        (ModuleCat.extendScalars (algebraMap A B))).hom ≫
      HomologicalComplex.extendMap ED.hom ComplexShape.embeddingUpNat := by
  rw [← HomologicalComplex.extendMap_comp, h, HomologicalComplex.extendMap_comp]
  rw [← Category.assoc, ← mapExtend_hom_naturality]
  exact Category.assoc _ _ _

end ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion
