import ZInQKernel.Contrib.MulEtale.FibreMaps
import ZInQKernel.Contrib.MulEtale.Direct.FieldMulEtale
import ZInQKernel.Contrib.MulEtale.Direct.Global.CanonicalFibres

/-!
# Multiplication on the actual fibres of the given abelian scheme

The field theorem is applied to the same transported group object, with its
properness, smoothness and geometric integrality derived from the given model.
The map consumed by the arbitrary-base detector is identified by its actual
pullback projections; no fibre model, group law or desired square is supplied.
This module must compile before it supplies the arbitrary-base construction.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace H101DirectFieldRoute.FibreMultiplication

open ZInQ.Contrib.MulEtale.FibreMaps
open H101DirectGlobalDetection.CanonicalFibres

variable {O : Type} [CommRing O]

/-- The detector's actual fibre map is multiplication on the same native
`mapGrp.obj`, after the equality-domain transport proved from `Over.w`. -/
theorem fiberHom_pow_eq (A : Grp (Over (Spec (.of O)))) (s : Spec (.of O)) (m : ℕ) :
    fiberHom (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom s =
      (fibreMulDomainIso A s m).hom ≫
        (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left := by
  let f₀ := (𝟙 A.X ^ m : A.X ⟶ A.X).left
  let f₁ := (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left
  let e := fibreMulDomainIso A s m
  let i := A.X.hom.fiberι s
  let b := A.X.hom.fiberToSpecResidueField s
  apply pullback.hom_ext
  · calc
      fiberHom f₀ A.X.hom s ≫ i =
          (f₀ ≫ A.X.hom).fiberι s ≫ f₀ := fiberHom_fiberι f₀ A.X.hom s
      _ = (e.hom ≫ i) ≫ f₀ :=
        (congrArg (fun h => h ≫ f₀) (fibreMulDomainIso_hom_fiberι A s m)).symm
      _ = e.hom ≫ (i ≫ f₀) := Category.assoc e.hom i f₀
      _ = e.hom ≫ (f₁ ≫ i) :=
        congrArg (fun h => e.hom ≫ h) (fibre_mul_fiberι A s m).symm
      _ = (e.hom ≫ f₁) ≫ i := (Category.assoc e.hom f₁ i).symm
  · calc
      fiberHom f₀ A.X.hom s ≫ b =
          (f₀ ≫ A.X.hom).fiberToSpecResidueField s :=
        fiberHom_fiberToSpecResidueField f₀ A.X.hom s
      _ = e.hom ≫ b := (fibreMulDomainIso_hom_toSpec A s m).symm
      _ = e.hom ≫ (f₁ ≫ b) :=
        congrArg (fun h => e.hom ≫ h) (fibre_mul_toSpec A s m).symm
      _ = (e.hom ≫ f₁) ≫ b := (Category.assoc e.hom f₁ b).symm

/-- Apply the checked all-field theorem to the actual residue fibre. -/
theorem fibre_pow_etale (A : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme A]
    (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    Etale ((𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left) := by
  letI : GrpObj (fibreGrp A s).X := (fibreGrp A s).grp
  letI : Smooth (fibreGrp A s).X.hom := fibre_smooth A s
  letI : IsProper (fibreGrp A s).X.hom := fibre_isProper A s
  letI : GeometricallyIntegral (fibreGrp A s).X.hom := fibre_geometricallyIntegral A s
  exact @H101DirectFieldRoute.Translation.etale_pow_id_left_of_isUnit
    ((Spec (.of O)).residueField s) inferInstance (fibreGrp A s).X
    (fibreGrp A s).grp (fibre_smooth A s) (fibre_isProper A s)
    (fibre_geometricallyIntegral A s) m (isUnit_residue_natCast s m hm)

/-- This is the same fibre map required by the all-base detector, not just an
isomorphic abstract endomorphism. The equality-domain isomorphism is étale. -/
theorem fiberHom_pow_etale (A : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme A]
    (s : Spec (.of O)) (m : ℕ) (hm : IsUnit (m : O)) :
    Etale (fiberHom (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom s) := by
  rw [fiberHom_pow_eq]
  letI : Etale ((𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left) :=
    fibre_pow_etale A s m hm
  letI : Etale (fibreMulDomainIso A s m).hom := inferInstance
  exact Etale.etale_comp (fibreMulDomainIso A s m).hom
    (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left

end H101DirectFieldRoute.FibreMultiplication
