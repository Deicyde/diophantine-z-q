-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.ProjectiveSpectrum.GlobalSections), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.BasicOpen
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Global sections in affine charts of Proj

The morphism to a basic open of Proj induced by global sections is computed
by the corresponding map of degree-zero homogeneous localizations.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {gradedPieces : Type u} {gradedRing : Type u} [CommRing gradedRing]
  [SetLike gradedPieces gradedRing] [AddSubgroupClass gradedPieces gradedRing]
  (grading : ℕ → gradedPieces) [GradedRing grading] {sourceScheme : Scheme.{u}}

lemma toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom (sectionMap : gradedRing →+* Γ(sourceScheme, ⊤))
    {homogeneousElement : gradedRing} {degree : ℕ} {imageSection : Γ(sourceScheme, ⊤)} (imageEq : sectionMap homogeneousElement = imageSection) (h0d : 0 < degree) (homogeneous : homogeneousElement ∈ grading degree)
    (mapsPowers : Submonoid.powers homogeneousElement ≤ (Submonoid.powers imageSection).comap sectionMap) :
    toBasicOpenOfGlobalSections grading sectionMap imageEq h0d homogeneous ≫ (basicOpenIsoSpec grading homogeneousElement homogeneous h0d).hom =
      sourceScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen imageSection) (sourceScheme.basicOpen imageSection)
          (sourceScheme.toSpecΓ_preimage_basicOpen imageSection).ge ≫
        (basicOpenIsoSpecAway imageSection).hom ≫
          Spec.map (CommRingCat.ofHom
            ((IsLocalization.map (S := Localization.Away homogeneousElement) (Localization.Away imageSection) sectionMap mapsPowers).comp
              (algebraMap (Away grading homogeneousElement) (Localization.Away homogeneousElement)))) := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, Category.assoc, Scheme.Hom.map_resLE_assoc,
    Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Proj
