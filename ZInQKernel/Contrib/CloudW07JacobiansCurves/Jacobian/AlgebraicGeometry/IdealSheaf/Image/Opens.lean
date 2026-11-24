-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.IdealSheaf.Image.Opens), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# An open inside its scheme-theoretic closure

The scheme-theoretic image of a quasi-compact open inclusion agrees with the
original scheme over that open, where the open remains scheme-theoretically dense.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Opens

variable {scheme : Scheme.{u}} (opensFamily : scheme.Opens) [QuasiCompact opensFamily.ι]

lemma surjective_imageι_ι (hU : Dense (opensFamily : Set scheme)) : Surjective opensFamily.ι.imageι :=
  have : IsDominant opensFamily.ι := ⟨by rwa [DenseRange, range_ι]⟩
  inferInstance

/-- The copy of `opensFamily` inside the scheme-theoretic image `scheme*` of `opensFamily ⟶ scheme` is the preimage of `opensFamily`:
the open immersion `opensFamily ⟶ scheme*` has image `scheme* ∩ opensFamily`. -/
@[simp]
lemma opensRange_toImage : opensFamily.ι.toImage.opensRange = opensFamily.ι.imageι ⁻¹ᵁ opensFamily := by
  refine TopologicalSpace.Opens.ext ?_
  have witness : (opensFamily : Set scheme) = opensFamily.ι.imageι '' Set.range opensFamily.ι.toImage := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, opensFamily.ι.toImage_imageι, range_ι]
  change Set.range opensFamily.ι.toImage = opensFamily.ι.imageι ⁻¹' (opensFamily : Set scheme)
  rw [witness, Set.preimage_image_eq _ opensFamily.ι.imageι.isClosedEmbedding.injective]

/-- The scheme-theoretic closure `scheme* ⟶ scheme` of an open `opensFamily ⊆ scheme` is an isomorphism over `opensFamily`. -/
instance isIso_morphismRestrict_imageι : IsIso (opensFamily.ι.imageι ∣_ opensFamily) := by
  set e := opensFamily.ι.toImage.isoOpensRange ≪≫ opensFamily.ι.image.isoOfEq (opensRange_toImage opensFamily) with he
  have hcomp : e.hom ≫ (opensFamily.ι.imageι ∣_ opensFamily) = 𝟙 _ := by
    rw [← cancel_mono opensFamily.ι, Category.assoc, morphismRestrict_ι, Category.id_comp, he]
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι_assoc,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.toImage_imageι]
  have : IsIso (e.hom ≫ (opensFamily.ι.imageι ∣_ opensFamily)) := hcomp ▸ inferInstance
  exact IsIso.of_isIso_comp_left e.hom _

/-- **`opensFamily` is scheme-theoretically dense in its scheme-theoretic closure `scheme*`**: the inclusion
of the copy of `opensFamily` in `scheme*` is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_preimage_imageι :
    IsSchemeTheoreticallyDominant (opensFamily.ι.imageι ⁻¹ᵁ opensFamily).ι := by
  rw [← opensRange_toImage opensFamily, ← Scheme.Hom.isoOpensRange_inv_comp opensFamily.ι.toImage]
  infer_instance

end AlgebraicGeometry.Scheme.Opens
