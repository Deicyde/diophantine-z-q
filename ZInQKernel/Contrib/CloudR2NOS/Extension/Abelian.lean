import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2NOS.AVInput

/-!
# Abelian-variety input after literal original-group base change

New H5 bundle glue on `PkgI2.baseChange`, using Mathlib's actual pullback
properties. The scheme and all group data stay those of the original definition.
This is neither a Néron-model constructor nor good-reduction descent.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace ZInQ.Contrib.CloudR2NOS.Extension

/-- The literal original-group base change remains an abelian variety. -/
theorem isAbelianVariety_baseChange {K : Type u} [Field K]
    (A : Grp (Over (Spec (.of K)))) [hA : PkgI2.IsAbelianVariety A]
    (E : Type u) [Field E] [Algebra K E] :
    PkgI2.IsAbelianVariety (PkgI2.baseChange A E) := by
  haveI : IsProper A.X.hom := hA.proper
  haveI : Smooth A.X.hom := hA.smooth
  haveI : GeometricallyIntegral A.X.hom := hA.geomIntegral
  refine ⟨?_, ?_, ?_⟩
  · change IsProper (CategoryTheory.Limits.pullback.snd A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    infer_instance
  · change Smooth (CategoryTheory.Limits.pullback.snd A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    infer_instance
  · change GeometricallyIntegral (CategoryTheory.Limits.pullback.snd A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    infer_instance

/-- The canonical H76/FLT source input uses the SAME base-changed group scheme. -/
theorem sourceBundleOf_baseChange {K : Type u} [Field K]
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (E : Type u) [Field E] [Algebra K E] :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle
      E (PkgI2.baseChange A E).X.hom := by
  letI : PkgI2.IsAbelianVariety (PkgI2.baseChange A E) := isAbelianVariety_baseChange A E
  exact ZInQ.Contrib.CloudR2NOS.sourceBundleOfAbelianVariety (PkgI2.baseChange A E)

end ZInQ.Contrib.CloudR2NOS.Extension

#print axioms ZInQ.Contrib.CloudR2NOS.Extension.isAbelianVariety_baseChange
#print axioms ZInQ.Contrib.CloudR2NOS.Extension.sourceBundleOf_baseChange
