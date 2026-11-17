import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits

namespace PicDict
open PkgI3 PkgI3.AbVar

/-- **`GeomIntegralProd` is a theorem** for abelian varieties: `A × B` is smooth (so geometrically reduced) and
geometrically irreducible (Mathlib's `GeometricallyIrreducible.comp`). -/
theorem geomIntegralProd : GeomIntegralProd := by
  intro K _ A B
  have e : (A.X ⊗ B.X).hom = pullback.fst A.X.hom B.X.hom ≫ A.X.hom := rfl
  haveI : Smooth (A.X ⊗ B.X).hom := by rw [e]; infer_instance
  haveI := geometricallyReduced_of_smooth (A.X ⊗ B.X).hom
  haveI : GeometricallyIrreducible (A.X ⊗ B.X).hom := by
    rw [e]; exact GeometricallyIrreducible.comp _ _
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end PicDict

#print axioms PicDict.geomIntegralProd
