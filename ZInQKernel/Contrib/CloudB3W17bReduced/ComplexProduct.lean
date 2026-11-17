import ZInQKernel.Contrib.CloudB3W17bReduced.Port.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
import ZInQKernel.OneProof.H.TailP

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

namespace ZInQ.Contrib.CloudB3W17bReduced

/-- Products of the original reduced complex schemes are reduced; no geometric-reducedness
or smoothness premise is added. -/
theorem isReduced_complex_pullback {X Y : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℂ)) (g : Y ⟶ Spec (CommRingCat.of ℂ))
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced Y] :
    AlgebraicGeometry.IsReduced (pullback f g) :=
  AlgebraicGeometry.isReduced_pullback_over_perfectField f g

/-- The same statement on the existing over-category product, not a substitute product object. -/
theorem isReduced_complex_tensor (X Y : Over (Spec (CommRingCat.of ℂ)))
    [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsReduced Y.left] :
    AlgebraicGeometry.IsReduced (X ⊗ Y).left := by
  change AlgebraicGeometry.IsReduced (pullback X.hom Y.hom)
  exact isReduced_complex_pullback X.hom Y.hom

end ZInQ.Contrib.CloudB3W17bReduced
