import ZInQKernel.Contrib.OneProof.ShimuraPointDict

/-! Check the fixed interfaces without opening their definitions. -/

namespace ShimuraPointDict

open CategoryTheory AlgebraicGeometry
open LeafModCurves AfTateLam

example : HeckePin.X1TauPoints := x1TauPoints
example : HeckePin.ConstOnTauPoints := constOnTauPoints

example (N : ℕ) (hN : 2 ≤ N) (X : Over SpecQ) [IsIntegral X.left]
    (jX tX : X.left.functionField) (hC : IsCurve X) (hG : IsX1Gen N X jX tX) :
    ∀ τ : UpperHalfPlane, ∃! x : CPt X, AtTau N jX tX x τ :=
  existsUnique_atTau hN hC hG

#check ShimuraPointDict.atTau_unique
#check ShimuraPointDict.exists_xi_of_compositeActions
#check ShimuraPointDict.shimuraHeckeRelations_of_compositeActions

end ShimuraPointDict
