import ZInQKernel.OneProof.H.TailB
open CategoryTheory AlgebraicGeometry
example {K : Type} [Field K] (A : PkgI3.AbVar K) : GeometricallyReduced A.X.hom := inferInstance
example {K : Type} [Field K] (A : PkgI3.AbVar K) : Flat A.X.hom := inferInstance
example {K : Type} [Field K] : IsReduced (Spec (CommRingCat.of K)) := inferInstance
example {K : Type} [Field K] : IsLocallyNoetherian (Spec (CommRingCat.of K)) := inferInstance
example {K : Type} [Field K] (A : PkgI3.AbVar K) : IsReduced A.X.left :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom
#check @GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
