import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FinalAssemblyMin2
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.H1StandardEtale
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# The level-three moduli target, with smoothness descent proved

Smoothness of relative dimension `n` descends along the finite etale surjections used by the
construction; this is proved from Mathlib (`SourceDescent.h1StdEt_descentSmoothRelDimFiniteEtale`),
so no descent statement remains among the inputs.
-/

/-- `Y3RouteA.Y3FullThreeRepZ30` from the remaining printed inputs. -/
theorem y3FullThreeRepZ30_of_printed_min4 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hF3 : GeomFree3) (hB25 : BuzzardFrameRepTorsor 5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min2 hB1 hM3 hF3 hB25 hB3 hB4 hB6
    SourceDescent.h1StdEt_descentSmoothRelDimFiniteEtale hM5

end Y3Buzzard
