import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FinalAssemblyMin4
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3Card
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OModCard
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# The level-three moduli target from checked printed statements

Level-3 frames come from Milne's count of torsion points (`GeomCard3`) together with Milne,
Prop. 20.7, at `n = 3`; `O / 3 O` has 81 elements (`Y3OrderMod.card_OMod3`). Smoothness descent
is proved from Mathlib.
-/

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs. -/
theorem y3FullThreeRepZ30_of_printed_min5 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hB25 : BuzzardFrameRepTorsor 5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min hB1 (frameRepNS3_of hM3 hC3 Y3OrderMod.card_OMod3) hB25 hB3
    hB4 hB6 SourceDescent.h1StdEt_descentSmoothRelDimFiniteEtale hM5

end Y3Buzzard
