import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FinalAssembly
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.DescentFromMathlib
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# The level-three moduli target with the Mathlib-provable descent leaves discharged

`ProperLocalOnBase` and `DescentClosedImmersion` are proved from Mathlib's flat descent
results, so they are no longer hypotheses. Smoothness of the descended curve comes from B7(b). Local finite type of the quotient descends
along the finite flat quotient map by the Artin-Tate lemma (`Y3SourceDescent`), and at level 3
only frame representability without the torsor clause or surjectivity is used.
-/

/-- `Y3RouteA.Y3FullThreeRepZ30` from the remaining printed leaves. -/
theorem y3FullThreeRepZ30_of_printed_min (hB1 : BuzzardThm21Cor23V15')
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale) (hM : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed hB1 hB23 hB25 hB3 hB4 hB6 hB7b descentClosedImmersion hM
    properLocalOnBase

end Y3Buzzard
