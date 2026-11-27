import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FinalAssemblyMin
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# The level-three moduli target, with level-3 frames derived

Frame representability at level 3 is derived from Milne, Prop. 20.7 at `n = 3` (multiplication
by 3 is finite and etale) and `GeomFree3` (the 3-torsion at a geometric point is free of rank one
over `O/3O`). Buzzard's frame statement, which assumes the level is coprime to the discriminant,
is used only at level 5.
-/

/-- `Y3RouteA.Y3FullThreeRepZ30` from the printed inputs, with level-3 frames derived. -/
theorem y3FullThreeRepZ30_of_printed_min2 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hF3 : GeomFree3) (hB25 : BuzzardFrameRepTorsor 5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min hB1 (frameRepNS_of_rep (frameRep3_of hM3 hF3)) hB25 hB3 hB4
    hB6 hB7b hM5

end Y3Buzzard
