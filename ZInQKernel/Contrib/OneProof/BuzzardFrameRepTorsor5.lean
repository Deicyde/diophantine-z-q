import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Defs
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.FrameRepM
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.GeomFree5
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Torsor
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# Full level-5 frames from Milne's statements

Buzzard prints, without proof, that full level-`M` structures on a false elliptic curve are
represented by a closed subscheme of `A[M]` which is an étale `(O/MO)ˣ`-torsor (Duke Math. J. 87
(1997), §1, after Def. 1.1). At `M = 5` this is `BuzzardFrameRepTorsor 5`. Here it is proved from
two statements of Milne's *Abelian Varieties* (1986): Prop. 20.7 at `n = 5` (multiplication by 5
is finite and étale, `MilneProp207 5`) and Remark 8.4 at `n = 5` (a geometric fibre has 625 points
of order dividing 5, `GeomCard5`).

* `GeomFreeM 5`: at each geometric point the 5-torsion has a generator, since `O/5O ≅ M₂(F₅)`
  splits it into two halves of 25 points each (`geomFree5_of_card`);
* `BuzzardFrameRep 5`: the generators form a closed subscheme of `A`, finite, étale and surjective
  over the base (`LevelM.frameRepM_of`);
* the torsor square: two generators over the same point differ by a unique unit of `O/5O`
  (`frameRepTorsor_of_rep`).
-/

/-- `BuzzardFrameRepTorsor 5` from Milne, Prop. 20.7 and Remark 8.4, at `n = 5`. -/
theorem buzzardFrameRepTorsor5_of_milne (hM5 : MilneProp207 5) (hC5 : GeomCard5) :
    BuzzardFrameRepTorsor 5 :=
  frameRepTorsor_of_rep 5 (LevelM.frameRepM_of 5 hM5 (geomFree5_of_card hC5))

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs, with Milne's count of the 5-torsion
(`GeomCard5`) in place of `BuzzardFrameRepTorsor 5`. -/
theorem y3FullThreeRepZ30_of_printed_milne5 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hC3 : GeomCard3) (hC5 : GeomCard5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_min5 hB1 hM3 hC3 (buzzardFrameRepTorsor5_of_milne hM5 hC5) hB3
    hB4 hB6 hM5

/-- `Y3RouteA.Y3FullThreeRepZ30` from seven printed inputs: Milne's Remark 8.4 for every order
prime to the characteristic (`MilneRem84`) gives both counts `GeomCard3` and `GeomCard5`. -/
theorem y3FullThreeRepZ30_of_printed_rem84 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hR : MilneRem84)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_milne5 hB1 hM3 (geomCard3_of_rem84 hR) (geomCard5_of_rem84 hR)
    hB3 hB4 hB6 hM5

end Y3Buzzard
