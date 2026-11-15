import ZInQKernel.Contrib.OneProof.QuotientP1Printed
import ZInQKernel.Contrib.OneProof.QuotientP1.TameQuotSmooth
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-!
# p1-quot3: `quotientP1Coordinate` without the glue `TameQuotientSmoothRelDim`

`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean`; bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`). p1-quot2 (`QuotientP1Printed.lean`) reduced it to Lichtenbaum's theorem,
mcr-glue's L2, the smoothness half `TameQuotientSmoothRelDim` of L3, L4 `SmoothModelOfP1`, Edixhoven's theorem and
chain fields. Here `TameQuotientSmoothRelDim` is proved from the chain's textbook field `regularSmoothPerfect`
(`QuotientP1/TameQuotSmooth.lean`, `QuotientP1/TameInvariants.lean`), and `HeckeIrreducible` comes from the research
fields `mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU` (dcy3-used's `DCY3Used.y3Connected_of_leaves`) instead of
`mumfordRigidityCore` and `deligneComponentsY3PrintedAb`.

```
HDec.MCRQuot.quotientP1Coordinate_of_fields4
    (hL : QuotientP1Proof.LichtenbaumProjective) (hQE : FiniteQuotientExists) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hRS : CurveSplit.RegularSmoothPerfect) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hM : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) (hU3 : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MCRGlue.QuotientP1Coordinate
```
docs/research/p1-quot3.md. No `sorry`, no `axiom`. -/

namespace HDec

set_option maxHeartbeats 1000000

namespace MCRQuot

open MCRGlue

/-- **`QuotientP1Coordinate` from Lichtenbaum's theorem, mcr-glue's L2 and L4, Edixhoven's theorem and the chain's
fields** `regularSmoothPerfect`, `mumfordTorsionAlgClosed`, `mumfordGroupLaw`, `shimuraMainThmIDeligneY3AbU`,
`uniformizationLeafAll`, `gagaMorphism` (L3 proved: properness by p1-quot2, smoothness here). -/
theorem quotientP1Coordinate_of_fields4 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hP1 : SmoothModelOfP1) (hE : EdixhovenFixedSmooth2)
    (hRS : _root_.CurveSplit.RegularSmoothPerfect) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hM : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hU3 : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) : MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed2 hL hQE (tameQuotientSmooth_of_regularSmoothPerfect hRS) hP1 hE
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (TSHecke.heckeIrreducible_of_connected (_root_.DCY3Used.y3Connected_of_leaves hM hU3))
    (cMStabObjWeak_of_fields hU hG hMT)

end MCRQuot

end HDec
