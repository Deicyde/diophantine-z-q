import ZInQKernel.Contrib.OneProof.QuotientP1Coordinate
import ZInQKernel.OneProof.H.TailZ30

/-!
# p1-quot: `QuotientP1Coordinate` from the chain's own fields for T5, `HeckeIrreducible` and `QMAutCard`

* T5 from the textbook field `mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`, as in `TailZ23`);
* `HeckeIrreducible` from the added field `deligneComponentsY3PrintedAb` through the research field
  `mumfordRigidityCore` (`deligneComponentsY3Printed_iff_ab`, as in `TailZ23`, then gap-triage's route
  `deligneComponentsY3_of_printed` → `y3Connected_of_deligne` → `heckeIrreducible_of_connected`);
* `QMAutCard` from `QMCentralizerCM` (`QMSplit.Aut.qmAutCard_of`, TailU), itself from `QMCentralizerCMC` (proved by the
  contribution `QMLattice` from the textbook fields `uniformizationLeafAll`, `gagaMorphism`,
  `mumfordTorsionAlgClosed`, as in `TailZ30`) and T11(b) (`AVB2.t11b_of_exists` of the proved `t11bExists_lf8`).
-/

namespace HDec.MCRQuot

open MCRGlue

theorem quotientP1Coordinate_of_fields (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hRC : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (hD : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) (h24 : CMStab24) :
    MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed hAF hQE hTS hP1 hE
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (TSHecke.heckeIrreducible_of_connected (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed
        ((_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab
          (_root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core hRC)).mpr hD))))
    (QMSplit.Aut.qmAutCard_of (QMSplit.Aut.qmCentralizerCM_of
      (QMLattice.qmCentralizerCMC_of hU hG hMT) (AVB2.t11b_of_exists HSyn.t11bExists_lf8)))
    h24

end HDec.MCRQuot
