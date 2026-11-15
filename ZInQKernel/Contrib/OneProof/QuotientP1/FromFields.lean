import ZInQKernel.Contrib.OneProof.QuotientP1Coordinate
import ZInQKernel.OneProof.H.TailZ17

/-!
# p1-quot: `QuotientP1Coordinate` from the chain's own fields for T5 and `HeckeIrreducible`

T5 comes from the textbook field `mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`, as in
`TailZ23`), `HeckeIrreducible` from the added field `deligneComponentsY3PrintedAb` through the research field
`mumfordRigidityCore` (`deligneComponentsY3Printed_iff_ab`, as in `TailZ23`, then gap-triage's route
`deligneComponentsY3_of_printed` → `y3Connected_of_deligne` → `heckeIrreducible_of_connected`).
-/

namespace HDec.MCRQuot

open MCRGlue

theorem quotientP1Coordinate_of_fields (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth) (hCyc : TameInertiaCyclic) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hRC : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (hD : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb) (hO : CMStabObj) :
    MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed hAF hQE hTS hP1 hE hCyc
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (TSHecke.heckeIrreducible_of_connected (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed
        ((_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab
          (_root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core hRC)).mpr hD)))) hO

end HDec.MCRQuot
