import ZInQKernel.Contrib.OneProof.R5fpCountLe
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute.Consumers
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-!
# fold34-eichler: the homfree form of FS5 with `R5fpCountLe`

The live consumer of González–Rotger's count in `ZInQ.OneProof.frozenTarget`'s proof is
`HDec.HSyn.gluePieces_of_open4_hf_pz` (`OneProof/H/PicZeroCharZeroCopy.lean`), through
`HDec.FS5NoCM.fibreComTrivialFull_of_leaves_hf''` (`Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean`),
whose last argument is `LeafQM.AV.R5fpCount`. gr56-prove gave the non-homfree forms with the weaker
`GR56.R5fpCountLe` (`HDec.FS5NoCM.fibreComTrivialFull_of_le` and its `_leaves'`/`_leaves''` forms,
`Contrib/OneProof/GR56Lattice.lean`); this module gives the homfree ones, verbatim up to that change. With
`EichlerBound.r5fpCountLe_proof` they let the fold remove `gonzalezRotgerProp56X6` with no new leaf.

No `sorry`; standard axioms only.
-/

namespace HDec

namespace FS5NoCM

open LeafQM.AV LeafQM.AV.Pin

/-- `fibreComTrivialFull_of_leaves_hf'` (HomFreeFiniteAlgClosedReroute/Consumers) with `R5fpCountLe`. -/
theorem fibreComTrivialFull_of_leaves_hf'_le (hL : R1R2fpFull) (hM : MobiusGlue)
    (hYu : QMLattice.YuB6Alg) (t6 : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialFull :=
  fibreComTrivialFull_of_le hL hM (comIntOrQuadOrder_of_leaves_hf hYu t6) hB hK hC

/-- `fibreComTrivialFull_of_leaves_hf''` (HomFreeFiniteAlgClosedReroute/Consumers) with `R5fpCountLe`. -/
theorem fibreComTrivialFull_of_leaves_hf''_le (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
    (hYu : QMLattice.YuB6Alg) (t6 : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves_hf'_le hL hM hYu t6 (cmConductorCoprime6_of hE) hK hC

end FS5NoCM

end HDec

/-- The research-field value the fold uses: `GR56.R5fpCountLe` from the proved `uniformizationLeafAll` and the two
textbook fields `gagaMorphism`, `mumfordTorsionAlgClosed` (taken as hypotheses, so that the fold does not depend on
their proofs). -/
theorem EichlerBound.r5fpCountLe_of_two (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    GR56.R5fpCountLe :=
  EichlerBound.r5fpCountLe_proof uniformizationLeafAll_proof hG hM

#print axioms HDec.FS5NoCM.fibreComTrivialFull_of_leaves_hf''_le
#print axioms EichlerBound.r5fpCountLe_of_two
