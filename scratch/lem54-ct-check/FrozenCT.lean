import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.CasselsTatePairing

namespace ZInQ.OneProof

/-- Dry run of `frozenTarget` with the pairing on the curves of Theorem 5.3 in place of Lemma 5.4. -/
theorem frozenTargetCT
    (r : HDec.HSyn.OpenResearchLeaves60) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open79 r t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing hRC hCT hB hK)

end ZInQ.OneProof

#check ZInQ.OneProof.frozenTarget
#check ZInQ.OneProof.frozenTargetCT
#print axioms ZInQ.OneProof.frozenTargetCT
#discharges
