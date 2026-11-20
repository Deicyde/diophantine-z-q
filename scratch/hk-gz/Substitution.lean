import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedSubstitute
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZAssembly

/-!
Conditional headline dry run. As in stage one, instantiate `height` with the unchanged
height supplier `HDec.HSyn.sixContactMin_of_open91`. No headline assembly module is imported.
-/

namespace ZInQ.Manuscript.HKGZ

universe u v w

theorem frozenTarget_of_heightAssembly_and_grossZagier
    {R : Sort u} {T : Sort v} {L : Sort w}
    (height : R → T → L → ZInQ.SixContactMin) (r : R) (t : T) (l : L)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : PoleS12.CasselsTatePairingCurves)
    (hB : ZInQ.Contrib.RC53Assist.BCDTPrint.BCDTThmAPrinted)
    (hNew : ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular)
    (hCM : PoleCMTraceDictionary) (hBFH : BFHTwistNonvanishingDraft)
    (hGZ : GrossZagierTraceDraft) (hConj : HeegnerTraceConjugationDraft) : ZInQ.FrozenTarget := by
  have hb := ZInQ.Contrib.RC53Assist.BCDTPrint.bcdtThmA_of_printed hB
  exact ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (height r t l)
    (HKRefereed.poleCompleteness_of_hkConsumed hRC hCT hb
      (hkConsumed_of_grossZagier hb hNew hCM hBFH hGZ hConj))

end ZInQ.Manuscript.HKGZ

#print axioms ZInQ.Manuscript.HKGZ.frozenTarget_of_heightAssembly_and_grossZagier
