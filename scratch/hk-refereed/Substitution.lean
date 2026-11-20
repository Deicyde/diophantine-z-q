import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedSubstitute

/-!
Dry run of the headline substitution. Instantiate `height` with
`HDec.HSyn.sixContactMin_of_open91` of the unchanged headline, whose result is
`ZInQ.SixContactMin`. The pole theorem, printed BCDT adapter, and final assembly are checked
here with their actual imports.
-/

namespace ZInQ.Manuscript.HKRefereed

universe u v w

theorem frozenTarget_of_heightAssembly_and_hkConsumed
    {R : Sort u} {T : Sort v} {L : Sort w}
    (height : R → T → L → ZInQ.SixContactMin) (r : R) (t : T) (l : L)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : PoleS12.CasselsTatePairingCurves)
    (hB : ZInQ.Contrib.RC53Assist.BCDTPrint.BCDTThmAPrinted)
    (hK : HKConsumed) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (height r t l)
    (poleCompleteness_of_hkConsumed hRC hCT
      (ZInQ.Contrib.RC53Assist.BCDTPrint.bcdtThmA_of_printed hB) hK)

end ZInQ.Manuscript.HKRefereed

#print axioms ZInQ.Manuscript.HKRefereed.frozenTarget_of_heightAssembly_and_hkConsumed
