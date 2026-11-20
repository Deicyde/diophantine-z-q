import ZInQKernel.OneProof.H.TailZ98
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedConsumed

/-! Dry run of the headline with just its consumed Kolyvagin input. -/

namespace ZInQ.Manuscript.HKRefereed

theorem frozenTarget_of_hkConsumed
    (r : HDec.HSyn.OpenResearchLeaves72) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves28)
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : PoleS12.CasselsTatePairingCurves)
    (hB : ZInQ.Contrib.RC53Assist.BCDTPrint.BCDTThmAPrinted)
    (hK : HKConsumed) : ZInQ.FrozenTarget := by
  have hB' := ZInQ.Contrib.RC53Assist.BCDTPrint.bcdtThmA_of_printed hB
  have h54 := PoleS12.lemma54At_of_casselsTatePairing hCT
  have hCRM : PoleRC.CRM := by
    intro ℓ hℓ hsf h12 h8 β hβ
    have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
    have hA := hRC ℓ hℓ hsf h12 (h54 ℓ hℓ hsf h12 h8)
    have hP := hK ℓ hℓ hsf h12 h8 (hB' _ (PoleRC.curve_isElliptic hℓ0)) hA
    exact PoleRC.descentGlueM ℓ hℓ hsf h12 (PoleRC.mordellWeilM ℓ hℓ hsf h12)
      hP h8 (β, 1) hβ
  exact ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open91 r t l)
    (PoleRC.poleCompleteness_of_crm hCRM PoleS12.simultaneousConstruction)

end ZInQ.Manuscript.HKRefereed

#print axioms ZInQ.Manuscript.HKRefereed.frozenTarget_of_hkConsumed
