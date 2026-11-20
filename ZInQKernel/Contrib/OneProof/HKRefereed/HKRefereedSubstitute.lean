import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedConsumed

/-! # Pole completeness using the consumed rank-one fragment -/

namespace ZInQ.Manuscript.HKRefereed

/-- The same pole argument with only the infinite-order output used at the descent call. -/
theorem poleCompleteness_of_hkConsumed
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : PoleS12.CasselsTatePairingCurves) (hB : PoleS12.BCDTThmA)
    (hK : HKConsumed) : PoleCompleteness := by
  have h54 := PoleS12.lemma54At_of_casselsTatePairing hCT
  have hCRM : PoleRC.CRM := by
    intro ℓ hℓ hsf h12 h8 β hβ
    have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
    have hA := hRC ℓ hℓ hsf h12 (h54 ℓ hℓ hsf h12 h8)
    have hP := hK ℓ hℓ hsf h12 h8 (hB _ (PoleRC.curve_isElliptic hℓ0)) hA
    exact PoleRC.descentGlueM ℓ hℓ hsf h12 (PoleRC.mordellWeilM ℓ hℓ hsf h12)
      hP h8 (β, 1) hβ
  exact PoleRC.poleCompleteness_of_crm hCRM PoleS12.simultaneousConstruction

end ZInQ.Manuscript.HKRefereed

#print axioms ZInQ.Manuscript.HKRefereed.poleCompleteness_of_hkConsumed
