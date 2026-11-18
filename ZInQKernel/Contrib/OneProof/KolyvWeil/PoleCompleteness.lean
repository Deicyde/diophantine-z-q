import ZInQKernel.Contrib.OneProof.KolyvWeil.Leaves
import ZInQKernel.Contrib.OneProof.CasselsTatePairing

namespace ZInQ.Manuscript.KolyvWeil

/-- The exact old `hK` statement follows from the conductor-level parametrization and
Kolyvagin's Theorem 1. The cusp form argument of the old interface is unused. -/
theorem kolyvaginThm1_of_prints (hB : BCDTThmA6) (hK : KolyvaginThm1Print) :
    PoleS12.KolyvaginThm1 := by
  intro E hE _ hA
  let _ := hE
  exact rankOne_and_finiteSha_of_prints hB hK E hA

/-- The rank implication consumed by `PoleRC.crm_of_restrictedConverse_proved`. -/
theorem kolyvaginRankOne_of_prints (hB : BCDTThmA6) (hK : KolyvaginThm1Print) :
    PoleRC.KolyvaginRankOne := by
  intro E hE hA
  let _ := hE
  exact (rankOne_and_finiteSha_of_prints hB hK E hA).1

/-- The same pole-completeness statement as
`PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` (tex `hyp:PC`,
L1001–1004), with the same derivation of Lemma 5.4 from the pairing. At `lem:forward-rank`
(L1086–1109) it supplies rank one from the conductor-level parametrization and Kolyvagin. -/
theorem poleCompleteness_of_restrictedConverseGenuine_print
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : PoleS12.CasselsTatePairingCurves)
    (hB6 : BCDTThmA6) (hKPrint : KolyvaginThm1Print) :
    ZInQ.Manuscript.PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (PoleS12.lemma54At_of_casselsTate (PoleS12.casselsTateSquareCurves_of_pairing hCT))
      (kolyvaginRankOne_of_prints hB6 hKPrint))
    PoleS12.simultaneousConstruction

end ZInQ.Manuscript.KolyvWeil
