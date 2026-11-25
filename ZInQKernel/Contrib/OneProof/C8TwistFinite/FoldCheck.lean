import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.C8TwistFinite.Chain

/-! # Headline check for the C8 reroute without `conradAppB`

* `addedLeaves28C8TF_ofLive`: the live added bundle `OpenAddedLeaves28` gives
  `OpenAddedLeaves28C8TF` by field projections alone, so every field of the new bundle has exactly
  the type of the live field of the same name (and the new bundle has one field fewer:
  `conradAppB`).
* `frozenTarget_without_conradAppB`: `ZInQ.OneProof.frozenTarget`'s body (`OneProof/Main.lean`)
  verbatim, with `HDec.HSyn.sixContactMin_of_open95` replaced by
  `HDec.HSyn.sixContactMin_of_open95_c8tf`, over `OpenAddedLeaves28C8TF`.
-/

namespace ZInQ.Contrib.C8TwistFinite

/-- The live added bundle gives the new one, field by field (no field is proved here). -/
theorem addedLeaves28C8TF_ofLive (l : HDec.HSyn.OpenAddedLeaves28) :
    HDec.HSyn.OpenAddedLeaves28C8TF where
  scholzeH1AbVar := l.scholzeH1AbVar
  t10TateDuality := l.t10TateDuality

example : HDec.HSyn.OpenResearchLeaves76 → HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves28C8TF → _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open95_c8tf

/-- **Theorem 1.1 without `conradAppB`**: `frozenTarget` with the added bundle
`OpenAddedLeaves28C8TF` (`OpenAddedLeaves28` without `conradAppB`). -/
theorem frozenTarget_without_conradAppB
    (r : HDec.HSyn.OpenResearchLeaves76) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves28C8TF)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open95_c8tf r t l)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end ZInQ.Contrib.C8TwistFinite

#print axioms ZInQ.Contrib.C8TwistFinite.frozenTarget_without_conradAppB
#print axioms ZInQ.Contrib.C8TwistFinite.addedLeaves28C8TF_ofLive
#print axioms ZInQ.Contrib.C8TwistFinite.c8TwistFinite_proof
#print axioms ZInQ.Contrib.C8TwistFinite.g12DetPZ_proof
#print axioms ZInQ.Contrib.C8TwistFinite.range_finite_of_pureHT
#print axioms HDec.HSyn.sixContactMin_of_open95_c8tf
