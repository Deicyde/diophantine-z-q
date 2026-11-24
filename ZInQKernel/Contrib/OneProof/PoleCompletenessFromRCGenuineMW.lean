import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuine
import ZInQKernel.Contrib.PoleRC.MordellWeilM

/-!
# Theorem 5.2 from the printed Theorem 5.3, with Mordell's theorem for `E_ℓ` proved

`PoleS12.poleCompleteness_of_restrictedConverseGenuine` (`PoleCompletenessFromRCGenuine.lean`) takes
the textbook statement `PoleRC.MordellWeil` (every elliptic curve over `ℚ` has finitely generated
rational points) as a hypothesis. Its proof uses it only at the curves `E_ℓ`, where it is proved:
`PoleRC.mordellWeilM` (`PoleRC/MordellWeilM.lean`, Mathlib's descent theorem with the naive height
and the 2-descent of `E_ℓ`). This file removes that hypothesis.

The remaining hypotheses of `poleCompleteness_of_restrictedConverseGenuine_mw` are Theorem 5.3
(`SelmerTwoPower.RestrictedConverseGenuine`), the printed leaves `PoleS12.Lemma54`,
`PoleS12.BCDTThmA` and `PoleS12.KolyvaginThm1`, and the Kummer identification
`PoleS12.KummerSelmerM`.
-/

namespace ZInQ.Manuscript.PoleS12

/-- **Theorem 5.2 from the printed Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121), with
Mordell's theorem for `E_ℓ` proved (`PoleRC.mordellWeilM`) instead of assumed. -/
theorem poleCompleteness_of_restrictedConverseGenuine_mw
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hKum : PoleS12.KummerSelmerM) (hB : PoleS12.BCDTThmA) (hK : PoleS12.KolyvaginThm1) :
    Manuscript.PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (PoleS12.lemma54At_of_printed h54 hKum) (PoleS12.kolyvaginRankOne_of_printed hB hK))
    PoleS12.simultaneousConstruction

end ZInQ.Manuscript.PoleS12
