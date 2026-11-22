import ZInQKernel.Contrib.OneProof.KummerSelmerMProof
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineMW

/-!
# Theorem 5.2 from the printed Theorem 5.3, with the Kummer identification proved

Lane R7 of fork issue #83. `PoleS12.poleCompleteness_of_restrictedConverseGenuine_mw`
(`PoleCompletenessFromRCGenuineMW.lean`) takes the Kummer identification `PoleS12.KummerSelmerM`
(`#Sel₂(E_ℓ/ℚ) = #SelM ℓ`, textbook GLUE there) as a hypothesis. It is proved:
`PoleRC.kummerSelmerM_proof` (`KummerSelmerMProof.lean`), from the bijection
`SelM ℓ ≃ Sel₂(E_ℓ/ℚ)` of `ZInQKernel/Contrib/PoleRC/SelMTauCeti.lean` (Silverman, AEC 2nd ed.,
Prop. X.1.4, on the vendored Tau Ceti Galois cohomology). This file removes that hypothesis.

The remaining hypotheses of `poleCompleteness_of_restrictedConverseGenuine_final` are Theorem 5.3
(`SelmerTwoPower.RestrictedConverseGenuine`), the manuscript's Lemma 5.4 `PoleS12.Lemma54`, and the leaves
`PoleS12.BCDTThmA` and `PoleS12.KolyvaginThm1`.
-/

namespace ZInQ.Manuscript.PoleS12

/-- **The Kummer identification for `E_ℓ` holds** (`PoleRC.kummerSelmerM_proof`): for positive
squarefree `ℓ`, `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`. -/
theorem kummerSelmerM : ZInQ.Manuscript.PoleS12.KummerSelmerM :=
  fun ℓ h1 h2 => ZInQ.Manuscript.PoleRC.kummerSelmerM_proof ℓ h1 h2

/-- **Theorem 5.2 from the printed Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121): from
Theorem 5.3 over the genuine Selmer condition, the manuscript's Lemma 5.4
(`PoleS12.Lemma54`), BCDT Theorem A (`PoleS12.BCDTThmA`) and Kolyvagin's Theorem 1
(`PoleS12.KolyvaginThm1`). Mordell's theorem for `E_ℓ` (`PoleRC.mordellWeilM`) and the Kummer
identification (`kummerSelmerM`) are proved. -/
theorem poleCompleteness_of_restrictedConverseGenuine_final
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) : ZInQ.Manuscript.PoleCompleteness :=
  ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_mw hRC h54
    ZInQ.Manuscript.PoleS12.kummerSelmerM hB hK

end ZInQ.Manuscript.PoleS12
