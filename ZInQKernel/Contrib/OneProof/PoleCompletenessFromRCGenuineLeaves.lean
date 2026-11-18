import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.SelmerTwoPowerLemma54

/-!
# Theorem 5.2 from Theorem 5.3, with Lemma 5.4 from its printed and textbook inputs

`PoleS12.poleCompleteness_of_restrictedConverseGenuine_final` takes Lemma 5.4 (`PoleS12.Lemma54`,
`diophantine_zq.tex` lines 1072–1084) as a leaf. The manuscript proves that lemma from the Kummer
sequence and the Cassels–Tate pairing; `SelmerTwoPower.lemma54_of_leaves`
(`SelmerTwoPowerLemma54.lean`) proves it from the printed parity statement
`SelmerTwoPower.MazurRubinParityTwo` (Mazur–Rubin, Invent. Math. 181 (2010), §2, display (2)) and the
textbook statements `SelmerTwoPower.SelmerCofinite` and `SelmerTwoPower.KummerSelmerRelation`.
This file composes the two, as an alternative to taking `PoleS12.Lemma54` as a leaf.
-/

namespace ZInQ.Manuscript.PoleS12

/-- **Theorem 5.2 from the printed Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121), with
Lemma 5.4 derived from the Mazur–Rubin parity statement, cofinite generation of `Sel_{2^∞}` and the
Kummer-sequence count. -/
theorem poleCompleteness_of_restrictedConverseGenuine_leaves
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hP : ZInQ.Manuscript.SelmerTwoPower.MazurRubinParityTwo)
    (hC : ZInQ.Manuscript.SelmerTwoPower.SelmerCofinite)
    (hKS : ZInQ.Manuscript.SelmerTwoPower.KummerSelmerRelation)
    (hB : ZInQ.Manuscript.PoleS12.BCDTThmA) (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.Manuscript.PoleCompleteness :=
  ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final hRC
    (ZInQ.Manuscript.SelmerTwoPower.lemma54_of_leaves hP hC hKS) hB hK

end ZInQ.Manuscript.PoleS12
