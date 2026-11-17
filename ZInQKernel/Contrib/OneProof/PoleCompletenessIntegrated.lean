import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCCore2
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuine
import ZInQKernel.Contrib.OneProof.KolyvCST.Kolyvagin

/-!
# Theorem 5.2 from the printed Theorem 5.3: rounds 1–2 and the cloud deliverables integrated

Task pc-review (fork issue #83). Report: `docs/research/pc-review.md`.

`poleCompleteness_of_restrictedConverseGenuine_integrated` proves `Manuscript.PoleCompleteness`
(Theorem 5.2, `diophantine_zq.tex` L1019–1121) from Theorem 5.3 over the genuine Selmer
condition (`SelmerTwoPower.RestrictedConverseGenuine`), with

* round 2's printed leaves for Lemma 5.4 (`PoleS12.Lemma54`, Poonen–Stoll) and Lemma 5.5
  (`PoleS12.BCDTThmA`, `PoleS12.KolyvaginThm1`) and its glue statement `PoleS12.KummerSelmerM`
  (Silverman X.1.4, not proved in Lean);
* the cloud's proof of Mordell's theorem for the curves `E_ℓ` (`PoleRC.mordellWeilM`), so the
  hypothesis `MordellWeil` of round 2's `poleCompleteness_of_restrictedConverseGenuine` is gone;
* the cloud's `Simul.matrixRealization` and `PoleRC.dimThreeCount` (round 2 proves the same two
  Props independently: `PoleS12.matrixRealization`, `PoleS12.dimThreeCount`).

Nothing new is proved here: this file only composes.
-/

namespace ZInQ.Manuscript.PCReview

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.SelmerTwoPower

/-- The cloud's `hK : KolyvaginRankOne` discharged by round 2's printed leaves (abstract `P`). -/
theorem poleCompleteness_of_restrictedConverse_printedK (P : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse P) (h54 : Lemma54At P) (hB : BCDTThmA) (hK : KolyvaginThm1) :
    Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_core2 P hRC h54 (kolyvaginRankOne_of_printed hB hK)

/-- **Theorem 5.2 from the printed Theorem 5.3, integrated.** Remaining hypotheses: Theorem 5.3
(`RestrictedConverseGenuine`, open), the printed leaves `Lemma54`, `BCDTThmA`, `KolyvaginThm1`,
and the textbook glue `KummerSelmerM`. -/
theorem poleCompleteness_of_restrictedConverseGenuine_integrated
    (hRC : RestrictedConverseGenuine) (h54 : Lemma54) (hKum : KummerSelmerM)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_core2 SelmerCorankOne hRC
    (lemma54At_of_printed h54 hKum) (kolyvaginRankOne_of_printed hB hK)

/-- The same from round 2's own route (its `matrixRealization`, `dimThreeCount`) with the cloud's
Mordell–Weil: `mordellWeilM` replaces `MordellWeil` in `crm_of_restrictedConverse`. -/
theorem poleCompleteness_of_restrictedConverseGenuine_integrated'
    (hRC : RestrictedConverseGenuine) (h54 : Lemma54) (hKum : KummerSelmerM)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm
    (crm_of_restrictedConverse_M SelmerCorankOne hRC (lemma54At_of_printed h54 hKum)
      (kolyvaginRankOne_of_printed hB hK) mordellWeilM descentGlueM)
    PoleS12.simultaneousConstruction

/-- The same with kolyv-cst-printed's `KolyvaginThm1Printed` (Kolyvagin Theorem 1 for `r ≤ 1`, the
form cited at tex L1093) in place of round 2's `KolyvaginThm1` (its `r = 1` case,
`KolyvCST.kolyvaginThm1_of_printed`). Same number of hypotheses; the theorem above is the stronger
result, since `KolyvaginThm1` is the weaker hypothesis. -/
theorem poleCompleteness_of_restrictedConverseGenuine_integratedPrinted
    (hRC : RestrictedConverseGenuine) (h54 : Lemma54) (hKum : KummerSelmerM)
    (hB : BCDTThmA) (hK : KolyvCST.KolyvaginThm1Printed) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_core2 SelmerCorankOne hRC
    (lemma54At_of_printed h54 hKum)
    (KolyvCST.kolyvaginRankOne_of_forwardRank (KolyvCST.forwardRank_of_printed hB hK))

end ZInQ.Manuscript.PCReview
