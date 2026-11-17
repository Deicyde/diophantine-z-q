import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCCore2
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuine

/-! pc-review step 3: the cloud's `hK : KolyvaginRankOne` discharged by round 2's printed leaves. -/

namespace ZInQ.Manuscript.PCReview

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.SelmerTwoPower

/-- Cloud core (abstract P) with round 2's `kolyvaginRankOne_of_printed` for `hK`. -/
theorem core_printedK (P : WeierstrassCurve ℚ → Prop) (hRC : RestrictedConverse P)
    (h54 : Lemma54At P) (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_core2 P hRC h54 (kolyvaginRankOne_of_printed hB hK)

/-- Integrated: Theorem 5.2 from the printed Theorem 5.3, without `MordellWeil`. -/
theorem integrated (hRC : RestrictedConverseGenuine) (h54 : Lemma54) (hKum : KummerSelmerM)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_core2 SelmerCorankOne hRC
    (lemma54At_of_printed h54 hKum) (kolyvaginRankOne_of_printed hB hK)

/-- Duplicates: both proofs inhabit the same Props. -/
example : PoleS12.matrixRealization = Simul.matrixRealization := rfl  -- proof irrelevance
example : PoleS12.dimThreeCount = PoleRC.dimThreeCount := rfl

#check @Simul.matrixRealization
#check @PoleS12.matrixRealization
#check @PoleRC.dimThreeCount
#check @PoleS12.dimThreeCount
#check @PoleRC.mordellWeilM
#check @PoleRC.mordellWeil_curve

end ZInQ.Manuscript.PCReview

#print axioms ZInQ.Manuscript.PCReview.integrated
#print axioms ZInQ.Manuscript.PCReview.core_printedK
#print axioms ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_core
#print axioms ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_coreM
#print axioms ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_core2
#print axioms ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_localProved
#print axioms ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_matrix
#print axioms ZInQ.Manuscript.PoleRC.simultaneousConstruction_of_local
#print axioms ZInQ.Manuscript.PoleRC.dimThreeCount
#print axioms ZInQ.Manuscript.PoleRC.Simul.matrixRealization
#print axioms ZInQ.Manuscript.PoleRC.localTwo
#print axioms ZInQ.Manuscript.PoleRC.localThree
#print axioms ZInQ.Manuscript.PoleRC.localBad
#print axioms ZInQ.Manuscript.PoleRC.localGood
#print axioms ZInQ.Manuscript.PoleRC.mordellWeilM
#print axioms ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine
#print axioms ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverse_abstract
