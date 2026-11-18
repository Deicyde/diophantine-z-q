import ZInQKernel.Contrib.OneProof.KolyvWeil.Leaves
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal

namespace ZInQ.Manuscript.KolyvWeil

/-- The exact old `hK` statement is a consequence of the two prints together.
BCDT (6) supplies Kolyvagin's hypothesis, so the old cusp form argument is unused. -/
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

/-- The same pole-completeness statement as `PoleS12.poleCompleteness_of_restrictedConverseGenuine_final`
(tex `hyp:PC`, L1001–1004), replacing just its two Lemma 5.5 inputs.
The proof uses its existing Kummer, Selmer count and descent steps; at `lem:forward-rank`
(L1086–1109) it takes the rank implication from BCDT (6) and Kolyvagin. -/
theorem poleCompleteness_of_restrictedConverseGenuine_print
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hB : BCDTThmA6) (hK : KolyvaginThm1Print) :
    ZInQ.Manuscript.PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (PoleS12.lemma54At_of_printed h54 PoleS12.kummerSelmerM) (kolyvaginRankOne_of_prints hB hK))
    PoleS12.simultaneousConstruction

end ZInQ.Manuscript.KolyvWeil
