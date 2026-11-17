import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCCore2
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuine
import ZInQKernel.Contrib.OneProof.PoleCompletenessIntegrated
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCLocal

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


/-- Duplicates, local images: the cloud's `LocalGood` (an iff, but for squarefree `a, b` only)
gives round 2's `LocalGoodUnram` (the "if" half, for all `a, b`) restricted to squarefree `a, b`;
conversely round 2's gives the cloud's "if" half. Neither implies the other as stated. -/
example (ℓ p : ℕ) [Fact p.Prime] (a b : ℤ) (hsf : Squarefree ℓ) (hp : ¬ p ∣ 6 * ℓ)
    (ha' : Squarefree a) (hb' : Squarefree b) (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    LocM ℚ_[p] ℓ a b :=
  (PoleRC.localGood ℓ p a b hsf hp ha' hb').mpr ⟨ha, hb⟩

example (ℓ p : ℕ) [Fact p.Prime] (a b : ℤ) (hsf : Squarefree ℓ) (hp : ¬ p ∣ 6 * ℓ)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) : LocM ℚ_[p] ℓ a b :=
  PoleS12.localGoodUnram ℓ p a b hsf hp ha hb

/-- Duplicates: the cloud's four local images give round 2's `necAt_S12` conclusion. -/
example (ℓ : ℕ) (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) : NecAt ℓ :=
  necAt_of_local localTwo localThree localBad localGood hsf h12

#check @PoleS12.necAt_S12
#check @PoleS12.localGoodUnram
#check @PoleS12.dimThreeCount_S12

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
#print axioms ZInQ.Manuscript.PCReview.poleCompleteness_of_restrictedConverseGenuine_integrated
#print axioms ZInQ.Manuscript.PCReview.poleCompleteness_of_restrictedConverseGenuine_integrated'
#print axioms ZInQ.Manuscript.PCReview.poleCompleteness_of_restrictedConverseGenuine_integratedPrinted
#print axioms ZInQ.Manuscript.PoleS12.matrixRealization
#print axioms ZInQ.Manuscript.PoleS12.dimThreeCount
#print axioms ZInQ.Manuscript.PoleS12.simultaneousConstruction
#print axioms ZInQ.Manuscript.PoleS12.localGoodUnram
#print axioms ZInQ.Manuscript.PoleRC.mordellWeil_curve
#print axioms ZInQ.Manuscript.KolyvCST.kolyvaginRankOne_of_forwardRank
