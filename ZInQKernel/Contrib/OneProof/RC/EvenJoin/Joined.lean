import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Complete

/-! The fixed actual even form and its transfer to the budget model. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget EvenExpansion ModularForm O12 ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped ModularForm

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}

private theorem unary_on_subscripts (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) :
    ∀ j ∈ subscripts U, EvenUnaryStageLaw P hS i j := by
  intro j hj
  exact EvenUnary.evenUnaryStageLaw P hS i
    (Nat.pos_of_ne_zero ((mem_subscripts (fun p hp => (hU p hp).1) j).mp hj).1.ne_zero)

private theorem exists_joinedForm (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ f : WeightTwo (movingLevel P U), ∀ n, (qExpansion 1 f).coeff n =
      timesTheta (halfDivided (evenTypes W.S hS.1).Good
        (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n := by
  obtain ⟨_, _, _, _, f, _, _, _, _, _, _, _, _, hf⟩ :=
    EvenMoving.evenWeightTwo_from_unary hS i U hU hodd (unary_on_subscripts hS i U hU)
  exact ⟨f, hf⟩

/-- The form supplied by the moving and unary transformations, at the level for this set. -/
def joinedForm (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    WeightTwo (movingLevel P U) :=
  (exists_joinedForm hS i U hU hodd).choose

theorem joinedForm_coeff (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (n : ℕ) :
    (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n =
      timesTheta (halfDivided (evenTypes W.S hS.1).Good
        (fun p => P.phaseData.η p) P.sievedCoeff P.δ i U.toList) n :=
  (exists_joinedForm hS i U hU hodd).choose_spec n

variable (hS : SupportSpec W) {B : ℕ} [NeZero (conductor W.S)]
variable {X : Model P hS B} [CharZero X.K] (A : FourierData X)
variable (C : SourceAtPlace P X.O X.K)

/-- Transfer at the fixed place once the model form is identified with the actual expansion.
The moving sieve and each unary shell use the proved laws. -/
theorem evenExpansion_joined (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
    (hcoord : ∀ n, n ≠ 0 →
      κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
        (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n) :
    ∀ n, n ≠ 0 → A.coeff n (X.F U) = timesTheta (evenH hS A C i U) n :=
  evenExpansion hS A C i U hU (joinedForm hS i U hU hodd)
    (joinedForm_coeff hS i U hU hodd) κ hκ hcoord

/-- Use a single comparison and coefficient place across the entire operator budget. -/
theorem budgetRealization_of_joined (i : Fin 2)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (κ : X.K →+* ℂ) (hκ : κ.comp C.eK = C.eC)
    (hcoord : ∀ (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p),
      U.card + 1 ≤ B → ∀ n, n ≠ 0 →
        κ (algebraMap X.O X.K (A.coeff n (X.F U))) =
          (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n)
    (hm : X.m.IsMaximal)
    (hphase : ∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C.η p ^ (2 ^ t) = 1)
    (hHecke : A.FormwiseHecke)
    (localBlocks : ∀ (U : Finset ℕ) (q : ℕ) (hqU : q ∈ U)
      (hU : ∀ s ∈ U, (evenTypes W.S hS.1).Good s),
      U.card + 1 ≤ B → ∀ Q : O12.LocalPair q,
      letI : Fact q.Prime := ⟨(hU q hqU).1⟩
      Nonempty (O12Local.Stage A U Q (hU q hqU).1.ne_zero)) :
    P.BudgetRealization hS B :=
  budgetRealization_of_blocks hS A C i hm hphase hHecke
    (fun U hU hB => evenExpansion_joined hS A C i U hU hodd κ hκ (hcoord U hU hB))
    localBlocks

end ZInQ.Manuscript.RC.EvenJoin
