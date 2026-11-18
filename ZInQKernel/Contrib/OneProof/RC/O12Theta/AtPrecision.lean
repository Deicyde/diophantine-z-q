import ZInQKernel.Contrib.OneProof.RC.O12Theta.Inputs
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Pointwise

/-! Assemble the same two inputs for a compatible realization over the entire
tested domain, using the finite-stage recurrence of the odd source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open AddressGenuine PrintsArith TraceLimits ThetaCoeff O12 ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R₀ : Finset ℕ → ZMod 2} {B : ℕ} {ap : ℕ → ℤ}
variable {X : GaloisConstituentModel T R₀ ap B χ}
variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing X.O M)} {δ : ℤ} {adm : ℕ → Prop}
variable (A : FourierData X) (E : Lift S) (D : Divisions E δ W R adm)

/-- The unchanged `Inputs` conclusion using an odd stage of sufficient
precision. This route does not require an exact integral `SourceCore` or
`RecAt`. Realization on the whole tested domain remains an input. -/
theorem inputs_at_precision
    (hgood : ∀ p, T.Good p → S.Good p) (hbudget : B ≤ W + 1)
    (hap : S.ap = ap) (hm : X.m.IsMaximal) (htyp : IsTypeChar T χ)
    (hphase : ∀ p, T.Good p → ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (hexp : ∀ U (hu : Admissible S W U), (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B →
      ∀ n, A.coeff n (X.F U) = E.FourierF D hu n)
    {avoid : Finset ℕ} (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hhecke : A.FormwiseHecke)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    (localData : LocalInput A) : X.Inputs := by
  have admissible (U : Finset ℕ) (hU : ∀ p ∈ U, T.Good p) (hB : U.card + 1 ≤ B) :
      Admissible S W U := ⟨by omega, fun p hp => hgood p (hU p hp)⟩
  refine ⟨?_, ?_⟩
  · intro U q hU hq hqU hB
    have hb : U.card + 1 ≤ B := by rwa [Finset.card_insert_of_notMem hqU] at hB
    have hu := admissible U hU hb
    refine fresh_input_of_stage A E D hbudget hm valuation hu hU hq hqU hB
      (hexp U hu hU hb q) ?_
    simpa only [mul_one] using A.trace_coeff_of_not_dvd hhecke hU hq hqU hb (n := 1)
      (fun h => hq.1.ne_one (Nat.dvd_one.mp h))
  · intro U p hpU hU hB g
    have hu := admissible U hU hB
    have hV : ∀ q ∈ U.erase p, T.Good q := fun q hq => hU q (Finset.mem_of_mem_erase hq)
    have hBV := (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset p U)) 1).trans hB
    have hv := admissible (U.erase p) hV hBV
    exact o12_at_one_of_stage A E D ops DF hDF hap hm htyp U p hpU hU hB g hu hv
      (hexp U hu hU hB) (hexp (U.erase p) hv hV hBV) (hphase p (hU p hpU))
      (localData U p hpU hU hB)

#print axioms inputs_at_precision

end ZInQ.Manuscript.RC.O12Theta
