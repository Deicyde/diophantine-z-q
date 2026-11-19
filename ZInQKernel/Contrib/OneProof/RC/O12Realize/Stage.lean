import ZInQKernel.Contrib.OneProof.RC.O12Realize.Consumers
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Inputs
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Pointwise

/-! Readings at one actual odd stage on a common space for a fixed set and
its subsets. The finite-precision recurrence is the one used in the
pointwise identities (tex 9699–9704, 9916–9918). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Realize

open AddressGenuine PrintsArith TraceLimits ThetaCoeff O12 O12Theta
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R₀ : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {X : GaloisConstituentModel T R₀ ap B χ}
variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]
variable {M W R : ℕ} {δ : ℤ} {adm : ℕ → Prop} {S : AppF.ThetaStage (StageRing X.O M)}
variable (A : FourierData X) (E : Lift S) (D : Divisions E δ W R adm)

/-- Actual expansions on the subsets of just one root. Each admissibility
proof uses the same stage, and all coefficients use the same lift. -/
def ExpansionsOn (U : Finset ℕ) : Prop :=
  ∀ V ⊆ U, ∃ hV : Admissible S W V, ∀ n, A.coeff n (X.F V) = E.FourierF D hV n

/-- The exact additional good-Hecke comparison needed for prescribed
primes excluded from the common space's ambient tests: only at the root
and coefficient one. -/
def ExcludedAtOne (U avoid : Finset ℕ) : Prop :=
  ∀ q, T.Good q → q ∉ U → q ∈ avoid →
    A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U)

/-- The fixed-set restriction of the existing same-lattice local input. -/
def LocalOn (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) : Prop :=
  ∀ p (hpU : p ∈ U), ∀ P : LocalPair p, ∃ Dp : LocalBlocks X U P, A.UpAtOne Dp (hU p hpU).1.ne_zero

variable {A E D}

private theorem fresh_at_on_stage {U V : Finset ℕ} (hVU : V ⊆ U)
    (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1)
    (hexp : ExpansionsOn A E D U) (hm : X.m.IsMaximal)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    {q : ℕ} (hq : T.Good q) (hqV : q ∉ V)
    (htrace : A.coeff 1 (X.tΛ (X.frob q) (X.F V)) = A.coeff q (X.F V)) :
    FreshAt X V q := by
  obtain ⟨hv, hfv⟩ := hexp V hVU
  have hc : (insert q V).card ≤ B := by
    rw [Finset.card_insert_of_notMem hqV]
    exact (Nat.add_le_add_right (Finset.card_le_card hVU) 1).trans hB
  exact fresh_input_of_stage A E D hbudget hm valuation hv
    (fun p hp => hU p (hVU hp)) hq hqV hc (hfv q) htrace

omit [CharZero X.O] [IsDomain X.O] [CharZero X.K] in
private theorem trace_one_of_good_data {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ) {V : Finset ℕ}
    (DF : DeterminantFourierData ops X.m (X.F V)) (hDF : DF.coeff = A.coeff)
    {q : ℕ} (hq : T.Good q) (hqa : q ∉ avoid) :
    A.coeff 1 (X.tΛ (X.frob q) (X.F V)) = A.coeff q (X.F V) := by
  obtain ⟨_, hh⟩ := A.goodHecke_of_data ops V DF hDF hq hqa
  have hn : ¬ q ∣ 1 := fun h => hq.1.ne_one (Nat.dvd_one.mp h)
  rw [hh, mul_one, ite_eq_right hn, add_zero]

/-- The pointwise stage identities supply the two readings in one window.
Only the actual expansions on its subsets are required. -/
theorem readings_on_of_stage {U avoid : Finset ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1)
    (hexp : ExpansionsOn A E D U) (hm : X.m.IsMaximal) (hap : S.ap = ap) (htyp : IsTypeChar T χ)
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ V, DeterminantFourierData ops X.m (X.F V)) (hDF : ∀ V, (DF V).coeff = A.coeff)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    (hphase : ∀ p ∈ U, ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (localData : LocalOn A U hU) : ReadingsOn X U avoid := by
  refine ⟨?_, ?_⟩
  · intro V hVU q hq hqV hqa
    exact fresh_at_on_stage hVU hU hB hbudget hexp hm valuation hq hqV
      (trace_one_of_good_data ops (DF V) (hDF V) hq hqa)
  · intro p hpU g
    obtain ⟨hu, hfu⟩ := hexp U (Finset.Subset.refl U)
    obtain ⟨hv, hfv⟩ := hexp (U.erase p) (Finset.erase_subset p U)
    exact o12_at_one_of_stage A E D ops DF hDF hap hm htyp
      U p hpU hU hB g hu hv hfu hfv (hphase p hpU) (localData p hpU)

/-- Extend the root reading to a prescribed fresh prime. On the ambient
domain use the proved reading; otherwise use only the comparison at one. -/
theorem root_readings_of_stage {U avoid : Finset ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1)
    (hexp : ExpansionsOn A E D U) (hm : X.m.IsMaximal)
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : DeterminantFourierData ops X.m (X.F U)) (hDF : DF.coeff = A.coeff)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    (hexcl : ExcludedAtOne A U avoid) :
    ∀ q, T.Good q → q ∉ U → FreshAt X U q := by
  intro q hq hqU
  apply fresh_at_on_stage (Finset.Subset.refl U) hU hB hbudget hexp hm valuation hq hqU
  by_cases hqa : q ∈ avoid
  · exact hexcl q hq hqU hqa
  · exact trace_one_of_good_data ops DF hDF hq hqa

end ZInQ.Manuscript.RC.O12Realize

#print axioms ZInQ.Manuscript.RC.O12Realize.fresh_at_on_stage
#print axioms ZInQ.Manuscript.RC.O12Realize.trace_one_of_good_data
#print axioms ZInQ.Manuscript.RC.O12Realize.readings_on_of_stage
#print axioms ZInQ.Manuscript.RC.O12Realize.root_readings_of_stage
