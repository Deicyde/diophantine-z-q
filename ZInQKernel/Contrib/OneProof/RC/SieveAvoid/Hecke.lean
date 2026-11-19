import ZInQKernel.Contrib.OneProof.RC.O12.Build

/-! Separate the allowed formwise tests from the ambient Hecke tests
(tex 9660–9668, 9670–9674). -/

noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open AddressGenuine PrintsArith TraceLimits O12
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {χ : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B χ}

abbrev GoodPrime (T : TypeData L ε) (Scoeff : Finset ℕ) (q : ℕ) : Prop :=
  T.Good q ∧ q ∉ Scoeff

abbrev GoodSet (T : TypeData L ε) (Scoeff U : Finset ℕ) : Prop :=
  ∀ p ∈ U, GoodPrime T Scoeff p

/-- The integral Fourier identity on one form and one prime. -/
def HeckeAt (A : FourierData X) (U : Finset ℕ) (q : ℕ) : Prop :=
  ∃ diamondF : X.Λ, ∀ n,
    A.coeff n (X.tΛ (X.frob q) (X.F U)) =
      A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0

/-- Only the permitted formwise tests omitted by the ambient level. -/
def Hexcl' (A : FourierData X) (Scoeff avoid : Finset ℕ) : Prop :=
  ∀ U q, GoodSet T Scoeff U → T.Good q → q ∉ Scoeff ∪ U →
    U.card + 1 ≤ B → q ∈ avoid → HeckeAt A U q

/-- The good Hecke formula at the actual tested pairs. -/
def FormwiseHecke' (A : FourierData X) (Scoeff : Finset ℕ) : Prop :=
  ∀ U q, GoodSet T Scoeff U → T.Good q → q ∉ Scoeff ∪ U →
    U.card + 1 ≤ B → HeckeAt A U q

theorem formwiseHecke_of_ambient (A : FourierData X) {Scoeff avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (D : ∀ U, DeterminantFourierData ops X.m (X.F U))
    (hD : ∀ U, (D U).coeff = A.coeff)
    (hexcl : Hexcl' A Scoeff avoid) : FormwiseHecke' A Scoeff := by
  intro U q hU hq hf hB
  by_cases hqa : q ∈ avoid
  · exact hexcl U q hU hq hf hB hqa
  · exact A.goodHecke_of_data ops U (D U) (hD U) hq hqa

/-- The good Hecke reading at an index prime to the tested prime. -/
theorem trace_coeff_of_not_dvd {A : FourierData X} {Scoeff U : Finset ℕ} {q n : ℕ}
    (H : FormwiseHecke' A Scoeff) (hU : GoodSet T Scoeff U) (hq : T.Good q)
    (hf : q ∉ Scoeff ∪ U) (hB : U.card + 1 ≤ B) (hn : ¬ q ∣ n) :
    A.coeff n (X.tΛ (X.frob q) (X.F U)) = A.coeff (q * n) (X.F U) := by
  obtain ⟨_, h⟩ := H U q hU hq hf hB
  rw [h, ite_eq_right hn, add_zero]

/-- The ambient comparison and (coefficient-one) formwise comparison can
be combined without ever testing a sieve prime. -/
theorem ambient_trace_at_one {A : FourierData X} {Scoeff avoid U : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (D : DeterminantFourierData ops X.m (X.F U)) (hD : D.coeff = A.coeff)
    (hexcl : ∀ q, T.Good q → q ∉ Scoeff ∪ U → q ∈ avoid →
      A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U))
    {q : ℕ} (hq : T.Good q) (hf : q ∉ Scoeff ∪ U) :
    A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U) := by
  by_cases h : q ∈ avoid
  · exact hexcl q hq hf h
  · obtain ⟨_, hh⟩ := A.goodHecke_of_data ops U D hD hq h
    rw [hh, mul_one, ite_eq_right (fun e => hq.1.ne_one (Nat.dvd_one.mp e)), add_zero]

#print axioms formwiseHecke_of_ambient
#print axioms trace_coeff_of_not_dvd
#print axioms ambient_trace_at_one

end ZInQ.Manuscript.RC.SieveAvoid
