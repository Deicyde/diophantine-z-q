import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.UnitIndex

/-! Fowler's bound with the order-unit index estimates discharged. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Cox, Theorem 7.24, on this order, with the local symbols used only through their
upper bound by one. The field and order class numbers and the unit index are fixed. -/
def CoxConductorProduct (O : NumberFieldOrder K) : Prop :=
  ∃ s : ℕ → ℤ, (∀ p ∈ O.index.primeFactors, s p ≤ 1) ∧
    (Nat.card (Pic O) : ℝ) * (quadraticOrderUnitIndex O : ℝ) =
      (classNumber K : ℝ) * (O.index : ℝ) *
        ∏ p ∈ O.index.primeFactors, (1 - (s p : ℝ) / (p : ℝ))

/-- The order-unit index conditions in the conductor reading are consequences of the
field being imaginary quadratic, including at the two exceptional discriminants. -/
theorem coxConductorData_of_product [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) (hc : CoxConductorProduct O) :
    CoxConductorData O :=
  ⟨quadraticOrderUnitIndex_le_three O hK, quadraticOrderUnitIndex_eq_one O hK, hc⟩

/-- Fowler, Proposition 2.7, on a given imaginary quadratic order from the effective
estimate, genus divisibility and Cox's conductor product. No unit-index bound is assumed. -/
theorem fowler_bound_of_conductor_product [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (ho : OesterleFieldBound K) (hg : FieldGenusDivisibility K) (hc : CoxConductorProduct O)
    (n : ℕ) (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) :=
  fowler_bound_of_order_readings O hK ho hg (coxConductorData_of_product O hK hc) n hn hh

end HDec.CMBranch.FowlerArithmetic
