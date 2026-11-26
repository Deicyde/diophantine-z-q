import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.FieldGenusDivisibility
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.FromOesterleGenus

/-! Fowler's bound using only Oesterlé's estimate for the actual fraction field. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

/-- Fowler, Proposition 2.7, on the given imaginary quadratic order. The only
arithmetic input is Oesterlé's effective estimate for its fraction field. -/
theorem fowler_bound_of_oesterle {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) (ho : OesterleFieldBound K)
    (n : ℕ) (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) :=
  fowler_bound_of_oesterle_and_genus O hK ho (fieldGenusDivisibility_proved hK) n hn hh

end HDec.CMBranch.FowlerArithmetic
