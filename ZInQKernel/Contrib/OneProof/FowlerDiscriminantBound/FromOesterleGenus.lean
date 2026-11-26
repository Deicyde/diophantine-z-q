import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.CoxFromConductorKernel
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorUnitKernel

/-!
# The conductor formula and the Fowler bound

The class-number product in Cox, Theorem 7.24, follows from the conductor-unit exactness
and the residue counts. The local factors use the splitting sign, which suffices for
Fowler's estimate without a separate comparison to the discriminant Kronecker symbol.
-/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The conductor product needed in Fowler's estimate is proved for the given quadratic order. -/
theorem coxConductorProduct_proved (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) :
    CoxConductorProduct O :=
  coxConductorProduct_of_conductor_kernel O hK (ker_conductorUnitsToPic O)

/-- Fowler's estimate on the given order from the effective bound and genus divisibility
for its fraction field. The conductor product and unit-index estimates are proved. -/
theorem fowler_bound_of_oesterle_and_genus [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (ho : OesterleFieldBound K) (hg : FieldGenusDivisibility K)
    (n : ℕ) (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) :=
  fowler_bound_of_conductor_product O hK ho hg (coxConductorProduct_proved O hK) n hn hh

end HDec.CMBranch.FowlerArithmetic
