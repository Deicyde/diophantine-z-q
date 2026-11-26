import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.GenusFromRamifiedMap
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.DiscriminantGenusMap

/-! Genus divisibility for the actual class number of an imaginary quadratic field. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField

/-- The class number of an imaginary quadratic field is divisible by `2^(t-1)`
for `t` the number of distinct prime divisors of the field discriminant. -/
theorem fieldGenusDivisibility_proved {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (hk : Module.finrank ℚ K = 2) :
    2 ^ ((NumberField.discr K).natAbs.primeFactors.card - 1) ∣ classNumber K := by
  classical
  exact genus_dvd_of_ramified_genus_map hk (genusRamifiedPrime hk) (genusRamifiedPrime_sq hk)
    (genusInteger_injective (fun p => Nat.prime_of_mem_primeFactors p.2) Subtype.val_injective)
    (genusInteger_squarefree (fun p => Nat.prime_of_mem_primeFactors p.2) Subtype.val_injective)

end HDec.CMBranch.FowlerArithmetic
