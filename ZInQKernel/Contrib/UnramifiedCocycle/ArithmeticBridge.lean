import ZInQKernel.Contrib.UnramifiedCocycle.FiniteQuotient
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The integral unramified hypothesis, without a hidden local-field conclusion

The baseline's prime-by-prime ramification-index condition is connected to
Mathlib's actual commutative-algebra predicate.  This establishes that part of
the arithmetic bridge, not the existence of a residue Frobenius quotient or its
lift through the doubled cyclic level.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q NumberField

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]

/-- A prime above `p` is unramified in the genuine commutative-algebra sense. -/
theorem unramifiedAt_prime (p : Nat.Primes) (hu : UnramifiedAt L p)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hp : ((p : ℤ) : 𝓞 L) ∈ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  exact Ideal.ramificationIdx_eq_one_iff.mp (hu P inferInstance hp)

/-- Conversely, prime-by-prime unramifiedness gives exactly the original
ramification-index predicate.  Neither direction changes its index set. -/
theorem unramifiedAt_iff_prime (p : Nat.Primes) :
    UnramifiedAt L p ↔
      ∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((p : ℤ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt ℤ P := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  constructor
  · intro hu P _ hp
    exact unramifiedAt_prime L p hu P hp
  · intro hu P hP hp
    let : P.IsPrime := hP
    exact Ideal.ramificationIdx_eq_one_iff.mpr (hu P hp)

end ZInQ.Contrib.UnramifiedCocycle
