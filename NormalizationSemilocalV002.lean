import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Semilocality of finite Dedekind algebras over a DVR -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {R C : Type*} [CommRing R] [CommRing C]

/-- All maximal ideals lie over the unique base maximal ideal, whose primes in
a Dedekind algebra form a finite set. -/
theorem finite_maximal_normalization [IsDomain R] [IsDiscreteValuationRing R]
    [IsDedekindDomain C] [Algebra R C] [Module.Finite R C] [Module.IsTorsionFree R C] :
    {P : Ideal C | P.IsMaximal}.Finite := by
  let p := IsLocalRing.maximalIdeal R
  apply (IsDedekindDomain.primesOver_finite p C).subset
  intro P hP
  letI : P.IsMaximal := hP
  refine ⟨hP.isPrime, ?_⟩
  rw [Ideal.liesOver_iff]
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (S := C) P)).symm

end FiniteExtensionValuation
