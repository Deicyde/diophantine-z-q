import Mathlib
open IsDedekindDomain
#check @ValuationSubring.mem_nonunits_iff
#check @ValuationSubring.valuation_le_one_iff
#check @ValuationSubring.inv_mem_nonunits_iff
#check @ValuationSubring.mem_or_inv_mem
#check @Valuation.Integer.isUnit_iff_valuation_eq_one
#check @IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
#check @Ideal.ramificationIdx'_eq_ramificationIdx
#check @Ideal.ramificationIdxIn_eq_ramificationIdx
#check @Ideal.eq_prime_pow_mul_coprime
#check @WithZero.lt_one_iff_le_exp_neg_one
#check @HeightOneSpectrum.intValuation_eq_exp_neg_one_of_mem_of_notMem_sq
#check @PrincipalIdealRing.isMaximal_of_irreducible
#check @IsIntegrallyClosed.isIntegral_iff
#check @IntermediateField.inclusion
#check @Ideal.map_span
#check @WeierstrassCurve.Affine.Point.map_injective
#check @WeierstrassCurve.Affine.baseChange_nonsingular
example (K : Type) [Field K] : Normal K (AlgebraicClosure K) := inferInstance
example (K : Type) [Field K] (V : ValuationSubring K) : IsIntegrallyClosed V := inferInstance
example (K : Type) [Field K] (V : ValuationSubring K) : IsFractionRing V K := inferInstance
example (k : Type) [Field k] (L : Type) [Field L] [Algebra (RatFunc k) L] [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L] [FiniteDimensional (RatFunc k) L] [CharZero k]: Module.Flat (Polynomial k) (integralClosure (Polynomial k) L) := inferInstance
example (k : Type) [Field k] (L : Type) [Field L] [Algebra (RatFunc k) L] [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L] [FiniteDimensional (RatFunc k) L] [CharZero k]: IsDedekindDomain (integralClosure (Polynomial k) L) := inferInstance
example (k : Type) [Field k] (L : Type) [Field L] [Algebra (RatFunc k) L] [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L] [FiniteDimensional (RatFunc k) L] [CharZero k]: IsFractionRing (integralClosure (Polynomial k) L) L := inferInstance
example (k : Type) [Field k] (L : Type) [Field L] [Algebra (RatFunc k) L] [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L] [FiniteDimensional (RatFunc k) L] [CharZero k]: Module.Finite (Polynomial k) (integralClosure (Polynomial k) L) := inferInstance
