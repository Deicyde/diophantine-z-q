import ZInQKernel.Contrib.DifferentBound.SerreLocal
import ZInQKernel.Contrib.DifferentBound.Comparison

/-!
# Exact pointwise global conclusions from proved local bounds and matched models

These theorems are explicitly conditional on a genuine global/local ideal
comparison. They do not construct a model for every number field and are not
closed providers for `GlueConductor.SerreDifferentBound`.

The supplied-factor and supplied-tower interfaces use no completeness or
perfectness hypothesis. The complete-model interface uses those properties only
on its constructed local rings, not as assumptions on the global number field.
-/

namespace ZInQ.Contrib.DifferentBound

open NumberField IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Conditional exact global result from an actual supplied factor model.** All local Serre
arithmetic is proved; only the displayed global/local ring and ideal identifications remain
model inputs. The ramification-index equality is derived, not assumed. -/
theorem serreDifferentBound_atPrime_of_factor_model
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra (𝓞 L) B] [FaithfulSMul (𝓞 L) B]
    (hbase : maximalIdeal A = Ideal.span {(p : A)})
    (hmapP : P.map (algebraMap (𝓞 L) B) = maximalIdeal B)
    (hmapD : (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B)
    (F : UnramifiedDVRFactor A B) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound_atPrime_of_local_ideal_model L p hp P A B hmapP hmapD
    (ramificationIdx_local_model_eq_global L p hp P A B hbase hmapP)
    (differentIdeal_bound_of_factor A B F)

/-- **Conditional exact global result from a supplied unramified, residue-surjective DVR
 tower.** No completeness, perfectness, monogenicity, degree equality, Hilbert formula, or Serre
bound is an input. The global/local different identity is still a required proved model fact. -/
theorem serreDifferentBound_atPrime_of_unramified_tower_model
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (A U B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A U] [Algebra U B] [Algebra A B] [IsScalarTower A U B]
    [Module.Finite A U] [Module.Finite U B] [Module.Finite A B]
    [Module.IsTorsionFree A U] [Module.IsTorsionFree U B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (maximalIdeal U)]
    [Algebra (𝓞 L) B] [FaithfulSMul (𝓞 L) B]
    (hbase : maximalIdeal A = Ideal.span {(p : A)})
    (hmapP : P.map (algebraMap (𝓞 L) B) = maximalIdeal B)
    (hmapD : (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B)
    (hres : Function.Surjective ((residue B).comp (algebraMap U B))) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound_atPrime_of_local_ideal_model L p hp P A B hmapP hmapD
    (ramificationIdx_local_model_eq_global L p hp P A B hbase hmapP)
    (differentIdeal_bound_of_residue_surjective_unramified_tower A U B hres)

/-- **Conditional exact global result from a genuine complete DVR model.** This consumes the
closed local bound, and derives the ramification normalization from the prime-image facts.
It is not a construction of such a model for every allowed `L,p,P`. -/
theorem serreDifferentBound_atPrime_of_completeDVR_model
    (L : Type*) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra (𝓞 L) B] [FaithfulSMul (𝓞 L) B]
    (hbase : maximalIdeal A = Ideal.span {(p : A)})
    (hmapP : P.map (algebraMap (𝓞 L) B) = maximalIdeal B)
    (hmapD : (differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound_atPrime_of_local_ideal_model L p hp P A B hmapP hmapD
    (ramificationIdx_local_model_eq_global L p hp P A B hbase hmapP)
    (differentIdeal_bound_completeDVR A B)

#check @serreDifferentBound_atPrime_of_factor_model
#check @serreDifferentBound_atPrime_of_unramified_tower_model
#check @serreDifferentBound_atPrime_of_completeDVR_model
#print axioms serreDifferentBound_atPrime_of_factor_model
#print axioms serreDifferentBound_atPrime_of_unramified_tower_model
#print axioms serreDifferentBound_atPrime_of_completeDVR_model

end ZInQ.Contrib.DifferentBound
