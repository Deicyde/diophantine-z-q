import ZInQKernel.Contrib.DifferentBound.Global
import ZInQKernel.Contrib.DifferentBound.Valuation
import ZInQKernel.Contrib.DifferentBound.Monogenic
import ZInQKernel.Contrib.DifferentBound.Degree
import ZInQKernel.Contrib.DifferentBound.Local
import ZInQKernel.Contrib.DifferentBound.Tower
import ZInQKernel.Contrib.DifferentBound.Transport
import ZInQKernel.Contrib.DifferentBound.UnramifiedFactor
import ZInQKernel.Contrib.DifferentBound.Generator
import ZInQKernel.Contrib.DifferentBound.SerreLocal
import ZInQKernel.Contrib.DifferentBound.Comparison
import ZInQKernel.Contrib.DifferentBound.GlobalReduction

/-!
# Focused type and axiom report for T21 component proofs

This file audits the actual proofs and displays the conditional model interfaces.
It is not a closed proof of T21: no declaration named `serreDifferentBound` with
the baseline's closed proposition is supplied by this component audit.
-/

open NumberField IsLocalRing
open ZInQ.Contrib.DifferentBound

#check @serreDifferentBound_of_ramificationIdx_eq_one
#check @primeAbove_multiplicity_natCast
#check @minpoly_natDegree_eq_ramificationIdx_of_generating_uniformizer
#check @differentIdeal_bound_of_generating_uniformizer
#check @differentIdeal_bound_of_unramified_tower
#check @serreDifferentBound_atPrime_of_local_ideal_model
#check @serreDifferentBound_atPrime_of_generating_uniformizer_model
#check @UnramifiedFactor.nonempty_of_perfect
#check @differentIdeal_bound_of_factor
#check @differentIdeal_bound_of_residue_surjective_unramified_tower
#check @localDifferentBound
#check @ramificationIdx_local_model_eq_global
#check @serreDifferentBound_atPrime_of_factor_model
#check @serreDifferentBound_atPrime_of_unramified_tower_model
#check @serreDifferentBound_atPrime_of_completeDVR_model

example : PkgI6.DifferentBound := localDifferentBound

#print axioms span_natPrime_ne_bot
#print axioms primeAbove_ne_bot
#print axioms global_ramificationIdx_pos
#print axioms global_different_ne_bot
#print axioms pow_dvd_global_different_iff
#print axioms not_pow_dvd_global_different_iff
#print axioms serreDifferentBound_of_ramificationIdx_eq_one
#print axioms serreDifferentBound_of_isUnramifiedAt
#print axioms primeAbove_intValuation_natCast
#print axioms primeAbove_multiplicity_natCast
#print axioms addValuation_sum_eq_inf_of_ne
#print axioms addVal_algebraMap
#print axioms powerBasis_term_valuations_ne
#print axioms addVal_sum_algebraMap_mul_pow
#print axioms field_adjoin_eq_top_of_ring_adjoin_eq_top
#print axioms differentIdeal_eq_span_aeval_derivative_minpoly
#print axioms minpoly_natDegree_eq_finrank_of_ring_adjoin_eq_top
#print axioms dvr_ramificationIdx_mul_residueDegree
#print axioms dvr_ramificationIdx_eq_fractionField_finrank_of_surjective_residue
#print axioms residue_surjective_of_generating_uniformizer
#print axioms minpoly_natDegree_eq_ramificationIdx_of_generating_uniformizer
#print axioms addVal_aeval_derivative_le
#print axioms differentIdeal_bound_of_generating_uniformizer
#print axioms multiplicity_differentIdeal_le_of_generating_uniformizer
#print axioms differentIdeal_eq_top_of_isUnramifiedAt
#print axioms ramificationIdx_eq_of_unramified_tower
#print axioms differentIdeal_eq_of_unramified_tower
#print axioms differentIdeal_bound_of_unramified_tower
#print axioms multiplicity_map_eq_of_prime_maps_to_maximal
#print axioms multiplicity_le_of_dvd_maximalIdeal_pow_mul_span
#print axioms serreDifferentBound_atPrime_of_local_ideal_model
#print axioms serreDifferentBound_atPrime_of_generating_uniformizer_model
#print axioms UnramifiedFactor.nonempty_of_perfect
#print axioms UnramifiedFactor.nonempty_of_finite_residue
#print axioms adjoin_eq_top_of_residue_surjective_uniformizer
#print axioms differentIdeal_bound_of_factor
#print axioms differentIdeal_bound_of_residue_surjective_unramified_tower
#print axioms differentIdeal_bound_completeDVR
#print axioms localDifferentBound
#print axioms ramificationIdx_local_model_eq_global
#print axioms serreDifferentBound_atPrime_of_factor_model
#print axioms serreDifferentBound_atPrime_of_unramified_tower_model
#print axioms serreDifferentBound_atPrime_of_completeDVR_model

-- Dyadic and odd primes require no additional assumption in the proved unramified case.
example (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (he : P.ramificationIdx ℤ = 1) : ¬ P ^ 1 ∣ differentIdeal ℤ (𝓞 L) := by
  simpa [he] using serreDifferentBound_of_ramificationIdx_eq_one L 2 P he

example (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (he : P.ramificationIdx ℤ = 1) : ¬ P ^ 1 ∣ differentIdeal ℤ (𝓞 L) := by
  simpa [he] using serreDifferentBound_of_ramificationIdx_eq_one L 3 P he

-- Empty and all-zero families retain infinite additive valuation, rather than a fake finite one.
example {R : Type*} [Ring R] (v : AddValuation R ℕ∞) :
    v (∑ _i : Fin 0, (0 : R)) = ⊤ := by simp

example {R : Type*} [Ring R] (v : AddValuation R ℕ∞) (m : ℕ) :
    v (∑ _i : Fin m, (0 : R)) = ⊤ := by simp

-- If the ramification index vanishes in the extension ring, the ideal-form local bound is empty.
example {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B]
    (he : ((maximalIdeal B).ramificationIdx A : B) = 0) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} := by
  simp [he]
