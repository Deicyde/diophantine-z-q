import ZInQKernel.Contrib.FrobeniusDensity.ClosedProof

/-! Reproducible, scoped type and standard-axiom reports. No target registration. -/

open ZInQ.Contrib.FrobeniusDensity

example : T18 =
    (∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
      ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
        LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U) := rfl

#print frobenius_dense_avoiding_finite_set
#print t18_holds
#print axioms NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet
#print axioms finite_frobenius_hasNaturalDensity
#print axioms finite_frobenius_density_pos
#print axioms finite_frobenius_primes_infinite
#print axioms exists_absNorm_gt_of_infinite
#print axioms exists_finite_arithFrob_avoiding
#print axioms chebotarevExists
#print axioms chebotarevExists_C10
#print axioms exists_le_one_and_residue_eq_pow
#print axioms one_lt_map_of_one_lt
#print axioms mem_nonunits_comap_iff
#print axioms mem_decompositionSubgroup_of_congruence
#print axioms isArithFrob_iff_congruence
#print axioms apply_mem_nonunits_smul_iff
#print axioms liesOver_smul_iff
#print axioms IsArithFrob.conj
#print axioms IsArithFrob.restrictNormal
#print axioms zbarFractionRing
#print axioms localization_integer_or_inverse
#print axioms liesOver_valuationOverIntegralPrime
#print axioms isArithFrob_at_integralPrime
#print axioms exists_valuation_of_integral_frobenius
#print axioms valuation_frobLift
#print axioms exists_finiteGalois_fixingSubgroup_le
#print axioms inv_mul_mem_of_restrictNormal_eq
#print axioms frobenius_dense_avoiding_finite_set
#print axioms t18_holds
