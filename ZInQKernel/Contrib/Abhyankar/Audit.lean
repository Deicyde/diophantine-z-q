import ZInQKernel.Contrib.Abhyankar.General
import ZInQKernel.Contrib.Abhyankar.One
import ZInQKernel.Contrib.Abhyankar.Kummer
import ZInQKernel.Contrib.Abhyankar.DvrInclusion

/-!
# Reproducible scoped type and axiom report for T2

This reports the exact baseline provider type and its actual axiom dependencies.
It is not a registration, controller decision, or independent acceptance.
-/

set_option pp.universes true

#check ZInQ.Contrib.Abhyankar.abhyankarDVR
#check ZInQ.Contrib.Abhyankar.baseline_iff_all_exponents
#check ZInQ.Contrib.Abhyankar.atExponent_one
#check ZInQ.Contrib.Abhyankar.pureKummer_at_every_prime
#check ZInQ.Contrib.Abhyankar.trivialExtension_at_every_prime
#check ZInQ.Contrib.Abhyankar.exponent_dvd_at_every_prime
#check ZInQ.Contrib.Abhyankar.integralClosure_eq_tameRootModel
#check ZInQ.Contrib.Abhyankar.tameRootModel_at_every_prime
#check ZInQ.Contrib.Abhyankar.normalizationPrimeFamilyEquiv

#print axioms ZInQ.Contrib.Abhyankar.abhyankarDVR
#print axioms ZInQ.Contrib.Abhyankar.atExponent_one
#print axioms ZInQ.Contrib.Abhyankar.pureKummer_at_every_prime
#print axioms ZInQ.Contrib.Abhyankar.trivialExtension_at_every_prime
#print axioms ZInQ.Contrib.Abhyankar.exponent_dvd_at_every_prime
#print axioms ZInQ.Contrib.Abhyankar.isFractionRing_adjoin_of_adjoin_eq_top
#print axioms ZInQ.Contrib.Abhyankar.integralClosure_local_dvr
#print axioms ZInQ.Contrib.Abhyankar.uniformizer_factorization_at_prime
#print axioms ZInQ.Contrib.Abhyankar.exists_tameModel_data
#print axioms ZInQ.Contrib.Abhyankar.integralClosure_eq_tameRootModel
#print axioms ZInQ.Contrib.Abhyankar.tameRootModel_at_every_prime
#print axioms ZInQ.Contrib.Abhyankar.ClosureTower.equivBase
#print axioms ZInQ.Contrib.Abhyankar.localization_field_scalarTower
#print axioms ZInQ.Contrib.Abhyankar.localization_isFractionRing
#print axioms ZInQ.Contrib.Abhyankar.normalizationPrimeFamilyEquiv
#print axioms ZInQ.Contrib.Abhyankar.normalization_ramificationIdx
#print axioms ZInQ.Contrib.Abhyankar.normalization_residueSeparable_iff
#print axioms ZInQ.Contrib.Abhyankar.normalized_at_prime
#print axioms ZInQ.Contrib.Abhyankar.algebraMap_bijective_of_dvr
