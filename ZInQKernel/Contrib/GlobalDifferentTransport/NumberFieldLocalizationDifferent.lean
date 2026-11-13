/-
# The actual number-field different under canonical base localization

This instantiates the proved trace-dual/different localization theorem on the
actual rings of integers, the original number fields, and their canonical
IsLocalization.lift maps. No desired different-image equality or local integral
closure is taken as an input.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.CanonicalLocalization
public import ZInQKernel.Contrib.GlobalDifferentTransport.LocalizationDifferent
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Concrete number-field localization of the different

For `L/K` an extension of number fields and `q` a prime of `𝓞 K`, set
`A = (𝓞 K)_q` and `B = (q.primeCompl)⁻¹(𝓞 L)`, where the extension ring is
localized at the image of the **same base submonoid**. All algebra and
fraction-field squares are constructed canonically. Uniqueness of primes is
not needed for this simultaneous, possibly semilocal statement.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace GlobalDifferentTransport.NumberFieldLocalization

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (q : Ideal (𝓞 K)) [q.IsPrime]

/-- The actual localization of the base number-field integers at the chosen prime. -/
abbrev baseRing := Localization.AtPrime q

/-- The image of the very same base prime complement in the actual extension integer ring. -/
abbrev extensionDenominators := Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl

/-- The simultaneous base localization of the actual extension integer ring. -/
abbrev extensionRing := Localization (extensionDenominators K L q)

omit [NumberField L] in
/-- The inverted extension denominators are nonzero divisors, by the genuine global field square. -/
theorem extensionDenominators_le : extensionDenominators K L q ≤ (𝓞 L)⁰ :=
  imageDenominators_le_nonZeroDivisors (𝓞 K) (𝓞 L) K L q.primeCompl
    q.primeCompl_le_nonZeroDivisors

omit [NumberField L] in
/-- The simultaneously localized extension is a domain; no single-prime or Galois assumption
is needed. Kept in a contribution scope to avoid new ambient instance choices. -/
theorem extensionRing_isDomain : IsDomain (extensionRing K L q) :=
  IsLocalization.isDomain_localization (extensionDenominators_le K L q)

scoped[GlobalDifferentTransportNumberFieldLocalization] attribute [instance]
  GlobalDifferentTransport.NumberFieldLocalization.extensionRing_isDomain

open scoped GlobalDifferentTransportNumberFieldLocalization

/-- Simultaneous localization preserves the genuine Dedekind-domain structure of `𝓞 L`. -/
theorem extensionRing_isDedekindDomain : IsDedekindDomain (extensionRing K L q) :=
  IsLocalization.isDedekindDomain (𝓞 L) (extensionDenominators_le K L q) _

omit [NumberField K] [NumberField L] in
/-- The actual localized base algebra acts faithfully through the canonical localized ring map. -/
theorem extensionRing_faithfulSMul :
    FaithfulSMul (baseRing K q) (extensionRing K L q) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact localizationAlgebra_injective
    (M := q.primeCompl) (Rₘ := baseRing K q) (Sₘ := extensionRing K L q)
    (NumberField.RingOfIntegers.algebraMap.injective K L)

scoped[GlobalDifferentTransportNumberFieldLocalization] attribute [instance]
  GlobalDifferentTransport.NumberFieldLocalization.extensionRing_isDedekindDomain
  GlobalDifferentTransport.NumberFieldLocalization.extensionRing_faithfulSMul

/-- Torsion-freeness of the actual simultaneous localized algebra follows from injectivity. -/
theorem extensionRing_isTorsionFree :
    Module.IsTorsionFree (baseRing K q) (extensionRing K L q) := by
  let _ := extensionRing_faithfulSMul K L q
  infer_instance

omit [NumberField K] in
/-- Genuine finiteness of the simultaneous localized extension, not finiteness of a chosen
single-prime localization in the split case. -/
theorem extensionRing_moduleFinite : Module.Finite (baseRing K q) (extensionRing K L q) := by
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.right ℤ (𝓞 K) (𝓞 L)
  exact Module.Finite.of_isLocalization (𝓞 K) (𝓞 L) q.primeCompl

scoped[GlobalDifferentTransportNumberFieldLocalization] attribute [instance]
  GlobalDifferentTransport.NumberFieldLocalization.extensionRing_isTorsionFree
  GlobalDifferentTransport.NumberFieldLocalization.extensionRing_moduleFinite

/-- The genuine global different equals the actual localized relative different along the
canonical simultaneous base-localization map. The localized integral closure and all
fraction-field comparison structures are derived in the proof. -/
theorem map_differentIdeal_eq :
    (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (extensionRing K L q)) =
      differentIdeal (baseRing K q) (extensionRing K L q) := by
  let : Algebra (baseRing K q) K :=
    localizationFractionFieldAlgebra (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 K) (baseRing K q) K :=
    localizationFractionFieldIsScalarTower (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsFractionRing (baseRing K q) K :=
    isFractionRing_localization_actualField (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : Algebra (extensionRing K L q) L :=
    localizationFractionFieldAlgebra (𝓞 L) L (extensionDenominators K L q)
      (extensionDenominators_le K L q)
  let : IsScalarTower (𝓞 L) (extensionRing K L q) L :=
    localizationFractionFieldIsScalarTower (𝓞 L) L (extensionDenominators K L q)
      (extensionDenominators_le K L q)
  let : Algebra (baseRing K q) L :=
    localizationBaseToExtensionFieldAlgebra (𝓞 K) K L q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (baseRing K q) K L :=
    localizationBaseFieldIsScalarTower (𝓞 K) K L q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 K) (baseRing K q) L :=
    localizationBaseToExtensionFieldIsScalarTower (𝓞 K) K L q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (baseRing K q) (extensionRing K L q) L :=
    localizationExtensionFieldIsScalarTower (𝓞 K) (𝓞 L) K L q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 K) (extensionRing K L q) L :=
    IsScalarTower.to₁₃₄ (𝓞 K) (𝓞 L) (extensionRing K L q) L
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.right ℤ (𝓞 K) (𝓞 L)
  exact map_differentIdeal_baseLocalization (R := 𝓞 K) (Rₘ := baseRing K q)
    (S := 𝓞 L) (Sₘ := extensionRing K L q) (K := K) (L := L) (M := q.primeCompl)
    q.primeCompl_le_nonZeroDivisors

end GlobalDifferentTransport.NumberFieldLocalization
