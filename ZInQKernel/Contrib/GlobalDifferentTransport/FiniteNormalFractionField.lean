/-
# Fraction-field structure of an actual finite normal ring extension

Finiteness is transported using the existing denominator-clearing theorem for
algebraic elements and Module.Finite.of_isLocalization. Integral closure is
proved from normality of the upper ring and integrality of the finite extension.
These are structural suppliers, not arithmetic bounds or desired different facts.
-/
module

public import Mathlib.Algebra.CharZero.AddMonoidHom
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Finite, separable fraction-field extension and actual integral closure

This closes the fraction-field and integral-closure structure required to apply
DVR arithmetic to a genuinely finite localized fixed-field tower. It does not
assert finiteness of a single localization when primes split over its base.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped nonZeroDivisors

namespace GlobalDifferentTransport

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- The fraction field of the upper ring localizes at the image of the actual base nonzero
submonoid. Cofinality of these denominators is proved from algebraicity, not assumed. -/
theorem fractionField_isLocalization_baseNonzero :
    IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) := by
  let T := Algebra.algebraMapSubmonoid S R⁰
  have hT : T ≤ S⁰ := map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective R S) le_rfl
  apply (IsLocalization.iff_of_le_of_exists_dvd (M := T) (S := FractionRing S) S⁰ hT ?_).mpr
  · infer_instance
  · intro b hb
    obtain ⟨c, d, hd, hdc⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R (1 : S)
      (nonZeroDivisors.ne_zero hb)
    refine ⟨algebraMap R S d, ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩, c, ?_⟩
    simpa only [Algebra.smul_def, mul_one] using hdc

/-- A genuinely finite faithful extension of domains induces a finite extension of the actual
canonical fraction fields. No local completeness or degree formula is a premise. -/
theorem finite_fractionField_extension : Module.Finite (FractionRing R) (FractionRing S) := by
  let := fractionField_isLocalization_baseNonzero R S
  exact Module.Finite.of_isLocalization R S R⁰

/-- A finite extension of domains with normal upper ring has that actual ring as the integral
closure of the base in its own canonical fraction field. -/
theorem isIntegralClosure_finite_normal_fractionField [IsIntegrallyClosed S] :
    IsIntegralClosure S R (FractionRing S) := by
  refine ⟨IsFractionRing.injective S (FractionRing S), fun {x} ↦ ?_⟩
  constructor
  · intro hx
    exact IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top
  · rintro ⟨s, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := R) s).algebraMap

/-- In characteristic zero the induced actual finite fraction-field extension is separable. -/
theorem isSeparable_fractionField_extension [CharZero R] :
    Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
  let := finite_fractionField_extension R S
  let : CharZero (FractionRing R) := CharZero.of_addMonoidHom
    (algebraMap R (FractionRing R)).toAddMonoidHom
    (algebraMap R (FractionRing R)).map_one (IsFractionRing.injective R _)
  infer_instance

end GlobalDifferentTransport
