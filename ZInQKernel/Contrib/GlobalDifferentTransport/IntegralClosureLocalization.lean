/-
# Integral closure under simultaneous base localization

The localized integral-closure property is proved by clearing a base denominator,
not taken as a new premise. The ambient fraction fields and all comparison maps
are explicit and unchanged by localization.
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The actual localized integral closure

This supplies the integral-closure hypothesis needed by different localization.
Both rings must be localized at the same base submonoid (and its image).
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped nonZeroDivisors

namespace GlobalDifferentTransport

variable {R Rₘ S Sₘ K L : Type*}
  [CommRing R] [CommRing Rₘ] [CommRing S] [IsDomain S] [CommRing Sₘ]
  [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L]
  [Algebra R L] [Algebra S L] [IsFractionRing S L] [Algebra R S]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [Algebra R Rₘ] [Algebra Rₘ L] [IsScalarTower R Rₘ L]
  [Algebra S Sₘ] [Algebra Sₘ L] [IsScalarTower S Sₘ L]
  [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Sₘ L]
  {M : Submonoid R} [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

include S K in
/-- Simultaneously localizing the base and its integral closure gives the actual integral closure
in the same ambient fraction field. Local integral closure is derived, not assumed. -/
theorem isIntegralClosure_baseLocalization (hM : M ≤ R⁰) : IsIntegralClosure Sₘ Rₘ L := by
  have hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _
      (algebraMap_injective_of_field_isFractionRing R S K L) hM
  let : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors Sₘ hMS
  let : IsFractionRing Sₘ L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid S M) Sₘ L
  refine ⟨IsFractionRing.injective Sₘ L, fun {x} ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M x hx
    obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := S)).mp ha
    let am : Algebra.algebraMapSubmonoid S M := ⟨algebraMap R S a, ⟨a, a.2, rfl⟩⟩
    refine ⟨IsLocalization.mk' Sₘ s am, ?_⟩
    have hau : IsUnit (algebraMap R L a) := by
      simpa only [← IsScalarTower.algebraMap_apply R Rₘ L] using
        (IsLocalization.map_units Rₘ a).map (algebraMap Rₘ L)
    apply mul_right_cancel₀ hau.ne_zero
    calc
      algebraMap Sₘ L (IsLocalization.mk' Sₘ s am) * algebraMap R L a =
          algebraMap S L s := by
        simpa only [am, map_mul, ← IsScalarTower.algebraMap_apply S Sₘ L,
          ← IsScalarTower.algebraMap_apply R S L] using
          congrArg (algebraMap Sₘ L) (IsLocalization.mk'_spec Sₘ s am)
      _ = x * algebraMap R L a := by
        rw [hs]
        simp only [Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨s, _, m, hm, rfl⟩, hsm⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid S M) y
    have hsmL : algebraMap Sₘ L y * algebraMap R L m = algebraMap S L s := by
      simpa only [map_mul, IsScalarTower.algebraMap_apply R S Sₘ,
        IsScalarTower.algebraMap_apply R Sₘ L,
        IsScalarTower.algebraMap_apply S Sₘ L] using congrArg (algebraMap Sₘ L) hsm
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units Rₘ ⟨m, hm⟩)
    have hmc : algebraMap R L m * algebraMap Rₘ L c = 1 := by
      simpa only [map_mul, map_one, ← IsScalarTower.algebraMap_apply R Rₘ L] using
        congrArg (algebraMap Rₘ L) hc
    have hy : algebraMap Sₘ L y = algebraMap Rₘ L c * algebraMap S L s := by
      calc
        algebraMap Sₘ L y = algebraMap Sₘ L y * 1 := (mul_one _).symm
        _ = algebraMap Sₘ L y * (algebraMap R L m * algebraMap Rₘ L c) := by rw [hmc]
        _ = (algebraMap Sₘ L y * algebraMap R L m) * algebraMap Rₘ L c :=
          (mul_assoc _ _ _).symm
        _ = algebraMap S L s * algebraMap Rₘ L c := by rw [hsmL]
        _ = algebraMap Rₘ L c * algebraMap S L s := mul_comm _ _
    have hs : IsIntegral R (algebraMap S L s) :=
      (IsIntegralClosure.isIntegral_iff (A := S)).mpr ⟨s, rfl⟩
    rw [hy]
    exact (isIntegral_algebraMap (R := Rₘ) (A := L)).mul hs.tower_top

end GlobalDifferentTransport
