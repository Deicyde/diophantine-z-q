/-
# Actual number-field different at a uniquely lying-over prime

The canonical fraction-field and algebra squares are constructed in the proof.
The only additional intermediary condition is genuine uniqueness of the prime
above the base prime. No desired different comparison is an assumption.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberFieldLocalizationDifferent
public import ZInQKernel.Contrib.GlobalDifferentTransport.UniqueLocalization

/-!
# Concrete single-prime number-field different localization

The general comparison permits an explicit unique-prime condition. The actual
decomposition fixed-field application proves that condition separately; it is
not silently assumed for split primes or arbitrary global extensions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace GlobalDifferentTransport.NumberFieldLocalization

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (q : Ideal (𝓞 K)) [q.IsPrime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver q]

/-- The original global field square induces the canonical square of localized rings and
unchanged fraction fields. The ring map is `algebraOfLiesOver`, not a supplied comparison. -/
theorem atPrime_fractionField_square :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    (localizationToFractionField (𝓞 L) L P.primeCompl P.primeCompl_le_nonZeroDivisors).comp
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) =
      (algebraMap K L).comp
        (localizationToFractionField (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  apply IsLocalization.ringHom_ext q.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  have hlocal : algebraMap (Localization.AtPrime q) (Localization.AtPrime P)
      (algebraMap (𝓞 K) (Localization.AtPrime q) a) =
      algebraMap (𝓞 L) (Localization.AtPrime P) (algebraMap (𝓞 K) (𝓞 L) a) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L)]
  rw [hlocal, localizationToFractionField_algebraMap, localizationToFractionField_algebraMap,
    ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
    ← IsScalarTower.algebraMap_apply (𝓞 K) K L]

/-- The genuine global different maps to the actual single-prime localized relative different
when the selected prime is the only prime above the base prime. Every fraction-field and
scalar-tower structure is the canonical one, and localized integral closure is derived. -/
theorem map_differentIdeal_atPrime_eq (hUnique : Ideal.primesOver q (𝓞 L) = {P}) :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (Localization.AtPrime P)) =
      differentIdeal (Localization.AtPrime q) (Localization.AtPrime P) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  let : Algebra (Localization.AtPrime q) K :=
    localizationFractionFieldAlgebra (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 K) (Localization.AtPrime q) K :=
    localizationFractionFieldIsScalarTower (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsFractionRing (Localization.AtPrime q) K :=
    isFractionRing_localization_actualField (𝓞 K) K q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime P) L :=
    localizationFractionFieldAlgebra (𝓞 L) L P.primeCompl P.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 L) (Localization.AtPrime P) L :=
    localizationFractionFieldIsScalarTower (𝓞 L) L P.primeCompl P.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime q) L :=
    localizationBaseToExtensionFieldAlgebra (𝓞 K) K L q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (Localization.AtPrime q) K L :=
    localizationBaseFieldIsScalarTower (𝓞 K) K L q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (𝓞 K) (Localization.AtPrime q) L :=
    localizationBaseToExtensionFieldIsScalarTower (𝓞 K) K L q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower (Localization.AtPrime q) (Localization.AtPrime P) L :=
    IsScalarTower.of_algebraMap_eq' (atPrime_fractionField_square K L q P).symm
  let : IsScalarTower (𝓞 K) (Localization.AtPrime P) L :=
    IsScalarTower.to₁₃₄ (𝓞 K) (𝓞 L) (Localization.AtPrime P) L
  let : FaithfulSMul (Localization.AtPrime q) (Localization.AtPrime P) :=
    FaithfulSMul.of_field_isFractionRing (Localization.AtPrime q) (Localization.AtPrime P) K L
  let : Module.IsTorsionFree (Localization.AtPrime q) (Localization.AtPrime P) := inferInstance
  let : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.right ℤ (𝓞 K) (𝓞 L)
  let : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl)
      (Localization.AtPrime P) := isLocalization_base_primeCompl_atPrime q P hUnique
  exact map_differentIdeal_baseLocalization (R := 𝓞 K) (Rₘ := Localization.AtPrime q)
    (S := 𝓞 L) (Sₘ := Localization.AtPrime P) (K := K) (L := L) (M := q.primeCompl)
    q.primeCompl_le_nonZeroDivisors

end GlobalDifferentTransport.NumberFieldLocalization

namespace GlobalDifferentTransport

section Coefficients

variable (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)

include hP in
/-- Localization preserves every prime-power divisibility test of every ideal, including the
zero ideal and the zero exponent. This statement requires no uniqueness above a base prime. -/
theorem pow_dvd_map_numberField_atPrime_iff (I : Ideal (𝓞 L)) (n : ℕ) :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n ∣
        I.map (algebraMap (𝓞 L) (Localization.AtPrime P)) ↔ P ^ n ∣ I := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap,
    ← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal_pow P (Localization.AtPrime P)]

include hP in
/-- The coefficient of a nonzero global ideal is preserved by localization at its actual prime. -/
theorem multiplicity_map_numberField_atPrime_eq (I : Ideal (𝓞 L)) (hI : I ≠ ⊥) :
    multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (I.map (algebraMap (𝓞 L) (Localization.AtPrime P))) = multiplicity P I := by
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP _
  have hlocal := FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field (Localization.AtPrime P))
      inferInstance) (Ideal.map_ne_bot_of_ne_bot hI)
  have hglobal := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP inferInstance) hI
  have hn (n : ℕ) :
      n ≤ multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (I.map (algebraMap (𝓞 L) (Localization.AtPrime P))) ↔ n ≤ multiplicity P I :=
    hlocal.pow_dvd_iff_le_multiplicity.symm.trans
      ((pow_dvd_map_numberField_atPrime_iff L P hP I n).trans hglobal.pow_dvd_iff_le_multiplicity)
  exact le_antisymm ((hn _).mp le_rfl) ((hn _).mpr le_rfl)

end Coefficients

namespace NumberFieldLocalization

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (q : Ideal (𝓞 K)) [q.IsPrime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver q]

/-- The concrete coefficient-localization theorem for the actual number-field different.
Uniqueness is an explicit structural intermediary premise, not a different equality premise. -/
theorem multiplicity_differentIdeal_atPrime_eq (hP : P ≠ ⊥)
    (hUnique : Ideal.primesOver q (𝓞 L) = {P}) :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (differentIdeal (Localization.AtPrime q) (Localization.AtPrime P)) =
      multiplicity P (differentIdeal (𝓞 K) (𝓞 L)) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  rw [← map_differentIdeal_atPrime_eq K L q P hUnique]
  exact multiplicity_map_numberField_atPrime_eq L P hP _ differentIdeal_ne_bot

/-- Every exponent of the concrete local different is tested against the genuine global prime,
with the actual different equality proved rather than supplied as an input. -/
theorem pow_dvd_differentIdeal_atPrime_iff (hP : P ≠ ⊥)
    (hUnique : Ideal.primesOver q (𝓞 L) = {P}) (n : ℕ) :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n ∣
        differentIdeal (Localization.AtPrime q) (Localization.AtPrime P) ↔
      P ^ n ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  rw [← map_differentIdeal_atPrime_eq K L q P hUnique]
  exact pow_dvd_map_numberField_atPrime_iff L P hP _ n

end NumberFieldLocalization

end GlobalDifferentTransport
