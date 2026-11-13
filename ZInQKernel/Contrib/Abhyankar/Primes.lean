import ZInQKernel.Contrib.Abhyankar.Field
import ZInQKernel.Contrib.Abhyankar.Local
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# All-prime field/DVR bridges for the exact T2 hypotheses

The target only assumes finiteness and separability of `L/K`. The root and
field-generation equations supply these properties for `M/K`. Each prime of
the actual integral closure above the maximal ideal is then nonzero, maximal,
and has a DVR localization. In particular, the lower-divisibility theorem at
the end covers every such prime, without a chosen-place or completeness
assumption. The reverse divisibility and residue separability in the general
tame compositum are not asserted here.
-/

namespace ZInQ.Contrib.Abhyankar

open IsLocalRing

/-- The actual baseline root and generation hypotheses make `M/K` finite. -/
theorem finiteDimensional_M
    {R K L M : Type*} [CommRing R] [Field K] [Field L] [Field M]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    {π : R} {n : ℕ} (hn : 0 < n) {t : M}
    (ht : t ^ n = algebraMap R M π)
    (hadjoin : IntermediateField.adjoin L {t} = ⊤) : FiniteDimensional K M := by
  have : IsScalarTower R L M := scalarTower_right (K := K)
  have : FiniteDimensional L M := finiteDimensional_of_root_adjoin hn ht hadjoin
  exact FiniteDimensional.trans K L M

/-- The actual unit exponent and nonzero uniformizer make `M/K` separable. -/
theorem isSeparable_M
    {R K L M : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    {π : R} (hπ : π ≠ 0) {n : ℕ} (hn : IsUnit (n : R)) {t : M}
    (ht : t ^ n = algebraMap R M π)
    (hadjoin : IntermediateField.adjoin L {t} = ⊤) : Algebra.IsSeparable K M := by
  have : IsScalarTower R L M := scalarTower_right (K := K)
  have hπL : algebraMap R L π ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap_injective_of_fractionTower (K := K) (M := L)).ne hπ
  have : Algebra.IsSeparable L M := isSeparable_of_root_adjoin hπL hn ht hadjoin
  exact Algebra.IsSeparable.trans K L M

/-- Every prime of an integral closure above a maximal ideal is maximal.
This does not replace the integral closure by a chosen local factor. -/
theorem integralClosure_prime_isMaximal
    {R E : Type*} [CommRing R] [IsLocalRing R] [CommRing E] [Algebra R E]
    (Q : Ideal (integralClosure R E)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    Q.IsMaximal := by
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q
  rw [← Q.over_def (maximalIdeal R)]
  infer_instance

/-- Each actual integral-closure prime above the closed point has a DVR localization. -/
theorem integralClosure_local_dvr
    (R K E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (Q : Ideal (integralClosure R E)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    IsDiscreteValuationRing (Localization.AtPrime Q) := by
  have : IsDedekindDomain (integralClosure R E) := integralClosure.isDedekindDomain R K E
  have : FaithfulSMul R (integralClosure R E) :=
    FaithfulSMul.of_field_isFractionRing R (integralClosure R E) K E
  have hQ : Q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) Q
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (integralClosure R E) hQ _

/-- The specified base-ring map remains injective in every integral-closure localization. -/
theorem integralClosure_local_algebraMap_injective
    (R K E : Type*) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    (Q : Ideal (integralClosure R E)) [Q.IsPrime] :
    Function.Injective (algebraMap R (Localization.AtPrime Q)) := by
  have hR : Function.Injective (algebraMap R (integralClosure R E)) :=
    algebraMap_injective_of_field_isFractionRing R (integralClosure R E) K E
  rw [IsScalarTower.algebraMap_eq R (integralClosure R E) (Localization.AtPrime Q)]
  exact (IsLocalization.injective (Localization.AtPrime Q)
    Q.primeCompl_le_nonZeroDivisors).comp hR

/-- **All-prime lower divisibility under the baseline hypotheses.**
No tameness or residue perfection is assumed to obtain this necessary part of T2. -/
theorem exponent_dvd_at_every_prime
    {R K L M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) (hu : IsUnit (n : R)) {t : M}
    (ht : t ^ n = algebraMap R M π)
    (hadjoin : IntermediateField.adjoin L {t} = ⊤)
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] :
    n ∣ Q.ramificationIdx R := by
  have : FiniteDimensional K M := finiteDimensional_M hn ht hadjoin
  have : Algebra.IsSeparable K M := isSeparable_M (K := K) hπ.ne_zero hu ht hadjoin
  have : IsDiscreteValuationRing (Localization.AtPrime Q) := integralClosure_local_dvr R K M Q
  let s : integralClosure R M := ⟨t, isIntegral_root hn ht⟩
  have hs : s ^ n = algebraMap R (integralClosure R M) π := Subtype.ext ht
  have hπq : algebraMap R (Localization.AtPrime Q) π ≠ 0 := by
    simpa only [map_zero] using
      (integralClosure_local_algebraMap_injective R K M Q).ne hπ.ne_zero
  exact exponent_dvd_ramificationIdx hπ Q hπq hn hs

end ZInQ.Contrib.Abhyankar
