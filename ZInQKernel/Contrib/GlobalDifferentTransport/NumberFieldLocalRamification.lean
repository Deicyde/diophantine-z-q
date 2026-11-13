/-
# Ramification index of the actual number-field prime localizations

The canonical algebraOfLiesOver square identifies the image of the base maximal
ideal with localization of the genuine globally mapped base prime. Multiplicity
preservation then proves equality of the actual ramification indices. No local
finiteness or comparison identity is assumed.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberFieldPrimeLocalizationDifferent

/-!
# Concrete local/global ramification at number-field primes

This does not assert that a single-prime localization is finite over the base
when primes split. The length-defined ramification index and its genuine ideal
multiplicity comparison are valid without that false finiteness assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace GlobalDifferentTransport.NumberFieldLocalization

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (q : Ideal (𝓞 K)) [q.IsPrime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver q]

/-- The actual canonical local-prime algebra is injective through the original global embedding. -/
theorem atPrime_algebraMap_injective :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    Function.Injective (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  have hf : q.primeCompl ≤ P.primeCompl.comap (algebraMap (𝓞 K) (𝓞 L)) := by
    intro a ha h
    exact ha ((Ideal.mem_of_liesOver P q a).mpr h)
  change Function.Injective (IsLocalization.map (Localization.AtPrime P)
    (algebraMap (𝓞 K) (𝓞 L)) hf : Localization.AtPrime q →+* Localization.AtPrime P)
  exact IsLocalization.map_injective_of_injective' (S := 𝓞 L) q.primeCompl
    (Localization.AtPrime P) hf (by simp)
    (NumberField.RingOfIntegers.algebraMap.injective K L)

/-- The target local maximal ideal lies over the actual base local maximal ideal under the
canonical localization algebra map. -/
theorem atPrime_maximalIdeal_liesOver :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  have h := IsLocalization.liesOver_of_isPrime_of_disjoint
    (R' := Localization.AtPrime q) (S' := Localization.AtPrime P)
    q.primeCompl P.primeCompl q (P := P)
      (by exact Set.disjoint_left.mpr (fun x hx hxP ↦ hx hxP))
  simpa only [Localization.AtPrime.map_eq_maximalIdeal] using h

/-- The actual local image of the base maximal ideal is the localization of the genuinely
mapped global prime. This proves the identity of the ideal whose coefficient is used below. -/
theorem atPrime_map_maximalIdeal_eq :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) =
      (q.map (algebraMap (𝓞 K) (𝓞 L))).map (algebraMap (𝓞 L) (Localization.AtPrime P)) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  have hcomp : (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)).comp
      (algebraMap (𝓞 K) (Localization.AtPrime q)) =
      (algebraMap (𝓞 L) (Localization.AtPrime P)).comp (algebraMap (𝓞 K) (𝓞 L)) :=
    (IsScalarTower.algebraMap_eq (𝓞 K) (Localization.AtPrime q) (Localization.AtPrime P)).symm.trans
      (IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 L) (Localization.AtPrime P))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, hcomp]

/-- The ramification index of the actual local DVR extension is its genuine global index.
There is no unique-prime or finite-local-module premise in this comparison. -/
theorem ramificationIdx_atPrime_eq (hP : P ≠ ⊥) :
    let _ := Localization.AtPrime.algebraOfLiesOver q P
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).ramificationIdx
        (Localization.AtPrime q) = P.ramificationIdx (𝓞 K) := by
  let _ := Localization.AtPrime.algebraOfLiesOver q P
  dsimp only
  have hq : q ≠ ⊥ := by
    intro h
    exact hP (Ideal.eq_bot_of_under_eq_bot ((Ideal.over_def P q).symm.trans h))
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hq _
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP _
  let : FaithfulSMul (Localization.AtPrime q) (Localization.AtPrime P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (atPrime_algebraMap_injective K L q P)
  let := atPrime_maximalIdeal_liesOver K L q P
  have hglobal : q.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hq
  have hlocal : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field (Localization.AtPrime q))
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) hlocal,
    atPrime_map_maximalIdeal_eq K L q P,
    multiplicity_map_numberField_atPrime_eq L P hP _ hglobal]
  exact (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity q P hglobal).symm

end GlobalDifferentTransport.NumberFieldLocalization
