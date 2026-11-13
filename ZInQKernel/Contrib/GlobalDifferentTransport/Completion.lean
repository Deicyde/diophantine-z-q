/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Selected single-completion proofs adapted to Mathlib v4.35.0 from TauCeti,
revision a6027b1d24fcb935c53bd5b50d11b40991cda418,
TauCeti/RingTheory/DedekindDomain/AdicValuation/Completion.lean.
New all-power ideal-map consequences are proved below.
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Single-completion ideal transport

For a Dedekind domain `R`, its fraction field `K`, and a height-one prime `v`,
the prime generates the maximal ideal of the concrete ring
`v.adicCompletionIntegers K`. Extension to that ring preserves and reflects
**every** prime-power divisibility condition on **every** ideal of `R`.

No statement here identifies the extension of a global different with the
different of an extension of completed rings. That is a separate trace-pairing
comparison, not a premise hidden in this module.
-/

public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain WithZero

namespace GlobalDifferentTransport

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The adic completion has the normalized uniformizer value `exp (-1)`. -/
theorem isUniformizer_adicCompletion_iff {x : v.adicCompletion K} :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer x ↔
      Valued.v x = exp (-1) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)]
  rfl

/-- The maximal ideal of the completed integer ring contracts to the chosen prime. -/
theorem under_maximalIdeal_adicCompletionIntegers :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).under R = v.asIdeal := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, ← v.valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).trans ?_
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Elements outside the selected prime become units in its completed integer ring. -/
theorem isUnit_algebraMap_adicCompletionIntegers_iff (r : R) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) r) ↔ r ∉ v.asIdeal := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← Ideal.mem_under,
    under_maximalIdeal_adicCompletionIntegers v]

/-- An irreducible of the completed integer ring has normalized value `exp (-1)`. -/
theorem valued_algebraMap_eq_exp_neg_one_of_irreducible
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      exp (-1) := by
  have hgen : IsLocalRing.maximalIdeal
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring =
      Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  exact (isUniformizer_adicCompletion_iff v).mp huni

/-- The chosen global prime generates the maximal ideal of the completed integer ring. -/
theorem map_asIdeal_adicCompletionIntegers :
    Ideal.map (algebraMap R (v.adicCompletionIntegers K)) v.asIdeal =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def,
      under_maximalIdeal_adicCompletionIntegers v]
  · obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.intValuation_lt_one_iff_mem, hπ]
      simp
    have hπval : Valued.v
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) = exp (-1) := by
      rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπuni : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) :=
      (isUniformizer_adicCompletion_iff v).mpr hπval
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
      (v.adicCompletionIntegers K)
    have hϖuni : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (ϖ : v.adicCompletion K) :=
      Valuation.isUniformizer_of_maximalIdeal_eq_span _ hϖ.maximalIdeal_eq
    rw [hϖ.maximalIdeal_eq]
    have hassoc : Associated ϖ (algebraMap R (v.adicCompletionIntegers K) π) :=
      Valuation.associated_of_isUniformizer hϖuni hπuni
    rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_map_of_mem _ hπmem))

/-- The completed maximal-ideal filtration is the normalized valuation filtration. -/
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (v.adicCompletionIntegers K)
  have hint := Valuation.valuationSubring.integers
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))
  have hπn : Valued.v
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ n =
      exp (-(n : ℤ)) := by
    rw [valued_algebraMap_eq_exp_neg_one_of_irreducible v hπ, ← exp_nsmul]
    simp
  rw [← hπn]
  exact Set.ext_iff.mp
    (hint.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n) x

/-- The global prime-power filtration agrees with the valuation on global elements. -/
theorem mem_asIdeal_pow_iff_valued_algebraMap_le {r : R} {n : ℕ} :
    r ∈ v.asIdeal ^ n ↔
      Valued.v (algebraMap R (v.adicCompletion K) r) ≤ exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]

/-- Contraction of every power of the completed maximal ideal is the same global prime power. -/
theorem comap_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n).comap
        (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal ^ n := by
  ext r
  rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff v,
    mem_asIdeal_pow_iff_valued_algebraMap_le (K := K) v]
  rfl

/-- Extension sends every global prime power to the same completed maximal-ideal power. -/
theorem map_asIdeal_pow_adicCompletionIntegers (n : ℕ) :
    (v.asIdeal ^ n).map (algebraMap R (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  rw [Ideal.map_pow, map_asIdeal_adicCompletionIntegers v]

/-- Extension preserves and reflects all prime-power divisibility tests, including the
zero ideal and exponent zero. No finiteness of the completion over `R` is assumed. -/
theorem pow_dvd_map_adicCompletionIntegers_iff (I : Ideal R) (n : ℕ) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ∣
        I.map (algebraMap R (v.adicCompletionIntegers K)) ↔
      v.asIdeal ^ n ∣ I := by
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap,
    comap_maximalIdeal_pow_adicCompletionIntegers v]

end GlobalDifferentTransport
