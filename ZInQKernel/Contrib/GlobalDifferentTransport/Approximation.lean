/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Selected approximation proofs adapted to Mathlib v4.35.0 from TauCeti,
revision a6027b1d24fcb935c53bd5b50d11b40991cda418,
TauCeti/RingTheory/DedekindDomain/AdicValuation/Completion.lean,
lines 336–363 and 411–443. No Henselian or local-field wrapper is imported.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Completion

/-!
# Surjectivity modulo every completed prime power

The canonical map `R → v.adicCompletionIntegers K` is surjective modulo every
power of the maximal ideal. Together with exact contraction of powers, this
supplies the ring-map side of the comparison of ideal-power inertia groups.
The decomposition-group equivalence is a separate field-theoretic step.
-/

public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain WithZero Topology

namespace GlobalDifferentTransport

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The completed integer ring inherits its topological ring structure from the valued field. -/
instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/-- Every nonzero closed valuation ball around the origin of the adic completion is open. -/
theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {z : v.adicCompletion K | Valued.v z ≤ γ} := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K γ
  have hr0 : Valued.v.restrict z ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hz]
    exact hγ
  have h : {y : v.adicCompletion K | Valued.v y ≤ γ} =
      {y : v.adicCompletion K | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hz]
  rw [h]
  exact Valued.isOpen_closedBall _ hr0

/-- Each maximal-ideal power is open in the subspace topology of the completed integer ring. -/
theorem isOpen_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    IsOpen ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
  have h : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
      (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
        {y : v.adicCompletion K | Valued.v y ≤ exp (-(n : ℤ))} :=
    Set.ext fun x ↦ mem_maximalIdeal_pow_iff (K := K) v
  rw [h]
  exact (isOpen_setOf_valued_le (K := K) v exp_ne_zero).preimage continuous_subtype_val

/-- Every completed integer can be approximated by an element of the affine model modulo
any prescribed power. The approximation includes exponent zero. -/
theorem exists_valued_sub_le (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) -
      algebraMap R (v.adicCompletion K) a) ≤ exp (-(n : ℤ)) := by
  let U : Set (v.adicCompletionIntegers K) := (· - x) ⁻¹'
    ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
  have hU : IsOpen (((↑) : v.adicCompletionIntegers K → v.adicCompletion K) '' U) :=
    (Valued.isOpen_valuationSubring _).isOpenMap_subtype_val _
      ((isOpen_maximalIdeal_pow_adicCompletionIntegers v n).preimage
        (continuous_sub_right x))
  obtain ⟨z, y, hy, hyz⟩ := (v.denseRange_algebraMap (K := K)).exists_mem_open hU
    ⟨x, x, by simp [U], rfl⟩
  have hz : v.valuation K z ≤ 1 := by
    have hy1 : Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 :=
      hyz ▸ (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp y.2
    rwa [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hy1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz
    (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨a, ?_⟩
  have hxy : Valued.v ((x : v.adicCompletion K) - y) ≤ exp (-(n : ℤ)) := by
    have hy' := (mem_maximalIdeal_pow_iff (K := K) v).mp hy
    rwa [AddSubgroupClass.coe_sub, Valuation.map_sub_swap] at hy'
  have hza : Valued.v ((y : v.adicCompletion K) -
      algebraMap R (v.adicCompletion K) a) ≤ exp (-(n : ℤ)) := by
    rw [hyz, IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, Valuation.map_sub_swap]
    exact ha.le
  rw [← sub_add_sub_cancel _ (y : v.adicCompletion K)]
  exact Valuation.map_add_le _ hxy hza

/-- The canonical affine-model map is surjective modulo every completed maximal-ideal power. -/
theorem exists_sub_mem_maximalIdeal_pow (n : ℕ) (x : v.adicCompletionIntegers K) :
    ∃ a : R, x - algebraMap R (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  obtain ⟨a, ha⟩ := exists_valued_sub_le v x n
  refine ⟨a, ?_⟩
  rw [mem_maximalIdeal_pow_iff v]
  exact ha

end GlobalDifferentTransport
