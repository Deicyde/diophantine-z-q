/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/Different/Serre.lean
Original SHA-256: 4084efa2e7ae38b06021692c5c439a641a7e220fd2f621cb784305e9e11a01cf
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.ResidueLifting
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.Different.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Modified: the distinct valuation-class argument in
TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/LocalField/Eisenstein/PowerBasis.lean, is applied directly
inside the derivative estimate. Generic no-cancellation is invoked from Mathlib.
The valuation scaling and tower arguments retain
TauCeti/NumberTheory/LocalField/RamificationIndex.lean from the same source.
Full license and attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this adaptation when the pinned Mathlib provides the same estimate. -/

noncomputable section
open ValuativeRel IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] Ideal.Quotient.field

namespace TauCeti

section ValuationScaling

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/- The additive valuation on the integer ring scales by the ramification index. -/
@[simp]
theorem addVal_algebraMap (a : 𝒪[K]) :
    IsDiscreteValuationRing.addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] a) =
      ramificationIndex K L • IsDiscreteValuationRing.addVal 𝒪[K] a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hπmap0 : algebraMap 𝒪[K] 𝒪[L] π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L]
    simpa using h
  obtain ⟨q, v, hπmap⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπmap0 hϖ
  have hπK : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hϖL : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hmapUnits : Units.map (algebraMap K L : K →* L) (Units.mk0 (π : K) hπK) =
      Units.map (Subring.subtype 𝒪[L] : 𝒪[L] →* L) v *
        (Units.mk0 (ϖ : L) hϖL) ^ q := by
    apply Units.ext
    simpa using congrArg ((↑·) : 𝒪[L] → L) hπmap
  have hq : q = ramificationIndex K L := by
    have hv : normalizedValuation L
        (Units.map (Subring.subtype 𝒪[L] : 𝒪[L] →* L) v) = 1 := by
      rw [normalizedValuation_eq_one_iff]
      exact (Valuation.integer.integers (valuation L)).one_of_isUnit v.isUnit
    have hval := normalizedValuation_algebraMap_irreducible (L := L) hπ
    rw [hmapUnits, map_mul, map_pow, hv,
      normalizedValuation_irreducible hϖ, one_mul] at hval
    have hval' := congrArg Multiplicative.toAdd hval
    simpa [toAdd_pow, nsmul_eq_mul] using hval'
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ramificationIndex_pos.ne']
  · obtain ⟨n, w, ha⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hwval : IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] (w : 𝒪[K])) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (IsUnit.map _ w.isUnit)
    have hπval : IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] π) = ramificationIndex K L := by
      rw [IsDiscreteValuationRing.addVal_def _ v hϖ q hπmap, hq]
    rw [ha, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, hwval, zero_add, hπval,
      IsDiscreteValuationRing.addVal_def' w hπ n]
    simp [nsmul_eq_mul, mul_comm]

/- Ramification indices multiply in a compatible tower. -/
theorem ramificationIndex_tower (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [ValuativeExtension L M] :
    ramificationIndex K M = ramificationIndex K L * ramificationIndex L M := by
  letI : ValuativeExtension K M := {
    vle_iff_vle := fun a b => by
      simp only [IsScalarTower.algebraMap_apply K L M,
        ValuativeExtension.vle_iff_vle] }
  refine ramificationIndex_eq_iff.2 fun x ↦ ?_
  have hx : Units.map (algebraMap K M : K →* M) x =
      Units.map (algebraMap L M : L →* M) (Units.map (algebraMap K L : K →* L) x) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [hx, normalizedValuation_algebraMap, normalizedValuation_algebraMap, pow_mul]


end ValuationScaling

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [CharZero K]

private theorem derivative_uniformizer_bound (π : 𝒪[L]) (hπ : Irreducible π)
    (f : 𝒪[K][X]) (hf : f.Monic) (hdeg : f.natDegree = ramificationIndex K L) :
    IsDiscreteValuationRing.addVal 𝒪[L] (aeval π f.derivative) ≤
      IsDiscreteValuationRing.addVal 𝒪[L] (ramificationIndex K L : 𝒪[L]) +
        (ramificationIndex K L - 1 : ℕ) := by
  classical
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let e := ramificationIndex K L
  have he : 0 < e := ramificationIndex_pos
  have hdegree : f.natDegree = e := hdeg
  let c : Fin e → 𝒪[K] := fun i => f.derivative.coeff i
  let t : Fin e → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (c i) * π ^ (i : ℕ)
  let v := IsDiscreteValuationRing.addVal 𝒪[L]
  let q : Fin e := ⟨e - 1, by omega⟩
  have hcq : c q = (e : 𝒪[K]) := by
    dsimp [c, q]
    have hq : e - 1 + 1 = e := by omega
    have hcast : ((e - 1 : ℕ) : 𝒪[K]) + 1 = (e : 𝒪[K]) := by exact_mod_cast hq
    rw [coeff_derivative, hq, hcast, ← hdegree, hf.coeff_natDegree, one_mul]
  have htq : v (t q) = v (e : 𝒪[L]) + (e - 1 : ℕ) := by
    simp only [t, hcq, map_natCast, v, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ,
      nsmul_one, q]
  have htq0 : t q ≠ 0 := by
    dsimp [t]
    rw [hcq, map_natCast]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr he.ne') (pow_ne_zero _ hπ.ne_zero)
  have hterm (i : Fin e) :
      v (t i) = e • IsDiscreteValuationRing.addVal 𝒪[K] (c i) + (i : ℕ) := by
    dsimp [v, t]
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      addVal_algebraMap, IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_one]
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hdistinct (i j : Fin e) (hij : i ≠ j) (hi : t i ≠ 0) (hj : t j ≠ 0) :
      v (t i) ≠ v (t j) := by
    intro hval
    have hci : c i ≠ 0 := by intro h; exact hi (by simp [t, h])
    have hcj : c j ≠ 0 := by intro h; exact hj (by simp [t, h])
    obtain ⟨ni, ui, hci'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hci hρ
    obtain ⟨nj, uj, hcj'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcj hρ
    have hvi : IsDiscreteValuationRing.addVal 𝒪[K] (c i) = ni := by
      rw [hci', IsDiscreteValuationRing.addVal_def' ui hρ ni]
    have hvj : IsDiscreteValuationRing.addVal 𝒪[K] (c j) = nj := by
      rw [hcj', IsDiscreteValuationRing.addVal_def' uj hρ nj]
    rw [hterm, hterm, hvi, hvj] at hval
    have hnat : e * ni + (i : ℕ) = e * nj + (j : ℕ) := by
      have hcast : ((e * ni + (i : ℕ) : ℕ) : ℕ∞) = e * nj + (j : ℕ) := by
        simpa [nsmul_eq_mul] using hval
      exact_mod_cast hcast
    have hmod := congrArg (fun n : ℕ => n % e) hnat
    apply hij
    apply Fin.ext
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hmod
  obtain ⟨j, hj, hjmin⟩ := Finset.univ.exists_min_image (fun i => v (t i))
    ⟨q, Finset.mem_univ q⟩
  have htj0 : t j ≠ 0 := by
    intro hzero
    have hle := hjmin q (Finset.mem_univ q)
    rw [hzero, AddValuation.map_zero, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at hle
    exact htq0 hle
  have hstrict : ∀ i ∈ (Finset.univ : Finset (Fin e)) \ {j},
      v.toValuation (t i) < v.toValuation (t j) := by
    intro i hi
    have hij : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton.mpr h)
    have hle := hjmin i (Finset.mem_univ i)
    have hne : v (t j) ≠ v (t i) := by
      by_cases hi0 : t i = 0
      · rw [hi0, AddValuation.map_zero]
        change IsDiscreteValuationRing.addVal 𝒪[L] (t j) ≠ ⊤
        exact fun h => htj0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
      · exact (hdistinct i j hij hi0 htj0).symm
    exact (lt_of_le_of_ne hle hne).dual
  have hsum : v (∑ i, t i) = v (t j) := v.toValuation.map_sum_eq_of_lt hj hstrict
  have hexpand : aeval π f.derivative = ∑ i, t i := by
    rw [aeval_def, eval₂_eq_sum_range' (algebraMap 𝒪[K] 𝒪[L])
      (show f.derivative.natDegree < e by rw [← hdegree]; exact natDegree_derivative_lt (by omega))]
    exact (Fin.sum_univ_eq_sum_range (fun i =>
      algebraMap 𝒪[K] 𝒪[L] (f.derivative.coeff i) * π ^ i) e).symm
  rw [hexpand, hsum]
  exact (hjmin q (Finset.mem_univ q)).trans_eq htq

/-- A derivative in the different rules out every larger power of the maximal ideal. -/
private theorem not_pow_dvd_different_of_residue_bijective [Module.Finite K L]
    [Algebra.IsSeparable K L]
    (hres : Function.Bijective (algebraMap 𝓀[K] 𝓀[L])) (N : ℕ)
    (hN : IsDiscreteValuationRing.addVal 𝒪[L] (ramificationIndex K L : 𝒪[L]) +
      (ramificationIndex K L - 1 : ℕ) < (N : ℕ∞)) :
    ¬ 𝓂[L] ^ N ∣ differentIdeal 𝒪[K] 𝒪[L] := by
  classical
  letI : Module.Finite 𝒪[K] 𝒪[L] := integerRingModuleFinite K L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨hgen, hdeg⟩ := uniformizer_presentation K L hres π hπ
  have hint : IsIntegral 𝒪[K] π := Algebra.IsIntegral.isIntegral π
  have hbound := derivative_uniformizer_bound K L π hπ (minpoly 𝒪[K] π)
    (minpoly.monic hint) hdeg
  have hK : Algebra.adjoin K {algebraMap 𝒪[L] L π} = ⊤ := by
    rw [← IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun y _ => IsAlgebraic.of_finite K y)]
    exact TauCeti.IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top hgen
  have hmem := aeval_derivative_mem_differentIdeal 𝒪[K] K L π hK
  intro hdvd
  have hpower := Ideal.dvd_iff_le.mp hdvd hmem
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hpower
  have hval := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hpower
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ,
    nsmul_one] at hval
  exact (not_le_of_gt hN) (hval.trans hbound)

private theorem different_eq_top_of_ramificationIndex_eq_one
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (he : ramificationIndex K L = 1) : differentIdeal 𝒪[K] 𝒪[L] = ⊤ := by
  letI : Module.Finite 𝒪[K] 𝒪[L] := integerRingModuleFinite K L
  have hmap : 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] := by
    simpa only [he, pow_one] using map_maximalIdeal_eq_maximalIdeal_pow K L
  have hnot : ¬ 𝓂[L] ∣ differentIdeal 𝒪[K] 𝒪[L] := by
    have hmul : 𝓂[L] ^ 1 * 1 = 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) := by
      simpa only [pow_one, mul_one] using hmap.symm
    have hcrit := ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent.prime_power_divides_different_iff
      𝒪[K] (IsDiscreteValuationRing.not_a_field 𝒪[K]) 𝓂[L] 1 isCoprime_one_right hmul
    intro hd
    rcases hcrit.mp (by simpa only [pow_one] using hd) with hsep | hchar
    · exact hsep (inferInstance : Algebra.IsSeparable 𝓀[K] 𝓀[L])
    · exact one_ne_zero (by simpa only [Nat.cast_one] using hchar)
  by_contra hne
  exact hnot (Ideal.dvd_iff_le.mpr (IsLocalRing.le_maximalIdeal hne))

/-- The local Serre estimate in additive-valuation form, with no Galois hypothesis. -/
theorem not_pow_dvd_different_of_valuation_bound [Module.Finite K L]
    (N : ℕ)
    (hN : IsDiscreteValuationRing.addVal 𝒪[L] (ramificationIndex K L : 𝒪[L]) +
      (ramificationIndex K L - 1 : ℕ) < (N : ℕ∞)) :
    ¬ 𝓂[L] ^ N ∣ differentIdeal 𝒪[K] 𝒪[L] := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : Algebra.IsSeparable K L := inferInstance
  obtain ⟨M, hM⟩ := exists_unramified_residue_subextension K L
  letI := finiteExtensionValuativeRel K M
  letI := finiteExtensionNormedFieldTopology K M
  letI := finiteExtension_isNonarchimedeanLocalField K M
  letI := finiteExtension_valuativeExtension K M
  letI : ValuativeExtension M L := M.val.valuativeExtension
  letI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  obtain ⟨he, hres, _⟩ := hM
  letI : IsScalarTower 𝒪[K] 𝒪[M] 𝒪[L] :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
      simp only [coe_algebraMap_integerRing]
      exact IsScalarTower.algebraMap_apply K M L (x : K))
  letI : Module.Finite 𝒪[K] 𝒪[M] := integerRingModuleFinite K M
  letI : Module.Finite 𝒪[K] 𝒪[L] := integerRingModuleFinite K L
  letI : Module.Finite 𝒪[M] 𝒪[L] := integerRingModuleFinite M L
  have heML : ramificationIndex M L = ramificationIndex K L := by
    simpa only [he, one_mul] using
      (ramificationIndex_tower (K := K) (L := M) L).symm
  have htrivial : differentIdeal 𝒪[K] 𝒪[M] = ⊤ :=
    different_eq_top_of_ramificationIndex_eq_one K M he
  have hD : differentIdeal 𝒪[K] 𝒪[L] = differentIdeal 𝒪[M] 𝒪[L] := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal 𝒪[K] 𝒪[M] 𝒪[L],
      htrivial, Ideal.map_top, Ideal.mul_top]
  rw [hD]
  apply not_pow_dvd_different_of_residue_bijective M L hres N
  simpa only [heML] using hN

end TauCeti
