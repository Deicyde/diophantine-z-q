/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/Completion.lean
Original SHA-256: a05b95011b9afaf11fdd6150e8527f93a24738cd389262e2d8c6ee47381082f5
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/AdicValuation/Completion.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


/-
## Provenance

Adapted, with the author's proof, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean` line 594, and
`EllipticCurves/Mathlib/AdicCompletionExtension.lean` for the filtration and Henselian results,
and for `residueFieldEquivAdicCompletionIntegers` and the approximation modulo the maximal ideal
behind it, which `exists_valued_sub_le` generalizes to every power of the maximal ideal.
The source states the contraction with `Ideal.comap` of an `algebraMap`; Mathlib spells that
`Ideal.under`, which is used here.
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Henselian
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

open WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/- The completion of a field of characteristic zero at a height-one prime has characteristic
zero, since the field embeds into it. -/
instance adicCompletion_charZero [CharZero K] (v : HeightOneSpectrum R) :
    CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/- The prime of `R` lying under the maximal ideal of the ring of integers of the completion of
`K` at `v` is `v` itself. -/
@[simp]
lemma under_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).under R = v.asIdeal := by
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `Valuation.mem_maximalIdeal_iff` apply here.
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']

section SingleCompletion

variable (v : HeightOneSpectrum R)

/- An element of `R`, mapped to `K_v` through `K`, is the image of its image in `𝒪_v`. -/
@[simp]
theorem algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (algebraMap R (v.adicCompletionIntegers K) r) := by
  rw [ValuationSubring.algebraMap_apply, algebraMap_adicCompletionIntegers_apply,
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
/- An element of `K` with valuation one is the image of a unit in the ring of integers of its
completion at `v`. -/
theorem valued_algebraMap_eq_exp_neg_one_of_irreducible {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `π`'s maximal ideal be retyped as an ideal of the valuation subring here.
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

/- The height-one prime `v` generates the maximal ideal of the ring of integers of the
completion at `v`. -/
@[simp]
theorem map_asIdeal_adicCompletionIntegers :
    Ideal.map (algebraMap R (v.adicCompletionIntegers K)) v.asIdeal =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap,
      ← Ideal.under_def, v.under_maximalIdeal_adicCompletionIntegers]
  · obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.intValuation_lt_one_iff_mem, hπ]
      simp
    have hπval : Valued.v
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) = exp (-1) := by
      rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
        valuation_of_algebraMap, hπ]
    have hπuni : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
        (algebraMap R (v.adicCompletionIntegers K) π : v.adicCompletion K) := by
      rwa [Valuation.IsUniformizer.iff,
        Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.valuedAdicCompletion_surjective K)]
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

/- An element of `𝒪_v` lies in the `n`-th power of the maximal ideal exactly when its valuation
is at most `exp (-n)`.

This identifies the ideal filtration of `𝒪_v` with the valuation filtration it inherits from
`K_v`, which is what makes the subspace topology visibly `𝔪`-adic below. -/
@[simp]
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hint := Valuation.valuationSubring.integers (v := (Valued.v : Valuation
    (v.adicCompletion K) ℤᵐ⁰))
  have hπn : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ n =
      exp (-(n : ℤ)) := by
    rw [v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
    simp
  rw [← hπn]
  exact Set.ext_iff.mp (hint.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n) x

/- An element of `R` lies in `v ^ n` exactly when its image in `K_v` has valuation at most
`exp (-n)`: the ideal filtration of `R` at `v` is the valuation filtration `K_v` induces on it. -/
theorem mem_asIdeal_pow_iff_valued_algebraMap_le {r : R} {n : ℕ} :
    r ∈ v.asIdeal ^ n ↔ Valued.v (algebraMap R (v.adicCompletion K) r) ≤ exp (-(n : ℤ)) := by
  rw [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    valuation_of_algebraMap, intValuation_le_pow_iff_mem]

/- The maximal ideal of the ring of integers of an adic completion contains a nonzero element
whose valuation is below the valuations of `a` and `b`, and below `1`. -/
instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/- **A closed valuation ball of `K_v` around the origin is open.**  The valuation of `K_v` is
surjective onto `ℤᵐ⁰`, so every nonzero bound is attained and the ball is the closed ball around a
point, which `Valued.isOpen_closedBall` shows is open. -/
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

/- **Each power of the maximal ideal of `𝒪_v` is open**: `𝔪 ^ n` is the preimage under the
inclusion `𝒪_v → K_v` of a closed valuation ball, and those are open. -/
theorem isOpen_maximalIdeal_pow_adicCompletionIntegers (n : ℕ) :
    IsOpen ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
  have h : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
      (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
        {y : v.adicCompletion K | Valued.v y ≤ exp (-(n : ℤ))} :=
    Set.ext fun x ↦ v.mem_maximalIdeal_pow_iff (K := K)
  rw [h]
  exact (v.isOpen_setOf_valued_le (K := K) exp_ne_zero).preimage continuous_subtype_val

/- **Every neighbourhood of `0` in `𝒪_v` contains a power of the maximal ideal.** A neighbourhood
is cut out by a valuation bound, and `exp` takes some integer below that bound; the corresponding
`𝔪 ^ n` is then undercut by it. -/
theorem exists_maximalIdeal_pow_subset_of_mem_nhds {s : Set (v.adicCompletionIntegers K)}
    (hs : s ∈ nhds 0) : ∃ n : ℕ, ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) ⊆ s := by
  obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
  rw [ZeroMemClass.coe_zero] at ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
  obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine ⟨log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, ?_⟩
    conv_rhs => rw [← exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)]
    exact exp_lt_exp.mpr (by lia)
  refine ⟨(-m).toNat, fun x hx ↦ hts ?_⟩
  refine Set.mem_preimage.mpr (hγ ?_)
  have h1 := v.mem_maximalIdeal_pow_iff (K := K) |>.mp hx
  refine Set.mem_ofPred.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
    (h1.trans_lt ?_))
  calc exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by lia)
    _ < _ := hm

/- The subspace topology on the ring of integers `𝒪_v` of an adic completion is the `𝔪`-adic
topology of its maximal ideal. -/
theorem exists_valued_sub_le (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) ≤
      exp (-(n : ℤ)) := by
  -- the elements of `𝒪_v` congruent to `x` modulo `𝔪 ^ n` form an open subset of `K_v`
  let U : Set (v.adicCompletionIntegers K) := (· - x) ⁻¹'
    ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
  have hU : IsOpen (((↑) : v.adicCompletionIntegers K → v.adicCompletion K) '' U) :=
    (Valued.isOpen_valuationSubring _).isOpenMap_subtype_val _
      ((v.isOpen_maximalIdeal_pow_adicCompletionIntegers n).preimage (continuous_sub_right x))
  -- so it contains an element `z` of `K`, which is then integral at `v`
  obtain ⟨z, y, hy, hyz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
    ⟨x, x, by simp [U], rfl⟩
  have hz : v.valuation K z ≤ 1 := by
    have hy1 : Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 :=
      hyz ▸ (mem_adicCompletionIntegers R K v).mp y.2
    rwa [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation'] at hy1
  -- and `z` is approximated by an element of `R`
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
  refine ⟨a, ?_⟩
  have hxy : Valued.v ((x : v.adicCompletion K) - y) ≤ exp (-(n : ℤ)) := by
    have hy' := (v.mem_maximalIdeal_pow_iff (K := K)).mp hy
    rwa [AddSubgroupClass.coe_sub, Valuation.map_sub_swap] at hy'
  have hza : Valued.v ((y : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) ≤
      exp (-(n : ℤ)) := by
    rw [hyz, IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, Valuation.map_sub_swap]
    exact ha.le
  rw [← sub_add_sub_cancel _ (y : v.adicCompletion K)]
  exact Valuation.map_add_le _ hxy hza

/- **`R` is dense in the ring of integers of its completion at `v`.** Equivalently, every
neighbourhood of an element of `𝒪_v` contains the image of an element of `R`. -/
noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_le (K := K) x 1
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine Ideal.Quotient.eq.mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    push_cast [IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K)]
    rw [Valuation.map_sub_swap]
    exact ha.trans_lt (by simp)

/- The residue field of an adic completion is finite when the residue field at `v` is finite. -/
@[simp]
theorem residueFieldEquivAdicCompletionIntegers_apply_mk (a : R) :
    v.residueFieldEquivAdicCompletionIntegers (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (algebraMap R (v.adicCompletionIntegers K) a) := (rfl)

end SingleCompletion

end IsDedekindDomain.HeightOneSpectrum

end
