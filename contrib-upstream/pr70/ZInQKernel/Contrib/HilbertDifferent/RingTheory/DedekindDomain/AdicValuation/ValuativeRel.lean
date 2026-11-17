/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/ValuativeRel.lean
Original SHA-256: c1eeea9d7ae54fba999984ed4319a04c2bcb05e95864e5495299454209c392b9
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
TauCeti/RingTheory/DedekindDomain/AdicValuation/ValuativeRel.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.NormalizedValuation
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.Completion
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel Valued.integer

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

-- The declaration sequence and construction follow the human-authored specification in
-- `TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean`.
/- The valuative relation on an adic completion induced by its canonical adic valuation. -/
noncomputable instance instValuativeRelAdicCompletion : ValuativeRel (v.adicCompletion K) :=
  .ofValuation Valued.v

/- The canonical adic valuation is compatible with the valuative relation it induces. -/
instance instCompatibleValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

/- The topology of an adic completion is induced by its canonical valuative relation. -/
instance isValuativeTopologyAdicCompletion : IsValuativeTopology (v.adicCompletion K) := by
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
  intro s
  exact Valued.is_topological_valuation s

/- The canonical valuative relation on an adic completion is nontrivial. -/
instance isNontrivialAdicCompletion : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) |>.mpr inferInstance

/- The ring of integers of the valuative relation is the canonical ring of integers `𝒪_v`. -/
theorem integer_eq_adicCompletionIntegers :
    𝒪[v.adicCompletion K] = (v.adicCompletionIntegers K).toSubring := by
  ext x
  rw [ValuationSubring.mem_toSubring, mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (v.adicCompletion K))).symm.trans
    (Valuation.vle_one_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))

/- The ring of integers of the valuative relation of `K_v` is the canonical ring of integers
`𝒪_v`, as a ring isomorphism: the two are the same subring of `K_v`, carrying different
instances. The codomain is written as `v.adicCompletionIntegers K` and not as its `toSubring`,
whose coercion is the same type but carries no `IsLocalRing` instance. -/
def integerEquivAdicCompletionIntegers :
    𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K :=
  RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v)

/- The identification of the two rings of integers is the identity on elements of `K_v`. -/
@[simp]
theorem coe_integerEquivAdicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    (v.integerEquivAdicCompletionIntegers (K := K) x : v.adicCompletion K) =
      (x : v.adicCompletion K) := (rfl)

/- The inverse identification of the two rings of integers is the identity on elements of
`K_v`. -/
@[simp]
theorem coe_integerEquivAdicCompletionIntegers_symm (x : v.adicCompletionIntegers K) :
    ((v.integerEquivAdicCompletionIntegers (K := K)).symm x : v.adicCompletion K) =
      (x : v.adicCompletion K) := (rfl)

/- An element of the ring of integers of the valuative relation on `K_v` lies in the `n`-th power
of its maximal ideal exactly when its valuation is at most `exp (-n)`. This is
`mem_maximalIdeal_pow_iff`, read through `integerEquivAdicCompletionIntegers`. -/
theorem mem_maximalIdeal_integer_pow_iff {x : 𝒪[v.adicCompletion K]} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal 𝒪[v.adicCompletion K] ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  let e := v.integerEquivAdicCompletionIntegers (K := K)
  rw [← coe_integerEquivAdicCompletionIntegers v x, ← mem_maximalIdeal_pow_iff,
    ← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_bijective _ e.bijective]

/- An element of `K_v` lies in `𝒪_v` exactly when the valuation of the valuative relation is at
most `1`. This is Mathlib's `mem_adicCompletionIntegers`, which is stated for the adic valuation
`Valued.v`, read through the valuative relation. -/
-- This is intentionally not a simp lemma: it would make the upstream theorem
-- `adicCompletionExtension_mem_adicCompletionIntegers` fail the simp-normal-form linter, while
-- that theorem's module cannot import this valuative adapter without creating an import cycle.
theorem mem_adicCompletionIntegers_iff_valuation_le_one (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔
      ValuativeRel.valuation (v.adicCompletion K) x ≤ 1 := by
  rw [← Valuation.mem_integer_iff, integer_eq_adicCompletionIntegers,
    ValuationSubring.mem_toSubring]

/- **`𝒪_v` is a ring of integers of `K_v`.** The canonical ring of integers satisfies
`Valuation.Integers` for the valuation of the valuative relation of `K_v`, which is the form in
which the theory of local fields consumes a ring of integers. -/
theorem valuation_integers_adicCompletionIntegers :
    (ValuativeRel.valuation (v.adicCompletion K)).Integers (v.adicCompletionIntegers K) where
  hom_inj := Subtype.val_injective
  map_le_one x := (v.mem_adicCompletionIntegers_iff_valuation_le_one (K := K) x.1).mp x.2
  exists_of_le_one {r} hr :=
    ⟨⟨r, (v.mem_adicCompletionIntegers_iff_valuation_le_one (K := K) r).mpr hr⟩, rfl⟩

/- An element of `R` lands in the ring of integers of the valuative relation on `K_v`. -/
theorem algebraMap_mem_integer_adicCompletion (a : R) :
    algebraMap R (v.adicCompletion K) a ∈ 𝒪[v.adicCompletion K] := by
  rw [integer_eq_adicCompletionIntegers, ValuationSubring.mem_toSubring]
  exact coe_mem_adicCompletionIntegers v a

/- The residue field of the valuative relation on `K_v` is the residue field `R ⧸ v` of `v`. -/
noncomputable def residueFieldEquivAdicCompletion :
    (R ⧸ v.asIdeal) ≃+* 𝓀[v.adicCompletion K] :=
  (v.residueFieldEquivAdicCompletionIntegers (K := K)).trans
    (IsLocalRing.ResidueField.mapEquiv
      (v.integerEquivAdicCompletionIntegers (K := K)).symm)

/- **The residue-field equivalence on a quotient representative.** This is the characterization
consumers should use; the construction of the equivalence is an implementation detail and should
not be unfolded. -/
@[simp]
theorem residueFieldEquivAdicCompletion_apply_mk (a : R) :
    v.residueFieldEquivAdicCompletion (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      IsLocalRing.residue _ (⟨algebraMap R (v.adicCompletion K) a,
        v.algebraMap_mem_integer_adicCompletion (K := K) a⟩ : 𝒪[v.adicCompletion K]) := by
  let e : v.adicCompletionIntegers K ≃+* 𝒪[v.adicCompletion K] :=
    (v.integerEquivAdicCompletionIntegers (K := K)).symm
  have hcomp : v.residueFieldEquivAdicCompletion (K := K)
      (Ideal.Quotient.mk v.asIdeal a) =
      IsLocalRing.ResidueField.mapEquiv e
        (v.residueFieldEquivAdicCompletionIntegers (K := K)
          (Ideal.Quotient.mk v.asIdeal a)) :=
    RingEquiv.trans_apply _ _ _
  have hx : v.residueFieldEquivAdicCompletionIntegers (K := K)
      (Ideal.Quotient.mk v.asIdeal a) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) a) :=
    v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := K) a
  rw [hcomp, hx, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  apply congrArg (IsLocalRing.residue _)
  apply Subtype.ext
  dsimp only [e]
  calc
    _ = ↑(algebraMap R (v.adicCompletionIntegers K) a) :=
      RingEquiv.coe_subringCongr_apply
        (integer_eq_adicCompletionIntegers v).symm _
    _ = _ := IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K) a

/- If `R` is infinite, the residue field of `K_v` has cardinality the absolute norm of `v`. -/
instance isNonarchimedeanLocalField_adicCompletion [Finite (R ⧸ v.asIdeal)] :
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  -- The discrete valuation admits a rank-one normalization; its chosen base does not affect the
  -- topology.
  let _ : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (by norm_num : (1 : NNReal) < 2)
  let _ : NormedField (v.adicCompletion K) :=
    Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰
  -- The residue field of `𝒪_v` is `R ⧸ v`, which is finite.
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  -- Local compactness comes from Mathlib's criterion for the `Valued` structure of `K_v`. That
  -- criterion is stated for `Valued.integer`, which unfolds to `v.adicCompletionIntegers K`, so
  -- its two inputs are supplied by `inferInstanceAs` at the latter.
  let _ : ProperSpace (v.adicCompletion K) :=
    (@properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (v.adicCompletion K) ℤᵐ⁰ _ _
      (inferInstance : Valued (v.adicCompletion K) ℤᵐ⁰) inferInstance).mpr
      ⟨inferInstance,
        inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))⟩
  exact ⟨⟩

/- The zero-preserving normalized valuation of the completion `K_v` is the inverse of its adic
valuation `Valued.v`. -/
@[simp]
theorem normalizedValuationWithZero_adicCompletion [Finite (R ⧸ v.asIdeal)]
    (x : v.adicCompletion K) :
    TauCeti.normalizedValuationWithZero (v.adicCompletion K) x = (Valued.v x)⁻¹ :=
  Valuation.normalizedValuationWithZero_eq_inv_of_surjective _
    (v.valuedAdicCompletion_surjective K) x

/- The ring of integers in an adic completion that is a nonarchimedean local field is compact. -/
instance compactSpace_adicCompletionIntegers
    [IsNonarchimedeanLocalField (v.adicCompletion K)] :
    CompactSpace (v.adicCompletionIntegers K) := by
  let f : 𝒪[v.adicCompletion K] ≃ₜ v.adicCompletionIntegers K := {
    toEquiv := (v.integerEquivAdicCompletionIntegers (K := K)).toEquiv
    continuous_toFun := continuous_induced_rng.mpr <|
      continuous_subtype_val.congr fun x ↦
        (v.coe_integerEquivAdicCompletionIntegers (K := K) x).symm
    continuous_invFun := continuous_induced_rng.mpr <|
      continuous_subtype_val.congr fun x ↦
        (v.coe_integerEquivAdicCompletionIntegers_symm (K := K) x).symm }
  exact f.compactSpace

/- **An element of odd order of vanishing at `v` is a nonsquare in the completion `K_v`.**

The hypothesis `v.valuation K a = WithZero.exp n` with `¬ Even n` says that the valuation exponent
of `a` at `v` is `n`, that is, that its order of vanishing is the odd integer `-n`.  This is the
nonsquare criterion a finite place of a prescribed set needs: an element that vanishes there to odd
order remains a nonsquare in the completion.

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, whose
multiplicative identity `1` is the value zero, that is, order of vanishing zero, so an order of
vanishing `1` is written `WithZero.exp (-1)`, the value of a generator of `v.asIdeal`; the passage
between the two conventions is `neg_log_valuation_eq_one_iff` in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic`. -/
end IsDedekindDomain.HeightOneSpectrum

end
