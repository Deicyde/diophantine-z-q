/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/NormalizedValuation.lean
Original SHA-256: 62b890392eb51ba19e933d610dc9549e1d4d4c98bbb685b37a6832d4d75c10f9
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
TauCeti/NumberTheory/LocalField/NormalizedValuation.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.Support.Valuation
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import ZInQKernel.Contrib.HilbertDifferent.Data.Int.WithZero
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.AbsoluteValue
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.Discrete.Order
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- The declaration sequence follows the human-authored specification in
-- `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`.
variable (K) in
/- The normalized valuation `v_K^×` of a nonarchimedean local field `K`: the composite of
`ValuativeRel.valuation K` with the order isomorphism `valueGroupWithZeroIsoInt` of the value
group with `ℤᵐ⁰`, read additively and with the sign chosen so that a uniformizer has value
`Multiplicative.ofAdd 1`. -/
def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  invMonoidHom.comp
    ((((Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).trans
      WithZero.unitsWithZeroEquiv).toMonoidHom).comp
        (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom))

variable (K) in
/- The normalized valuation extended across zero, as a zero-preserving monoid homomorphism
from `K` to `ℤᵐ⁰`. -/
def normalizedValuationWithZero : K →*₀ ℤᵐ⁰ :=
  invMonoidWithZeroHom.comp
    ((valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.comp
      (valuation K).toMonoidWithZeroHom)

private noncomputable def intValuation : Valuation K ℤᵐ⁰ :=
  LanglandsFirstMainLemma.normalizedMultiplicativeValuation K

private theorem intValuation_surjective : Function.Surjective (intValuation (K := K)) := by
  intro z
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective ((valueGroupWithZeroIsoInt K).symm z)
  refine ⟨x, ?_⟩
  simp [intValuation, LanglandsFirstMainLemma.normalizedMultiplicativeValuation, hx]

private theorem intValuation_valuationSubring :
    (intValuation (K := K)).valuationSubring.toSubring = 𝒪[K] := by
  ext x
  -- Unfold mapped-valuation membership to expose the comparison transported by the order
  -- isomorphism; the valuation-subring API has no lemma stating this composite equality.
  change valueGroupWithZeroIsoInt K (valuation K x) ≤ 1 ↔ valuation K x ≤ 1
  simpa only [map_one] using
    (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K)
      (a := valuation K x) (b := 1))

private theorem intValuation_eq_maximalIdeal_valuation :
    intValuation (K := K) = (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation K := by
  have hv : Function.Surjective (intValuation (K := K)) := intValuation_surjective
  have : IsDiscreteValuationRing (intValuation (K := K)).valuationSubring :=
    Valuation.valuationSubring_isDiscreteValuationRing_of_surjective _ hv
  -- Both valuations are surjective and normalized, so it is enough to see that they have the
  -- same valuation subring, namely `𝒪[K]`.
  refine Valuation.eq_of_isEquiv_of_surjective hv
    (IsDedekindDomain.HeightOneSpectrum.valuation_surjective K _)
    ((Valuation.isEquiv_iff_valuationSubring ..).mpr ?_)
  refine ValuationSubring.eq_of_le_of_ne_top
    (A := (intValuation (K := K)).valuationSubring) ?_ ?_
  · intro x hx
    have hx' : x ∈ 𝒪[K] := by rwa [← intValuation_valuationSubring]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]) (K := K) (⟨x, hx'⟩ : 𝒪[K])
  · simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance

/- The zero-preserving normalized valuation vanishes exactly at zero. -/
@[simp]
theorem normalizedValuationWithZero_coe (x : Kˣ) :
    normalizedValuationWithZero K (x : K) = (normalizedValuation K x : ℤᵐ⁰) := by
  simp [normalizedValuationWithZero, normalizedValuation, invMonoidWithZeroHom]

/- The normalized valuation of a local field is the order of vanishing along `𝒪[K]`: it agrees
with Mathlib's `Ring.ordFrac`, the canonical `ℤᵐ⁰`-valued order map of a discrete valuation ring
on its fraction field. The `Ring.ordFrac` API therefore applies to `normalizedValuationWithZero`.
-/
theorem normalizedValuationWithZero_eq_ordFrac :
    normalizedValuationWithZero K = Ring.ordFrac 𝒪[K] := by
  ext x
  rw [Ring.ordFrac_eq_valuation_inv, ← intValuation_eq_maximalIdeal_valuation]
  simp [normalizedValuationWithZero, intValuation, LanglandsFirstMainLemma.normalizedMultiplicativeValuation, invMonoidWithZeroHom]

/- The zero-preserving normalized valuation is the inverse of any surjective `ℤᵐ⁰`-valued
valuation compatible with the valuative relation of `K`. This is how a concrete discrete
valuation, such as the adic valuation of a completion, is read as the normalized one. -/
theorem _root_.Valuation.normalizedValuationWithZero_eq_inv_of_surjective
    (v : Valuation K ℤᵐ⁰) [v.Compatible]
    (hv : Function.Surjective v) (x : K) :
    normalizedValuationWithZero K x = (v x)⁻¹ := by
  have h : intValuation (K := K) x = v x :=
    DFunLike.congr_fun (Valuation.eq_of_isEquiv_of_surjective intValuation_surjective hv
      ((Valuation.isEquiv_map_self_of_strictMono _
          (EquivLike.injective (valueGroupWithZeroIsoInt K))).trans
        (ValuativeRel.isEquiv _ _))) x
  rw [← h]
  simp [normalizedValuationWithZero, intValuation, LanglandsFirstMainLemma.normalizedMultiplicativeValuation, invMonoidWithZeroHom]

/- The translation between Mathlib's multiplicative valuation and the additive normalization:
the normalized valuation is minus the logarithm of `ValuativeRel.valuation`, transported to
`ℤᵐ⁰`. Every comparison of the two conventions goes through this lemma. -/
theorem toAdd_normalizedValuation_eq_neg_log (x : Kˣ) :
    (normalizedValuation K x).toAdd
      = -WithZero.log (valueGroupWithZeroIsoInt K (valuation K (x : K))) := by
  simp [normalizedValuation, ← WithZero.toAdd_unzero_eq_log]

private theorem toAdd_normalizedValuation_eq_ord (x : Kˣ) :
    (normalizedValuation K x).toAdd = Valuation.ord (intValuation (K := K)) (x : K) := by
  rw [toAdd_normalizedValuation_eq_neg_log, Valuation.ord_def]
  -- Both sides now unfold to the logarithm of the transported valuation; there is no named
  -- bridge between these two nested homomorphism presentations.
  rfl

theorem valueGroupWithZeroIsoInt_valuation (x : Kˣ) :
    valueGroupWithZeroIsoInt K (valuation K (x : K))
      = WithZero.exp (-(normalizedValuation K x).toAdd) := by
  rw [toAdd_normalizedValuation_eq_ord]
  exact Valuation.valuation_eq_exp_neg_ord (intValuation (K := K)) x.ne_zero

/- The normalized valuation vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem normalizedValuation_eq_one_iff (x : Kˣ) :
    normalizedValuation K x = 1 ↔ valuation K (x : K) = 1 := by
  rw [← toAdd_eq_zero, toAdd_normalizedValuation_eq_ord,
    Valuation.ord_eq_iff_valuation_eq_exp_neg (intValuation (K := K)) x.ne_zero]
  simp [intValuation, LanglandsFirstMainLemma.normalizedMultiplicativeValuation]

/- The normalized valuation vanishes on every root of unity: `Multiplicative ℤ` is torsion
free, so a unit of finite order has normalized valuation `1`. -/
theorem mem_integer_iff_toAdd_normalizedValuation_nonneg (x : Kˣ) :
    (x : K) ∈ 𝒪[K] ↔ 0 ≤ (normalizedValuation K x).toAdd := by
  rw [Valuation.mem_integer_iff, toAdd_normalizedValuation_eq_ord]
  -- Transport the valuation comparison through the order isomorphism before identifying the
  -- mapped valuation below.
  rw [show valuation K (x : K) ≤ 1 ↔
      valueGroupWithZeroIsoInt K (valuation K (x : K)) ≤ valueGroupWithZeroIsoInt K 1 from
    (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K) :
      valueGroupWithZeroIsoInt K (valuation K (x : K)) ≤ valueGroupWithZeroIsoInt K 1 ↔
        valuation K (x : K) ≤ 1).symm]
  simp only [map_one]
  -- Unfold the mapped valuation and its valuation-subring membership so that the generic
  -- order characterization applies; the API does not expose this as a rewrite lemma.
  change intValuation (K := K) (x : K) ≤ 1 ↔
    0 ≤ Valuation.ord (intValuation (K := K)) (x : K)
  exact Valuation.mem_valuationSubring_iff_ord_nonneg (intValuation (K := K))

/- The normalized value group of a nonarchimedean local field is all of `ℤ`. -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  intro n
  obtain ⟨x, hx⟩ := Valuation.ord_surjective (intValuation (K := K))
    intValuation_surjective n.toAdd
  rcases eq_or_ne x 0 with rfl | hx0
  · have hn : n = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hx.symm
    exact ⟨1, by simp [hn]⟩
  · refine ⟨Units.mk0 x hx0, ?_⟩
    apply Multiplicative.toAdd.injective
    simpa [toAdd_normalizedValuation_eq_ord] using hx

/- An element of the ring of integers is a unit there exactly when its zero-preserving
normalized valuation is one. -/
theorem exists_eq_mul_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    ∃ (u : Kˣ) (n : ℤ), valuation K (u : K) = 1 ∧
      x = u * Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h)) ^ n := by
  let hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨n, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := 𝒪[K]) hπ x.ne_zero
  let uK : Kˣ := Units.map (algebraMap 𝒪[K] K).toMonoidHom u
  refine ⟨uK, n, ?_, ?_⟩
  · exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  · apply Units.ext
    -- The algebra map from the valuation subring is definitionally its subtype coercion; expose
    -- that equality before applying the DVR decomposition equation.
    rw [show algebraMap 𝒪[K] K π = (π : K) by rfl] at hx
    simpa [uK, Units.smul_def, Algebra.smul_def] using hx

/- The normalized valuation of an irreducible element of `𝒪[K]`, that is of a uniformizer of
`K`, is `Multiplicative.ofAdd 1`. -/
@[simp]
theorem normalizedValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    normalizedValuation K
      (Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))) = Multiplicative.ofAdd 1 := by
  have h : normalizedValuationWithZero K (π : K) = WithZero.exp 1 := by
    rw [normalizedValuationWithZero_eq_ordFrac]
    exact Ring.ordFrac_irreducible (K := K) hπ
  -- Read the equation on `Kˣ`: the algebra map out of `𝒪[K]` is the subtype coercion, so `π` is
  -- the underlying element of the unit displayed in the statement.
  rw [show (π : K) = ((Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h)) : Kˣ) : K) from rfl,
    normalizedValuationWithZero_coe, WithZero.exp_eq_coe_ofAdd] at h
  exact_mod_cast h

/- The normalized valuation is the unique homomorphism `Kˣ →* Multiplicative ℤ` that vanishes
on the elements of valuation `1` and takes the value `Multiplicative.ofAdd 1` at a uniformizer. -/
section NormalizedAbsoluteValue

open scoped NNRat

private theorem one_lt_residueFieldCard :
    (1 : ℚ≥0) < Nat.card 𝓀[K] := by
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])

variable (K) in
/- The normalized absolute value of a nonarchimedean local field, with values in `ℚ≥0`.
For a nonzero element `x`, its value is `q ^ (-v_K(x))`, where
`q = Nat.card 𝓀[K]` is the cardinality of the residue field. -/
noncomputable def normalizedAbsoluteValue : AbsoluteValue K ℚ≥0 :=
  (intValuation (K := K)).toAbsoluteValue
    (WithZeroMulInt.toNNRat (one_lt_residueFieldCard (K := K)).ne_zero)
    (fun _ _ h ↦
      (WithZeroMulInt.toNNRat_strictMono (one_lt_residueFieldCard (K := K))).monotone h)
    (fun _ ↦ map_eq_zero _)

/- The normalized absolute value is the rational power `q ^ (-v_K(x))` at every nonzero
element, where `q` is the cardinality of the residue field. -/
theorem isNonarchimedean_normalizedAbsoluteValue :
    IsNonarchimedean (normalizedAbsoluteValue K) := by
  apply Valuation.isNonarchimedean_toAbsoluteValue

/- The normalized absolute value induces the order of Mathlib's valuation. -/
@[simp]
theorem normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff (x y : K) :
    normalizedAbsoluteValue K x ≤ normalizedAbsoluteValue K y ↔
      valuation K x ≤ valuation K y := by
  rw [normalizedAbsoluteValue, Valuation.toAbsoluteValue_apply, Valuation.toAbsoluteValue_apply,
    (WithZeroMulInt.toNNRat_strictMono (one_lt_residueFieldCard (K := K))).le_iff_le]
  exact OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K)

/- The normalized absolute value induces the strict order of Mathlib's valuation. -/
@[simp]
theorem normalizedAbsoluteValue_lt_normalizedAbsoluteValue_iff (x y : K) :
    normalizedAbsoluteValue K x < normalizedAbsoluteValue K y ↔
      valuation K x < valuation K y := by
  simp only [lt_iff_not_ge, normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff]

/- The normalized absolute value is less than one exactly on the elements of valuation less than
one, that is, on the maximal ideal of the ring of integers. -/
@[simp]
theorem normalizedAbsoluteValue_lt_one_iff (x : K) :
    normalizedAbsoluteValue K x < 1 ↔ valuation K x < 1 := by
  simpa using normalizedAbsoluteValue_lt_normalizedAbsoluteValue_iff x 1

/- The normalized absolute value takes the value one exactly on the elements of valuation one,
that is, on the units of the ring of integers. -/
@[simp]
theorem mem_integer_iff_normalizedAbsoluteValue_le_one (x : K) :
    x ∈ 𝒪[K] ↔ normalizedAbsoluteValue K x ≤ 1 := by
  rw [Valuation.mem_integer_iff, normalizedAbsoluteValue, Valuation.toAbsoluteValue_apply,
    WithZeroMulInt.toNNRat_le_one_iff]
  · -- `Valuation.map_apply` encounters the two propositionally equal preorder instances on
    -- `ℤᵐ⁰` under `≤`; expose the mapped value before transporting the comparison.
    change valuation K x ≤ 1 ↔ valueGroupWithZeroIsoInt K (valuation K x) ≤ 1
    simpa only [map_one] using
      (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K)
        (a := valuation K x) (b := 1)).symm
  · exact one_lt_residueFieldCard (K := K)

/- The normalized absolute value is one on every unit of the ring of integers. -/
end NormalizedAbsoluteValue

end TauCeti
