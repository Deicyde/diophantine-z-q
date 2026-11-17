/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/T21.lean
Original SHA-256: 4082dedb39b5e1f50951fe00cfb0ee20e7c3c895e40eb6c57b7e20c2dfd561b6
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

import ZInQKernel.Contrib.HilbertDifferent.T20
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.Different.Serre
import Mathlib.NumberTheory.Padics.LocalField

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- The rational-place valuation and global ideal-power application reuse the local different
estimate and the completion comparisons adapted from
TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d.
The parameter identifications use the pinned Mathlib API.
Full license and attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean. -/

/-! # Serre's different bound over number fields

The local derivative estimate is transported through the canonical completions and their
integer-ring equivalences, without a Galois hypothesis.
-/

noncomputable section
open IsDedekindDomain NumberField ValuativeRel IsLocalRing
open scoped NumberField AdicCompletionExtension WithZero

namespace ZInQKernel.Contrib.HilbertDifferent

private theorem multiplicity_rational_natCast (p : ℕ) [hp : Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)})
    (n : ℕ) (hn : n ≠ 0) :
    multiplicity v.asIdeal (Ideal.span {(n : 𝓞 ℚ)}) = padicValNat p n := by
  have hf : FiniteMultiplicity v.asIdeal (Ideal.span {(n : 𝓞 ℚ)}) :=
    FiniteMultiplicity.of_prime_left v.prime
      (by
        change Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥
        exact mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hn))
  apply hf.multiplicity_eq_iff.mpr
  constructor
  · rw [hv, Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    have hnat : p ^ padicValNat p n ∣ n := (padicValNat_dvd_iff_le hn).mpr le_rfl
    simpa only [Nat.cast_pow] using (Nat.cast_dvd_cast (α := 𝓞 ℚ) hnat)
  · rw [hv, Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    intro hd
    have hz := map_dvd Rat.ringOfIntegersEquiv hd
    simp only [map_pow, map_natCast] at hz
    have hnat : p ^ (padicValNat p n + 1) ∣ n := by exact_mod_cast hz
    have hle := (padicValNat_dvd_iff_le hn).mp hnat
    omega

private theorem addVal_rational_completion_natCast (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)})
    (n : ℕ) (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal 𝒪[v.adicCompletion ℚ] (n : 𝒪[v.adicCompletion ℚ]) =
      (padicValNat p n : ℕ∞) := by
  rw [TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton
    (Nat.cast_ne_zero.mpr hn)]
  let e := v.integerEquivAdicCompletionIntegers (K := ℚ)
  let E : Ideal 𝒪[v.adicCompletion ℚ] ≃* Ideal (v.adicCompletionIntegers ℚ) :=
    { e.idealComapOrderIso.symm.toEquiv with map_mul' := Ideal.map_mul e }
  have hm : multiplicity (maximalIdeal 𝒪[v.adicCompletion ℚ])
      (Ideal.span {(n : 𝒪[v.adicCompletion ℚ])}) =
      multiplicity (maximalIdeal (v.adicCompletionIntegers ℚ))
        (Ideal.span {(n : v.adicCompletionIntegers ℚ)}) := by
    rw [← multiplicity_map_eq E]
    change multiplicity ((maximalIdeal 𝒪[v.adicCompletion ℚ]).map e)
      ((Ideal.span {(n : 𝒪[v.adicCompletion ℚ])}).map e) = _
    rw [IsLocalRing.map_ringEquiv_maximalIdeal, Ideal.map_span, Set.image_singleton,
      map_natCast]
  rw [hm]
  have hs : Ideal.span {(n : v.adicCompletionIntegers ℚ)} =
      (Ideal.span {(n : 𝓞 ℚ)}).map (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)) := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hs, v.multiplicity_map_adicCompletionIntegers _
    (by exact mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hn)),
    multiplicity_rational_natCast p v hv n hn]

/-- Serre's different bound for every number field and every prime above a rational prime. -/
theorem serreDifferentBound
    (L : Type) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ *
      padicValNat p (P.ramificationIdx ℤ) + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hPp
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simp [hp.ne_zero]
  have hP0 : P ≠ ⊥ := by
    intro hzero
    have hunder := hPp.over
    rw [hzero, Ideal.under_bot] at hunder
    exact hp0 hunder
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, inferInstance, hP0⟩
  let v := w.under (𝓞 ℚ)
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (P.LiesOver (P.under (𝓞 ℚ)))
  have hZmap : algebraMap ℤ (𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  have hZsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) :=
    hZmap ▸ Rat.ringOfIntegersEquiv.symm.surjective
  have hvmap : v.asIdeal = (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 ℚ)) := by
    have h := Ideal.map_comap_of_surjective (algebraMap ℤ (𝓞 ℚ)) hZsurj v.asIdeal
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
      change (P.under (𝓞 ℚ)).under ℤ = _
      rw [Ideal.under_under, ← hPp.over]
    rw [← Ideal.under_def, hunder] at h
    exact h.symm
  have hv : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    simp only [hvmap, Ideal.map_span, Set.image_singleton, map_natCast]
  have he : TauCeti.ramificationIndex (v.adicCompletion ℚ) (w.adicCompletion L) =
      P.ramificationIdx ℤ := by
    rw [HeightOneSpectrum.ramificationIndex_adicCompletion v w,
      ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot,
      ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hp0]
    unfold Ideal.ramificationIdx'
    rw [hvmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have he0 : P.ramificationIdx ℤ ≠ 0 := by
    rw [← he]
    exact (TauCeti.ramificationIndex_pos (K := v.adicCompletion ℚ)
      (L := w.adicCompletion L)).ne'
  have hscale := TauCeti.addVal_algebraMap
    (K := v.adicCompletion ℚ) (L := w.adicCompletion L)
    (P.ramificationIdx ℤ : 𝒪[v.adicCompletion ℚ])
  rw [map_natCast, addVal_rational_completion_natCast p v hv _ he0,
    he, nsmul_eq_mul] at hscale
  have hlocal := TauCeti.not_pow_dvd_different_of_valuation_bound
    (v.adicCompletion ℚ) (w.adicCompletion L)
    (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ *
      padicValNat p (P.ramificationIdx ℤ) + 1) (by
      rw [he, hscale]
      exact_mod_cast (show P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) +
        (P.ramificationIdx ℤ - 1) < P.ramificationIdx ℤ - 1 +
          P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1 by omega))
  let : IsLocalization (⊥ : Submonoid ℤ) (𝓞 ℚ) :=
    IsLocalization.of_le_isUnit_of_bijective (by
      change Submonoid.map _ ⊥ ≤ _
      rw [Submonoid.map_bot]
      exact bot_le) (hZmap ▸ Rat.ringOfIntegersEquiv.symm.bijective)
  let : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (⊥ : Submonoid ℤ)) (𝓞 L) := by
    apply IsLocalization.of_le_isUnit
    change Submonoid.map _ ⊥ ≤ _
    rw [Submonoid.map_bot]
    exact bot_le
  have hbase : differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L) := by
    simpa using (TauCeti.map_differentIdeal_eq_differentIdeal
      (R := ℤ) (Rₘ := 𝓞 ℚ) (S := 𝓞 L) (Sₘ := 𝓞 L) (K := ℚ) (L := L) (M := ⊥))
  intro hdvd
  apply hlocal
  have hmultiplicity := v.differentExponent_adicCompletion_eq_multiplicity_differentIdeal w
  have hglobal := v.multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal w
  have hf : FiniteMultiplicity (maximalIdeal 𝒪[w.adicCompletion L])
      (differentIdeal 𝒪[v.adicCompletion ℚ] 𝒪[w.adicCompletion L]) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance)
      differentIdeal_ne_bot
  apply (hf.pow_dvd_iff_le_multiplicity).mpr
  rw [← TauCeti.differentExponent_def, hmultiplicity, hglobal, ← hbase]
  exact (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 inferInstance)
    differentIdeal_ne_bot).pow_dvd_iff_le_multiplicity.mp hdvd

end ZInQKernel.Contrib.HilbertDifferent
