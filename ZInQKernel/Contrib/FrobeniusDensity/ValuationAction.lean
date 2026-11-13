/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors of the two valuation-power lemmas: The Tau Ceti contributors

Modified for this contribution: moved the two upstream lemmas to a local
namespace, added the exact stabilizer, conjugation, and restriction statements,
and used only the project's pinned Mathlib. Upstream source:
TauCeti/RingTheory/Valuation/FrobeniusElement.lean at
30f41378f0cb1d569f51d8a4d0cb74aea8a80e44, lines 43–74.
See docs/research/t18-frobenius-density.md for provenance and license text.
-/
import ZInQKernel.Contrib.FrobeniusDensity.Defs
import Mathlib.FieldTheory.Normal.Basic

/-!
# Arithmetic Frobenius conventions at an actual valuation

These proofs do not assume Chebotarev or the existence of a Frobenius lift.
The congruence is imposed on every element of the valuation ring, not merely
on algebraic integers. For positive residue powers it itself forces stabilization.
-/

namespace ZInQ.Contrib.FrobeniusDensity

open IsLocalRing
open scoped Pointwise

section ValuationPower

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation L Γ) {q : ℕ}

/-- A power-residue congruence preserves the valuation ring and has exactly the
forward power action on residues. Adapted from the cited Tau Ceti proof. -/
theorem exists_le_one_and_residue_eq_pow {τ : L → L}
    (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ q) < 1) {z : L} (hz : v z ≤ 1) :
    ∃ hτz : v (τ z) ≤ 1,
      residue v.valuationSubring ⟨τ z, (v.mem_valuationSubring_iff _).mpr hτz⟩ =
        residue v.valuationSubring ⟨z, (v.mem_valuationSubring_iff z).mpr hz⟩ ^ q := by
  have hzq : v (z ^ q) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one' hz _
  have hτz : v (τ z) ≤ 1 := by
    rw [← sub_add_cancel (τ z) (z ^ q)]
    exact v.map_add_le (hτ z hz).le hzq
  refine ⟨hτz, ?_⟩
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  exact hτ z hz

/-- A nonzero power-residue congruence also preserves poles. Adapted from the
cited Tau Ceti proof. -/
theorem one_lt_map_of_one_lt {R : Type*} [FunLike R L L] [RingHomClass R L L]
    (hq : q ≠ 0) {τ : R} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ q) < 1)
    {x : L} (hx : 1 < v x) : 1 < v (τ x) := by
  have hinv : v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hx
  have h' : v (τ x⁻¹) < 1 := by
    rw [← sub_add_cancel (τ x⁻¹) (x⁻¹ ^ q)]
    refine v.map_add_lt (hτ _ hinv.le) ?_
    rw [map_pow]
    exact pow_lt_one₀ zero_le hinv hq
  have hx0 : τ x ≠ 0 :=
    (map_ne_zero τ).mpr (v.ne_zero_iff.mp (zero_lt_one.trans hx).ne')
  rwa [map_inv₀, map_inv₀, inv_lt_one₀ (v.pos_iff.mpr hx0)] at h'

end ValuationPower

/-- Pullback preserves the actual maximal-ideal membership, not only ring
membership. This avoids silently reversing a valuation restriction. -/
theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L]
    (v : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (v.comap f).nonunits ↔ f x ∈ v.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

/-- The congruence on the entire valuation ring forces the automorphism to
stabilize the valuation, provided the residue power is nonzero. -/
theorem mem_decompositionSubgroup_of_congruence {K L : Type*} [Field K] [Field L]
    [Algebra K L] {σ : L ≃ₐ[K] L} {v : ValuationSubring L} {q : ℕ} (hq : q ≠ 0)
    (hσ : ∀ x ∈ v, σ x - x ^ q ∈ v.nonunits) : σ ∈ v.decompositionSubgroup K := by
  have hpow : ∀ x, v.valuation x ≤ 1 → v.valuation (σ x - x ^ q) < 1 := by
    intro x hx
    exact hσ x ((v.valuation_le_one_iff x).mp hx)
  have hmem (x : L) : σ x ∈ v ↔ x ∈ v := by
    constructor
    · intro hx
      by_contra h
      have hlt : 1 < v.valuation x := by
        apply lt_of_not_ge
        intro hle
        exact h ((v.valuation_le_one_iff x).mp hle)
      exact (not_lt_of_ge ((v.valuation_le_one_iff _).mpr hx))
        (one_lt_map_of_one_lt v.valuation hq hpow hlt)
    · intro hx
      exact (v.valuation_le_one_iff _).mp
        (exists_le_one_and_residue_eq_pow v.valuation hpow
          ((v.valuation_le_one_iff _).mpr hx)).choose
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change σ.symm x ∈ v ↔ x ∈ v
  simpa only [AlgEquiv.apply_symm_apply] using (hmem (σ.symm x)).symm

/-- Under the prime/nonzero hypothesis of T18, stabilization is not an
additional unproved local condition. -/
theorem isArithFrob_iff_congruence {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p ≠ 0) : IsArithFrob σ v p ↔ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits :=
  ⟨And.right, fun h => ⟨mem_decompositionSubgroup_of_congruence hp h, h⟩⟩

/-- Transporting a valuation transports its maximal ideal in the forward
Galois-action direction. -/
theorem apply_mem_nonunits_smul_iff (g : GQ) (v : ValuationSubring Qbar) (x : Qbar) :
    g x ∈ (g • v).nonunits ↔ x ∈ v.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ← map_inv₀]
  change (g x = 0 ∨ ¬ g • x⁻¹ ∈ g • v) ↔ (x = 0 ∨ ¬ x⁻¹ ∈ v)
  rw [ValuationSubring.smul_mem_pointwise_smul_iff]
  simp only [map_eq_zero]

/-- The underlying rational prime is unchanged when its valuation is
conjugated by an absolute Galois automorphism. -/
theorem liesOver_smul_iff (g : GQ) (v : ValuationSubring Qbar) (p : ℕ) :
    LiesOver (g • v) p ↔ LiesOver v p := by
  simpa only [LiesOver, map_natCast] using apply_mem_nonunits_smul_iff g v (p : Qbar)

/-- Conjugating Frobenius requires transporting its valuation as well.
The orientation is `g * τ * g⁻¹` at `g • v`, never a geometric inverse. -/
theorem IsArithFrob.conj {τ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hτ : IsArithFrob τ v p) (hp : p ≠ 0) (g : GQ) :
    IsArithFrob (g * τ * g⁻¹) (g • v) p := by
  apply (isArithFrob_iff_congruence hp).mpr
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g x v).mp hx
  change g (τ (g.symm (g y))) - (g y) ^ p ∈ (g • v).nonunits
  rw [AlgEquiv.symm_apply_apply, ← map_pow, ← map_sub]
  exact (apply_mem_nonunits_smul_iff g v _).mpr (hτ.2 y hy)

/-- Actual arithmetic Frobenius restricts along a normal subfield and the
valuation pulls back along the inclusion. The exponent remains `p`. -/
theorem IsArithFrob.restrictNormal {τ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hτ : IsArithFrob τ v p) (hp : p ≠ 0)
    (E : IntermediateField ℚ Qbar) [Normal ℚ E] :
    let w := v.comap (algebraMap E Qbar)
    let σ := AlgEquiv.restrictNormal τ E
    σ ∈ w.decompositionSubgroup ℚ ∧ ∀ x ∈ w, σ x - x ^ p ∈ w.nonunits := by
  dsimp only
  have hcong : ∀ x ∈ v.comap (algebraMap E Qbar),
      AlgEquiv.restrictNormal τ E x - x ^ p ∈
        (v.comap (algebraMap E Qbar)).nonunits := by
    intro x hx
    rw [mem_nonunits_comap_iff, map_sub, map_pow,
      AlgEquiv.restrictNormal_commutes]
    exact hτ.2 (algebraMap E Qbar x) hx
  exact ⟨mem_decompositionSubgroup_of_congruence hp hcong, hcong⟩

end ZInQ.Contrib.FrobeniusDensity
