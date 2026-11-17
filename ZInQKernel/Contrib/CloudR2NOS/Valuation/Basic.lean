/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.

Source-derived portions: anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2:
* Definitions/Def_FLTPrelim_Ramification.lean:19-22 (exact inertia image definition).
* P2M/Sol/S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.lean:9-28.
* P2M/Sol/S_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul.lean:11-55.
* P2M/Sol/S_ValuationSubring_exists_isMaximal_valuation_lt_one_iff_and_exists_of_isMaximal_integralClosure.lean:33-44.

MODIFICATION NOTICE (2026-11-14, H5 Round-2 Lane2): narrow Mathlib-only
imports; isolated namespace; P2M export machinery removed; integral-membership
lemma generalized to any base-ring image containment; new power, coarsening,
trivial-restriction, top-inertia and purely-inseparable restriction proofs.
The original LICENSE, NOTICE and ATTRIBUTION are preserved in the lane report.
-/
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.CloudR2NOS.Valuation

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Exactly the image of Mathlib's nested inertia subgroup in `Aut(L/K)`. -/
def inertiaSubgroupIn (V : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (V.inertiaSubgroup K).map (V.decompositionSubgroup K).subtype

/-- A valuation ring is saturated under every strictly positive integer power. -/
theorem pow_mem_iff (V : ValuationSubring L) (x : L) {n : ℕ} (hn : 0 < n) :
    x ^ n ∈ V ↔ x ∈ V := by
  rw [← V.valuation_le_one_iff, map_pow, ← V.valuation_le_one_iff]
  constructor
  · intro h
    by_contra! hx
    exact (not_lt_of_ge h) (one_lt_pow₀ hx (Nat.ne_of_gt hn))
  · intro h
    exact pow_le_one₀ zero_le h

/-- Integral elements belong to a valuation ring containing all base coefficients. -/
theorem mem_of_isIntegral_of_algebraMap_mem (V : ValuationSubring L)
    (hV : ∀ a : K, algebraMap K L a ∈ V) {b : L} (hb : IsIntegral K b) : b ∈ V := by
  let f : K →+* V.toSubring := (algebraMap K L).codRestrict V.toSubring hV
  obtain ⟨p, hpm, hpe⟩ := hb
  have hcomp : (algebraMap V.toSubring L).comp f = algebraMap K L :=
    RingHom.ext fun _ => rfl
  have hint : IsIntegral V.toSubring b := by
    refine ⟨p.map f, hpm.map f, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hpe
  exact (V.mem_toSubring b).mp
    (LocalSubring.mem_of_isMax_of_isIntegral V.isMax_toLocalSubring hint)

/-- An algebraic field extension admits no nontrivial valuation trivial on its base. -/
theorem eq_top_of_comap_eq_top [Algebra.IsAlgebraic K L] (V : ValuationSubring L)
    (hV : V.comap (algebraMap K L) = ⊤) : V = ⊤ := by
  apply top_unique
  intro x _
  apply mem_of_isIntegral_of_algebraMap_mem (K := K) V
  · intro a
    have : a ∈ V.comap (algebraMap K L) := by rw [hV]; exact ValuationSubring.mem_top a
    exact this
  · exact Algebra.IsIntegral.isIntegral x

/-- Every valuation containing the original DVR restricts either to it or to top. -/
theorem comap_eq_or_eq_top (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (V : ValuationSubring L) (hV : ∀ r : O, algebraMap O L r ∈ V) :
    V.comap (algebraMap K L) = O ∨ V.comap (algebraMap K L) = ⊤ := by
  have hle : O ≤ V.comap (algebraMap K L) := fun x hx => hV ⟨x, hx⟩
  exact (ValuationSubring.eq_self_or_eq_top_of_le hle).imp Eq.symm id

/-- The preceding dichotomy on the extension field itself, using algebraicity. -/
theorem comap_eq_or_top [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (V : ValuationSubring L) (hV : ∀ r : O, algebraMap O L r ∈ V) :
    V.comap (algebraMap K L) = O ∨ V = ⊤ := by
  exact (comap_eq_or_eq_top O V hV).imp id (eq_top_of_comap_eq_top V)

/-- Residue-triviality written in the actual valuation of the extension field. -/
theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn (V : ValuationSubring L)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ inertiaSubgroupIn (K := K) V) {a : L} (ha : a ∈ V) :
    σ a ∈ V ∧ V.valuation (σ a - a) < 1 := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
  have hmem : ((τ : L ≃ₐ[K] L) a) ∈ V := (V.subMulAction K).smul_mem τ ha
  refine ⟨hmem, ?_⟩
  have hker : MulSemiringAction.toRingAut (V.decompositionSubgroup K)
      (IsLocalRing.ResidueField V) τ = 1 := MonoidHom.mem_ker.mp hτ
  have hsmul : τ • (⟨a, ha⟩ : V) = ⟨(τ : L ≃ₐ[K] L) a, hmem⟩ := rfl
  have hres : IsLocalRing.residue V ⟨(τ : L ≃ₐ[K] L) a, hmem⟩ =
      IsLocalRing.residue V ⟨a, ha⟩ := by
    rw [← hsmul, IsLocalRing.ResidueField.residue_smul]
    show (MulSemiringAction.toRingAut (V.decompositionSubgroup K)
        (IsLocalRing.ResidueField V) τ) (IsLocalRing.residue V ⟨a, ha⟩) = _
    rw [hker]
    rfl
  have hmem' : (⟨(τ : L ≃ₐ[K] L) a, hmem⟩ - ⟨a, ha⟩ : V) ∈
      IsLocalRing.maximalIdeal V :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by rw [map_sub, hres, sub_self])
  exact (V.valuation_lt_one_iff _).mp hmem'

/-- Criterion for membership in the same inertia image; no field perfection is used. -/
theorem mem_inertiaSubgroupIn_of_valuation_sub_lt_one (V : ValuationSubring L)
    {σ : L ≃ₐ[K] L} (hσV : σ • V = V)
    (h : ∀ a ∈ V, V.valuation (σ a - a) < 1) :
    σ ∈ inertiaSubgroupIn (K := K) V := by
  let d : V.decompositionSubgroup K := ⟨σ, hσV⟩
  refine ⟨d, ?_, rfl⟩
  change MulSemiringAction.toRingAut (V.decompositionSubgroup K)
    (IsLocalRing.ResidueField V) d = 1
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change d • IsLocalRing.residue V a = IsLocalRing.residue V a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h a a.2

/-- Exact Type* source inertia conjugation, in an isolated namespace. -/
theorem conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
    (V : ValuationSubring L) (g : L ≃ₐ[K] L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ inertiaSubgroupIn (K := K) (g • V)) :
    g⁻¹ * σ * g ∈ inertiaSubgroupIn (K := K) V := by
  have hσD : σ • (g • V) = g • V := by
    obtain ⟨d, _, rfl⟩ := hσ
    exact d.2
  refine mem_inertiaSubgroupIn_of_valuation_sub_lt_one V ?_ ?_
  · rw [mul_smul, mul_smul, hσD, inv_smul_smul]
  · intro a ha
    have hga : g a ∈ g • V := ValuationSubring.smul_mem_pointwise_smul g a V ha
    have hlt := (valuation_sub_lt_one_of_mem_inertiaSubgroupIn (g • V) hσ hga).2
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hlt ⊢
    have hcalc : (g⁻¹ * σ * g) a - a = g⁻¹ (σ (g a) - g a) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      congr 1
      exact (g.symm_apply_apply a).symm
    rw [hcalc]
    rcases hlt with h0 | hinv
    · left
      rw [h0, map_zero]
    · right
      rw [← map_inv₀]
      intro hmem
      apply hinv
      have := ValuationSubring.smul_mem_pointwise_smul g _ V hmem
      rwa [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this

/-- Inertia at the top valuation is literally the identity automorphism. -/
theorem eq_one_of_mem_inertiaSubgroupIn_top {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ inertiaSubgroupIn (K := K) (⊤ : ValuationSubring L)) : σ = 1 := by
  ext x
  have hlt := (valuation_sub_lt_one_of_mem_inertiaSubgroupIn
    (⊤ : ValuationSubring L) hσ (ValuationSubring.mem_top x)).2
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hlt
  have he : σ x - x = 0 := hlt.resolve_right (by simp)
  exact sub_eq_zero.mp he

end ZInQ.Contrib.CloudR2NOS.Valuation
