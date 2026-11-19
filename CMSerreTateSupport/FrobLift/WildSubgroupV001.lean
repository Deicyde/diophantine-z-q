import FrobLift.CorollariesV003

/-!
# The wild subgroup: a subgroup of inertia, normal in the decomposition group

For a valuation subring `w` of an algebraic extension `Ω/K`, the literal wild condition
`v_w(σ x - x) < v_w(x)` for all `x ≠ 0` cuts out a subgroup `wildSubgroup w` of `Gal(Ω/K)`.
Every wild element lies in the inertia group of `w` (`PkgI2.IsInertia`), and the wild subgroup is
normalized by the decomposition group (in particular by every Frobenius lift and by every inertia
element). Also: `IsUnit (ℓ : O)` gives `Nat.Coprime ℓ q` for `q = #(O / 𝔪_O)`.
-/

noncomputable section

namespace FrobLift

open scoped Pointwise

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

theorem val_eq_of_wild (w : ValuationSubring Ω) {σ : Ω ≃ₐ[K] Ω}
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) (x : Ω) :
    w.valuation (σ x) = w.valuation x := by
  by_cases hx : x = 0
  · simp [hx]
  have e : σ x = x + (σ x - x) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (hσ x hx)]

/-- The wild subgroup of `w` (lower ramification group `G₁`, valuation form). -/
def wildSubgroup (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x}
  one_mem' := by
    intro x hx
    simp only [AlgEquiv.one_apply, sub_self, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hx)
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
    have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]
      ring
    rw [e]
    apply Valuation.map_add_lt _ _ (hτ x hx)
    rw [← val_eq_of_wild w hτ x]
    exact hσ _ hτx
  inv_mem' := by
    intro σ hσ x hx
    set y := σ⁻¹ x with hy
    have hy0 : y ≠ 0 := (map_ne_zero σ⁻¹).mpr hx
    have hσy : σ y = x := by
      rw [hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have e : σ⁻¹ x - x = -(σ y - y) := by
      rw [← hy, hσy]
      ring
    rw [e, Valuation.map_neg, ← hσy, val_eq_of_wild w hσ y]
    exact hσ y hy0

theorem mem_wildSubgroup_iff (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ wildSubgroup w ↔ ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x := Iff.rfl

/-- Wild elements lie in the decomposition group. -/
theorem mem_decomposition_of_wild {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ wildSubgroup w) : σ ∈ w.decompositionSubgroup K := by
  show σ • w = w
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← ValuationSubring.valuation_le_one_iff,
    ← ValuationSubring.valuation_le_one_iff, AlgEquiv.smul_def,
    val_eq_of_wild w ((wildSubgroup w).inv_mem hσ) y]

/-- **Wild elements are inertia elements** (`PkgI2.IsInertia`). -/
theorem isInertia_of_wild {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ wildSubgroup w) : PkgI2.IsInertia w σ := by
  refine ⟨mem_decomposition_of_wild hσ, ?_⟩
  show MulSemiringAction.toRingAut _ _ _ = 1
  ext r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  show (⟨σ, mem_decomposition_of_wild hσ⟩ : w.decompositionSubgroup K) •
    IsLocalRing.residue w x = IsLocalRing.residue w x
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  show w.valuation (σ (x : Ω) - x) < 1
  by_cases hx : (x : Ω) = 0
  · rw [hx, map_zero, sub_zero, map_zero]
    exact zero_lt_one
  · exact lt_of_lt_of_le (hσ _ hx) ((ValuationSubring.valuation_le_one_iff w _).2 x.2)

/-- **The wild subgroup is normalized by the decomposition group** (algebraic extensions). -/
theorem conj_mem_wildSubgroup [Algebra.IsAlgebraic K Ω] {w : ValuationSubring Ω}
    {g σ : Ω ≃ₐ[K] Ω} (hg : g ∈ w.decompositionSubgroup K) (hσ : σ ∈ wildSubgroup w) :
    g * σ * g⁻¹ ∈ wildSubgroup w := by
  have hpres := WildTameCharacter.preserves_of_mem_decomposition hg
  intro x hx
  set y := g⁻¹ x with hy
  have hy0 : y ≠ 0 := (map_ne_zero g⁻¹).mpr hx
  have hgy : g y = x := by
    rw [hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have e : (g * σ * g⁻¹) x - x = g (σ y - y) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hy, map_sub, hgy]
  rw [e, hpres, ← hgy, hpres]
  exact hσ y hy0

end FrobLift

namespace FrobLift

variable {K : Type} [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]

/-- **`ℓ` invertible in `O` is prime to the residue cardinality `q`.** -/
theorem coprime_card_residueField_of_isUnit {ℓ : ℕ} (hℓ : IsUnit (ℓ : O)) :
    Nat.Coprime ℓ (Nat.card (IsLocalRing.ResidueField O)) := by
  haveI := finite_residueField O
  cases nonempty_fintype (IsLocalRing.ResidueField O)
  obtain ⟨p, hc⟩ := CharP.exists (IsLocalRing.ResidueField O)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (IsLocalRing.ResidueField O) p
  rw [Nat.card_eq_fintype_card, hk]
  refine Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  intro hdvd
  have h0 : ((ℓ : ℕ) : IsLocalRing.ResidueField O) = 0 := (CharP.cast_eq_zero_iff _ p ℓ).2 hdvd
  have h1 : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField O) := by
    have := hℓ.map (IsLocalRing.residue O)
    simpa using this
  rw [h0] at h1
  exact not_isUnit_zero h1

end FrobLift
