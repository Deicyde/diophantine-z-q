import Mathlib

open NumberField
open scoped Pointwise

namespace GlueConj

abbrev Qbar := AlgebraicClosure ℚ
abbrev Gal := Qbar ≃ₐ[ℚ] Qbar

theorem val_lt_one_iff (w : ValuationSubring Qbar) (t : Qbar) :
    w.valuation t < 1 ↔ t ∈ w ∧ (t = 0 ∨ t⁻¹ ∉ w) := by
  rw [← w.valuation_le_one_iff, ← w.valuation_le_one_iff]
  by_cases ht : t = 0
  · subst ht; simp
  have hprod : w.valuation t * w.valuation t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  constructor
  · intro h
    refine ⟨h.le, Or.inr fun h' => ?_⟩
    have : w.valuation t * w.valuation t⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h') h
    rw [hprod] at this; exact lt_irrefl _ this
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 ht
    · refine lt_of_le_of_ne h1 fun he => h2 ?_
      rw [he, one_mul] at hprod; exact hprod.le

/-- Transport of the maximal ideal under the pointwise action. -/
theorem val_smul_lt_one_iff (w : ValuationSubring Qbar) (g : Gal) (y : Qbar) :
    (g • w).valuation y < 1 ↔ w.valuation (g⁻¹ y) < 1 := by
  rw [val_lt_one_iff, val_lt_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹).injective]

/-- **Glue: conjugate places have conjugate inertia.** If `w' = g • w` then
`g⁻¹ I_{w'} g ≤ I_w` (inertia as in glue-b3-unram, the image of Mathlib's `inertiaSubgroup`). -/
theorem inertia_conj (w w' : ValuationSubring Qbar) (g : Gal) (hw : w' = g • w) (s : Gal)
    (hs : s ∈ (w'.inertiaSubgroup ℚ).map (w'.decompositionSubgroup ℚ).subtype) :
    g⁻¹ * s * g ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  have hdec : g⁻¹ * (t : Gal) * g ∈ w.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hw,
      MulAction.mem_stabilizer_iff.mp t.2, hw, inv_smul_smul]
  refine Subgroup.mem_map.mpr ⟨⟨_, hdec⟩, ?_, rfl⟩
  have ht' : ∀ z : w', w'.valuation ((t : Gal) (z : Qbar) - z) < 1 := by
    intro z
    have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField w') t = 1 := ht
    have h2 := congrArg (fun f => f (IsLocalRing.residue w' z)) h1
    change t • IsLocalRing.residue w' z = IsLocalRing.residue w' z at h2
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
    exact h2
  change _ = (1 : _)
  ext r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨_, hdec⟩ : w.decompositionSubgroup ℚ) • IsLocalRing.residue w y = IsLocalRing.residue w y
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hgy : g (y : Qbar) ∈ w' := by
    rw [hw]; exact ValuationSubring.smul_mem_pointwise_smul_iff.mpr y.2
  let e : w.decompositionSubgroup ℚ := ⟨_, hdec⟩
  show w.valuation ((e • y - y : w) : Qbar) < 1
  have he : ((e • y - y : w) : Qbar) = g⁻¹ ((t : Gal) (g y) - g y) := by
    rw [map_sub]
    show (g⁻¹ * ↑t * g) (y : Qbar) - y = _
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    congr 1
    exact ((g⁻¹ : Gal).apply_symm_apply _).symm.trans (by rfl) |>.symm ▸ rfl
  rw [he]
  generalize hu : (t : Gal) = u at ht' ⊢
  have h3 := ht' ⟨_, hgy⟩
  clear ht'
  subst hw
  rw [val_smul_lt_one_iff] at h3
  exact h3

end GlueConj
