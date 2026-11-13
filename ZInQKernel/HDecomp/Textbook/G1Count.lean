import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5b from
`scratch/t30-adelic/G1Count.lean` (G1-adelic, the count).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# t30-adelic, part G1-adelic (a): the order count of A3

For `Γ' = N/(𝔸_f^× K₃)`: with `Z = 𝔸_f^×` (central), `K₃ ≤ K₀ ≤ N`, and `Z K₃` normal in `N`,
`|Γ'| = |N/Z K₀| · |K₀/(Z ∩ K₀) K₃|`, and `Z ∩ K₀ = ℤ̂^×` in the application.
Generic group theory, stated inside the ambient group `G` (= `N` in the application).
-/

namespace G1Count

variable {G : Type*} [Group G]

/-- Dedekind's modular law for a normal `Z`: `(Z ⊔ K₃) ⊓ K₀ = (Z ⊓ K₀) ⊔ K₃` when `K₃ ≤ K₀`. -/
theorem sup_inf_eq (Z K₀ K₃ : Subgroup G) [Z.Normal] (hK : K₃ ≤ K₀) :
    (Z ⊔ K₃) ⊓ K₀ = (Z ⊓ K₀) ⊔ K₃ := by
  apply le_antisymm
  · rintro x ⟨hx, hx0⟩
    have hx' : x ∈ ((Z ⊔ K₃ : Subgroup G) : Set G) := hx
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨z, hz, k, hk, rfl⟩ := hx'
    have hz0 : z ∈ K₀ := by
      have := K₀.mul_mem hx0 (K₀.inv_mem (hK hk))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hz, hz0⟩) (Subgroup.mem_sup_right hk)
  · refine sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hK)

/-- **The count.** `[G : Z K₃] = [G : Z K₀] · [K₀ : (Z ∩ K₀) K₃]` for `K₃ ≤ K₀`, `Z` normal and
`Z K₃` normal. -/
theorem index_count (Z K₀ K₃ : Subgroup G) [Z.Normal] [(Z ⊔ K₃).Normal] (hK : K₃ ≤ K₀) :
    (Z ⊔ K₃).index = (Z ⊔ K₀).index * ((Z ⊓ K₀) ⊔ K₃).relIndex K₀ := by
  have hle : Z ⊔ K₃ ≤ Z ⊔ K₀ := sup_le_sup_left hK Z
  rw [← Subgroup.relIndex_mul_index hle, mul_comm]
  congr 1
  have hsup : K₀ ⊔ (Z ⊔ K₃) = Z ⊔ K₀ := by
    apply le_antisymm
    · exact sup_le le_sup_right hle
    · exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  rw [← hsup, Subgroup.relIndex_sup_right, ← sup_inf_eq Z K₀ K₃ hK, Subgroup.relIndex,
    Subgroup.relIndex, Subgroup.inf_subgroupOf_right]

/-- The same with `Z` central (so `Z` is normal). -/
theorem index_count_of_central (Z K₀ K₃ : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    [(Z ⊔ K₃).Normal] (hK : K₃ ≤ K₀) :
    (Z ⊔ K₃).index = (Z ⊔ K₀).index * ((Z ⊓ K₀) ⊔ K₃).relIndex K₀ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  exact index_count Z K₀ K₃ hK

end G1Count
