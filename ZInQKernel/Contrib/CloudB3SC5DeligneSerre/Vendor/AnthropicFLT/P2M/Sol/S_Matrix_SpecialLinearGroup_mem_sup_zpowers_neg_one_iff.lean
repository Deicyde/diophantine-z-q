/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff (git blob 16174080238826adbd5426c91414243d54f7c68d, sha256 dcb616d014941059db1fbb0ef535d802fef420b47ab127ec9f5ffe2e0c70bfb2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Matrix.SpecialLinearGroup
end Matrix.SpecialLinearGroup
namespace Matrix
end Matrix

namespace P2MW.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff

set_option autoImplicit false

open scoped MatrixGroups

namespace Matrix
export _root_.Matrix (J SpecialLinearGroup of)
namespace SpecialLinearGroup
namespace MemSupNegOne
open _root_.Matrix.SpecialLinearGroup
open _root_.Matrix

def pmSubgroup (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Γ.mul_mem ha hb)
    · right
      have : -(a * b) = a * -b := by rw [mul_neg]
      rw [this]
      exact Γ.mul_mem ha hb
    · right
      have : -(a * b) = -a * b := by rw [neg_mul]
      rw [this]
      exact Γ.mul_mem ha hb
    · left
      have : a * b = -a * -b := by rw [neg_mul_neg]
      rw [this]
      exact Γ.mul_mem ha hb
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (Γ.inv_mem ha)
    · right
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        apply inv_eq_of_mul_eq_one_right
        rw [neg_mul_neg, mul_inv_cancel]
      have : -a⁻¹ ∈ Γ := by
        rw [← hinv]
        exact Γ.inv_mem ha
      exact this

theorem mem_pmSubgroup_iff (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ pmSubgroup Γ ↔ g ∈ Γ ∨ -g ∈ Γ := Iff.rfl

end Matrix.SpecialLinearGroup.MemSupNegOne

open Matrix.SpecialLinearGroup.MemSupNegOne in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ := by
  constructor
  · intro hg
    have hle : Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ pmSubgroup Γ := by
      refine sup_le (fun x hx => Or.inl hx) ?_
      rw [Subgroup.zpowers_le, mem_pmSubgroup_iff]
      right
      rw [neg_neg]
      exact Γ.one_mem
    exact (mem_pmSubgroup_iff Γ g).mp (hle hg)
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have : g = -g * -1 := by rw [neg_mul_neg, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
