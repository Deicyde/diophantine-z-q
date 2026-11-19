/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives (git blob 09d593a0da6d225ca49fe18302bcf2d9131070a1, sha256 71e113c15dda9cc51b6dd9610e12abd45bc6c385254f9d2edd13c2c7253b3235).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

namespace RS11C1

variable {G X ι : Type*} [Group G] [MulAction G X]

theorem subgroup_smul_set (Γ : Subgroup G) (γ : Γ) (s : Set X) : γ • s = (γ : G) • s := rfl

theorem smul_iUnion_inv_smul (Γ : Subgroup G) (R : ι → Γ) (g : G) (s : Set X) :
    g • (⋃ i, ((R i : G)⁻¹) • s) = ⋃ i, (g * (R i : G)⁻¹) • s := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [smul_smul]

end RS11C1

theorem solution
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    refine NullMeasurableSet.iUnion fun i => ?_
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [RS11C1.subgroup_smul_set, Subgroup.coe_inv] at h
  ·
    filter_upwards [h𝓕.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨i, hi, -⟩ := hR γ
    refine ⟨⟨(R i : G)⁻¹ * γ, hi⟩, ?_⟩
    rw [Subgroup.smul_def]
    show ((R i : G)⁻¹ * (γ : G)) • x ∈ ⋃ i, ((R i : G)⁻¹) • 𝓕
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set (by rw [← Subgroup.smul_def]; exact hγ)
  ·
    intro γ γ' hne
    change AEDisjoint μ (γ • ⋃ i, ((R i : G)⁻¹) • 𝓕) (γ' • ⋃ i, ((R i : G)⁻¹) • 𝓕)
    rw [RS11C1.subgroup_smul_set, RS11C1.subgroup_smul_set, RS11C1.smul_iUnion_inv_smul Γ₁ R,
      RS11C1.smul_iUnion_inv_smul Γ₁ R, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j

    have hγ₁ : ((γ : G) * (R i : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ.2) (inv_mem (R i).2)
    have hγ₁' : ((γ' : G) * (R j : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ'.2) (inv_mem (R j).2)
    have hne' : (⟨(γ : G) * (R i : G)⁻¹, hγ₁⟩ : Γ₁) ≠ ⟨(γ' : G) * (R j : G)⁻¹, hγ₁'⟩ := by
      intro heq
      have heq' : (γ : G) * (R i : G)⁻¹ = (γ' : G) * (R j : G)⁻¹ := congrArg Subtype.val heq

      have hmem : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by
        have : ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * (γ : G) := by
          calc ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * ((γ' : G) * (R j : G)⁻¹) * (R i : G) := by group
            _ = (γ' : G)⁻¹ * ((γ : G) * (R i : G)⁻¹) * (R i : G) := by rw [heq']
            _ = (γ' : G)⁻¹ * (γ : G) := by group
        rw [Subgroup.coe_inv, this]
        exact mul_mem (inv_mem γ'.2) γ.2
      have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
      obtain ⟨k, -, hk⟩ := hR (R i)
      have hij : i = j := (hk i hii).trans (hk j hmem).symm
      subst hij
      apply hne
      apply Subtype.ext
      exact mul_right_cancel heq'
    have h := h𝓕.aedisjoint hne'
    simpa only [Function.onFun, RS11C1.subgroup_smul_set] using h
