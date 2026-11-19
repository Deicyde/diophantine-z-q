/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0 (git blob d796e780da90d6e2a1bae7570dec20311a9fdd6d, sha256 54b371a6313221863f8d780ce7460d8ff1518f4422e8fa8a75f6a7aee66d06f0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M) :
    ∃ H : Subgroup (ZMod M)ˣ, Γ = CohCarrier.GammaH M H := by
  classical

  refine ⟨(Γ.subgroupOf (CongruenceSubgroup.Gamma0 M)).map (CohCarrier.gamma0Units M), ?_⟩

  have hker : ∀ δ : ↥(CongruenceSubgroup.Gamma0 M), CohCarrier.gamma0Units M δ = 1 → (δ : SL(2, ℤ)) ∈ Γ := by
    intro δ hδ
    apply hΓ₁
    rw [CongruenceSubgroup.Gamma1_mem]
    have hd : (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hδ
      simp [CohCarrier.val_gamma0Units] at this
      exact this
    have hc : (((δ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := (CongruenceSubgroup.Gamma0_mem).mp δ.2
    have ha : (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = 1 := by
      have h := CohCarrier.Gamma0_d_mul_a M δ

      have h' : (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = 1 := by simpa using h
      rwa [hd, one_mul] at h'
    exact ⟨ha, hd, hc⟩
  apply le_antisymm
  · intro γ hγ
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hΓ₀ hγ, ?_⟩
    exact Subgroup.mem_map.mpr ⟨⟨γ, hΓ₀ hγ⟩, Subgroup.mem_subgroupOf.mpr hγ, rfl⟩
  · intro γ hγ
    obtain ⟨hγ0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    obtain ⟨δ, hδΓ, hδ⟩ := Subgroup.mem_map.mp hH
    have hδΓ' : (δ : SL(2, ℤ)) ∈ Γ := Subgroup.mem_subgroupOf.mp hδΓ

    have hk : ((δ⁻¹ * ⟨γ, hγ0⟩ : ↥(CongruenceSubgroup.Gamma0 M)) : SL(2, ℤ)) ∈ Γ := by
      apply hker
      rw [map_mul, map_inv, hδ, inv_mul_cancel]
    have : γ = (δ : SL(2, ℤ)) * ((δ⁻¹ * ⟨γ, hγ0⟩ : ↥(CongruenceSubgroup.Gamma0 M)) : SL(2, ℤ)) := by
      simp
    rw [this]
    exact Γ.mul_mem hδΓ' hk
