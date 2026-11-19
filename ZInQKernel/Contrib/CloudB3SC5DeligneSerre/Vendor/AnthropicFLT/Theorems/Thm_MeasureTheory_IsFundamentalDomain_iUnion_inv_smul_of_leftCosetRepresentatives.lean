/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives (git blob b3741102c92a8e0cd1ceb5933e652c58829ebe4c, sha256 32dc6d39c7831f9e250f2bb32390b84bf493d46ecbba20c30807762bef7c3a2c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

theorem MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by
  revert G X ι μ Γ₁ Γ₂ hle 𝓕 h𝓕 R hR
  exact @_root_.P2MW.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.solution
