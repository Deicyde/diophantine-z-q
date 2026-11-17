/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0 (git blob d350a8a9fe3eab10ff94868f141d75dfb061efc1, sha256 1adc7feace683b6bab577efe087470dc02402df4e646e8fdcddd08c33e2f0c70).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M) :
    ∃ H : Subgroup (ZMod M)ˣ, Γ = CohCarrier.GammaH M H := by
  revert M Γ hΓ₁ hΓ₀
  exact @_root_.P2MW.S_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0.solution
