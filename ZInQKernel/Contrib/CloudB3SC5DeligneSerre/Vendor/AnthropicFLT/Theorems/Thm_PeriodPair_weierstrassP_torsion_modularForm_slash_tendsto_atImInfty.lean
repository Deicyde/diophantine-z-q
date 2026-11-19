/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty (git blob 2ff7cefe60d11d105701a761294074621ad20e50, sha256 051aef1e5537a5f16c362a76e6e7883c326c70107900d8f8c8aa88e0ea36c821).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
    (L : UpperHalfPlane → PeriodPair) (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ :=
      fun b τ => (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)
    (∃ F : ModularForm (CongruenceSubgroup.Gamma N) 2, ⇑F = W a) ∧
    (∀ γ : SL(2, ℤ), W a ∣[(2 : ℤ)] γ = W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∧
    (a ≠ 0 → Filter.Tendsto (W a) UpperHalfPlane.atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) := by
  revert L hL N a
  exact @_root_.P2MW.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.solution
