/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq (git blob 36242307ffab76b4b62978c30daed167688f062b, sha256 bcbc4138f2c294453c28b51d7fee2995e617fbd80e5a8a472caafb92e0d0d13c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ')
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (hτ' : γ₀ • τ = τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by
  revert N H τ τ' hτ γ₀ hγ₀ hτ'
  exact @_root_.P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.solution
