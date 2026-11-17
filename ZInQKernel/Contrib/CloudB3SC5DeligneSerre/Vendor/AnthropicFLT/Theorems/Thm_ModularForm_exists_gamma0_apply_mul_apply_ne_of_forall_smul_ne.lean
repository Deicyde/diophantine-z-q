/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne (git blob 265ee845e9b342b7db8d84ad1872ef2e393117dc, sha256 6b07b37d912bf51fce6c9384c6684b94e3bc18509d9c8c877bf01b991948fbd8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := by
  revert N τ τ' hτ
  exact @_root_.P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.solution
