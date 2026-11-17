/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne (git blob 079345d0d4fcb047980955d350b215ab637fd6fb, sha256 3158c2dcedf56404a84330baef5e24764f5a416ec078404169937d59de2de706).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by
  revert N H τ τ' hτ
  exact @_root_.P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne.solution
