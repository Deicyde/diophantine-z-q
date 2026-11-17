/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne (git blob 37dd66ae28f2d4bf52f6b2d2810943b12fa3e734, sha256 192e6397fc8095d35fe8f00e8a2d701e351ce88507c087e167f360534c7bb828).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : UpperHalfPlane)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : UpperHalfPlane → ℂ) τ * (h : UpperHalfPlane → ℂ) τ' ≠
        (g : UpperHalfPlane → ℂ) τ' * (h : UpperHalfPlane → ℂ) τ := by
  classical
  by_cases hex : ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ₀ • τ = τ'
  · obtain ⟨γ₀, hγ₀, hτ'⟩ := hex
    exact ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq N H τ τ' hτ γ₀ hγ₀ hτ'
  · have h0 : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ' :=
      fun γ hγ => hex ⟨γ.1, γ.2, hγ⟩
    obtain ⟨k, g, h, hne⟩ := ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne N τ τ' h0
    have hle : ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
      Subgroup.map_mono (CohCarrier.GammaH_le_Gamma0 H)
    refine ⟨k, ModularCurve.restrictForm hle g, ModularCurve.restrictForm hle h, ?_⟩
    rw [ModularCurve.coe_restrictForm, ModularCurve.coe_restrictForm]
    exact hne
