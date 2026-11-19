/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU (git blob fb764734273da58ee2913ae5f57cafa93f7f494b, sha256 9c6b8f813850f3a64c7c95b03836dadc372423aa938d5c01fa0ee3fc00506e8a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
    (N : ℕ) [NeZero N] (k : ℤ) {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (G H V : UpperHalfPlane → ℂ)
    (hGH : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      G τ' = (τ : ℂ) ^ k * H τ)
    (hUV : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      ModularForm.heckeU k q H τ' = (τ : ℂ) ^ k * V τ)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N / q : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * (-(N : ℂ)) ^ (-k) * V (ModularForm.heckeMatrix q 0 • τ) := by
  revert N k q hq hqN G H V hGH hUV τ
  exact @_root_.P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.solution
