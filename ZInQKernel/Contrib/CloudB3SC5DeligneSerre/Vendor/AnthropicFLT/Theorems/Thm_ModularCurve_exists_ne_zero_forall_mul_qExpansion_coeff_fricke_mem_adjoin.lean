/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin (git blob b389dc49744df1afba5070031aaa62c8a830437a, sha256 4b66a388ca5948174859804b2059b6c5557236ac1996d39a3e9166c637b40348).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
    (N : ℕ) [NeZero N]
    (L : UpperHalfPlane → PeriodPair)
    (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), W v τ =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ,
      (D : ℂ) * (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant)).coeff n ∈
        Algebra.adjoin ℤ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ) := by
  revert N L hL W hW fricke hfricke v hv
  exact @_root_.P2MW.S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.solution
