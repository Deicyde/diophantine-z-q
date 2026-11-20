/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff (git blob d380d8f209b51a05ea94f264f473a22155d79b65, sha256 cf61f5cb11323519058b601e46e79e59a06e7f055935b631c301f8d7dfabe1ad).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff (N : ℕ)
    [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
      (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b *
      (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n) := by
  revert N k f a hf W hW
  exact @_root_.P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.solution
