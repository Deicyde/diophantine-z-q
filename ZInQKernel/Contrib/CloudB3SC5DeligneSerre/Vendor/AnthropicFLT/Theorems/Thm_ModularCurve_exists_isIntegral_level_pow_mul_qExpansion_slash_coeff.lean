/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff (git blob 0b63d81f443119fbfcd89b5559048a7761ba47c3, sha256 4bea9ec5dd8c9c19773061ab55b671b7aa1b178b905e267fc057d8ec7f3790c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p) (γ : SL(2, ℤ)) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ a *
      (UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n) := by
  revert M k f p hp γ
  exact @_root_.P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.solution
