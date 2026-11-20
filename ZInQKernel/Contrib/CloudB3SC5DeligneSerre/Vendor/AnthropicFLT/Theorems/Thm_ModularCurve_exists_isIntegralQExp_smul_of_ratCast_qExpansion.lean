/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion (git blob e9ecf94ae2857200e8dc1304758f9eb866f908c3, sha256 496e685e9fc9ff552cc61371dc775053cdff54fe37c6d70bf3d7398d57893b8f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑f : UpperHalfPlane → ℂ)) p := by
  revert M k f hf
  exact @_root_.P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.solution
