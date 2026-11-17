/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul (git blob 75e0f420e53fd5b8418e72024c177c1dd5372436, sha256 120b721df50290df0c5fe49624add094e43f47d302ee095da50da732a58cba9f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem ModularCurve.JOne.galois_smul_heckeAlgOne_smul (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x) := by
  revert M σ t x
  exact @_root_.P2MW.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.solution
