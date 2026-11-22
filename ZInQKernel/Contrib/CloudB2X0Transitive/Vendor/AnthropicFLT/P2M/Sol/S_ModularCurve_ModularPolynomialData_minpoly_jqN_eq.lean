/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq

open ModularCurve IntermediateField

theorem solution {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hirr : ModularCurve.PhiIrreducible data) :
    minpoly (↥ℚ⟮ModularCurve.jq⟯) (ModularCurve.jqN N) = data.toAdjoin :=
  ModularCurve.minpoly_jqN_eq_toAdjoin data hirr
