/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_veluQuotient2_cFour
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_veluQuotient2_cFour

open WeierstrassCurve in
theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R) :
    (W.veluQuotient2 x₀ y₀).c₄ = W.c₄ + 240 * W.veluGx x₀ y₀ := by
  have hb₄ : (W.veluQuotient2 x₀ y₀).b₄ = W.b₄ - 10 * W.veluGx x₀ y₀ := by
    simp only [b₄, veluQuotient2_a₁, veluQuotient2_a₃, veluQuotient2_a₄]; ring
  simp only [c₄, veluQuotient2_b₂, hb₄]; ring
