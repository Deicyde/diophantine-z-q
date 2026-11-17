/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_WeilDatum_addLeft_pairing (git blob 3c40bb521ce9a74357c3d1b609afb0ab85e9cb1c, sha256 ab6146c21c16b94f379ba5aa46ea450beeee050c03e6d0bb3592887c3b42e561).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_WeilDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_WeilDatum_addLeft_pairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.WeilDatum.addLeft_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) : (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by
  revert K F n d d' hD hf
  exact @_root_.P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.solution
