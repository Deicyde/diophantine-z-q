/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun (git blob ccbb1995996cbd877ddeeb1c40b1ca3d0e0f6b39, sha256 1f295a2be23a2e031ffe57b94c28d520dd0cd119072bca7a81aa7ec5b67401e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SiegelFunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open ModularCurve
open scoped Manifold in

theorem ModularCurve.SiegelUnit.differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) := by
  revert N r s
  exact @_root_.P2MW.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.solution
