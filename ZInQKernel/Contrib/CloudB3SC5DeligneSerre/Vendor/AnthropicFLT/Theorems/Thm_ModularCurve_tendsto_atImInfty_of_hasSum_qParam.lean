/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tendsto_atImInfty_of_hasSum_qParam (git blob 2fdcf358cc1c5ac8a45c1130e5823329da8df3b3, sha256 e931d65671b873478ef41f5aa1f981926112164fc0a9cd3d447b8b98480cc904).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.tendsto_atImInfty_of_hasSum_qParam (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (c 0)) := by
  revert h hh F c hc
  exact @_root_.P2MW.S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam.solution
