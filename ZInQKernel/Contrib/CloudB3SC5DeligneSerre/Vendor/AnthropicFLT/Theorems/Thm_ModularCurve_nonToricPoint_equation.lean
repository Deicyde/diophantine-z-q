/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_nonToricPoint_equation (git blob 6c9c2e8f2e1f78ea3890f7445a644963c1dcc3bb, sha256 ba2343b235b391bad927bb9eab8d3132b8094558bba9ddccf2bcaf1fc94688d7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_nonToricPoint_equation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
theorem ModularCurve.nonToricPoint_equation (K : Type*) [Field K] [CharZero K] (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (tateBase K p).toAffine.Equation (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 := by
  revert K p c j hj hjp
  exact @_root_.P2MW.S_ModularCurve_nonToricPoint_equation.solution
