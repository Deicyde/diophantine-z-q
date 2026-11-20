/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_evalFun_zpow_left (git blob 74ad5cbdd750b5beb925e75a8e4a7d6b2dd1b322, sha256 f8c596285a121689df013e4f1e8b3a17a27ee32af9e4c77d53ee92b9441d6cfc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_zpow_left

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by
  revert K F f hf D n hrat hord
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_zpow_left.solution
