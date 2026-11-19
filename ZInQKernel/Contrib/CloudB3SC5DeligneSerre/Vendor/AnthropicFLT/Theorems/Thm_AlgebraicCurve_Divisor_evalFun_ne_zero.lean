/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_evalFun_ne_zero (git blob bc4e270d459c4d70d39097d6a1e79190c3ebe935, sha256 9371183869f82a9aff4bf3d5a29e4f582e060f28b5d32ba1a13dd98333d36127).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} {D : Divisor K F} (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f D ≠ 0 := by
  revert K F f D h
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_ne_zero.solution
