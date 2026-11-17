/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk (git blob ba1f23ae4c51ace47e67af3bee74d9be62c21320, sha256 aa5ec56f47dee26b2f5455bec804e04e58bfbab22cdb3f6e1df9377eda154c90).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.isIntegral_adjoin_intermediateField_mk {L F : Type*} [Field L] [Field F] [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E) (h : IsIntegral (Algebra.adjoin L {j}) x) : IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E) := by
  revert L F E j x hj hx h
  exact @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk.solution
