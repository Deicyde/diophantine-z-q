/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor (git blob 4a446de00fdac76ba0a4cdb0dd251deaa4321f00, sha256 ac48186334546b74bd329cc827c09731261981661ed767847b687cf11c4c20bf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (m : ℕ) :
    (∀ g ∈ LSpace ((m : ℕ) • D), x * g ∈ LSpace ((m + 1) • D)) ∧
    (∀ g ∈ LSpace ((m + 1) • D), x * g ∈ LSpace ((m + 1) • D) → g ∈ LSpace (m • D)) := by
  revert K F x D hD m
  exact @_root_.P2MW.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor.solution
