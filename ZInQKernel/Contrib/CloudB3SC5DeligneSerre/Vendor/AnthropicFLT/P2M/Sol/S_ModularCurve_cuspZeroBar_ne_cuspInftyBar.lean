/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar (git blob 72b71416882d4ad1ccf45a0de37e9ef16a2f450a, sha256 9b3f7a7b8aa29bc3cb3e6c8f7a9e27d3139ef80ec043a9ea9b8d5fa3f63cec65).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) :
    cuspZeroBar N ≠ cuspInftyBar N := by
  intro e
  have h0 := ModularCurve.ord_cuspZeroBar_coeffEmb_jq N h
  rw [e, ModularCurve.ord_cuspInftyBar_coeffEmb_jq] at h0
  have : (N : ℤ) = 1 := by linarith
  exact absurd (Nat.cast_eq_one.mp this) hN.ne'
