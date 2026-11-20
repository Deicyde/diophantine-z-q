/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq (git blob d026536dd98d0b6c141a958a196afa86bf14fc27, sha256 448f65149066f12b2b542246e3e91bd9bc267b38fee7e666e03e07d31dbaf8bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_jq (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -N := by
  revert N h
  exact @_root_.P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq.solution
