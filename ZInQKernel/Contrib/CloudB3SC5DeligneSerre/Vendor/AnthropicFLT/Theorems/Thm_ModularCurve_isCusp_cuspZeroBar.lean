/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isCusp_cuspZeroBar (git blob 565e64091e96e2af403d819af977711f850ff61c, sha256 cb8d752a97438931be13a58a84fa5dd9986fbde1081300f2625d99a31bdfd1dd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isCusp_cuspZeroBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspZeroBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspZeroBar N) := by
  revert N h
  exact @_root_.P2MW.S_ModularCurve_isCusp_cuspZeroBar.solution
