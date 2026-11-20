/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar (git blob 8409b65622c496a379d0cda4092660902e1e0ae3, sha256 290889a5d5ddbc8c9491f4dee1859d8f0ffb43e45657245770e464248a87db6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.cuspZeroBar_ne_cuspInftyBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) : cuspZeroBar N ≠ cuspInftyBar N := by
  revert N h hN
  exact @_root_.P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar.solution
