/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ord_cuspInftyBar (git blob 056b8136bd8707a7d75c62b16fcb710b4fb48434, sha256 75b16c80acd4e656f749f14201cc7b5d2e4a29795b5f44a0a60b32273dce7cf3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ord_cuspInftyBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) : (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order := by
  revert N f
  exact @_root_.P2MW.S_ModularCurve_ord_cuspInftyBar.solution
