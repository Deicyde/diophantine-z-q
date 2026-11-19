/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi (git blob 150751f6bf6c4fadae8b645bba569fad9fe76714, sha256 b70ac5ae069728ac57defb91401d7837f89460f4edb27a2f097489597c6a3343).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_full_eq_dedekindPsi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
theorem ModularCurve.relfinrank_full_eq_dedekindPsi (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull N) = dedekindPsi N := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_relfinrank_full_eq_dedekindPsi.solution
