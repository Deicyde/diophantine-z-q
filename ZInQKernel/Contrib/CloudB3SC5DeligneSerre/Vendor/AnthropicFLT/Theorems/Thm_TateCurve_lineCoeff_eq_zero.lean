/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_lineCoeff_eq_zero (git blob 8238ad6b2db9e6d37be683106f72f43e9ae4b493, sha256 ac368c4c0009a115dcdd8c2f4760ad3b265c8f3dbf21419dd3661b556e72014d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_DefectLines
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_lineCoeff_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open TateCurve
theorem TateCurve.lineCoeff_eq_zero : ∀ N k : ℕ, 1 ≤ k → k ≤ N → lineCoeff N k = 0 := @_root_.P2MW.S_TateCurve_lineCoeff_eq_zero.solution
