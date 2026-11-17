/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_symAddHyps_unconditional (git blob 99c8920bc1e3f7e54c66bc51c1dc2fbf497bad79, sha256 decf65c4f3f14a89aa8506ca003cecad10e9b60fc8d53f35090faa230c1f565d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_XMultAlignment
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_symAddHyps_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped NNReal
theorem TateCurve.symAddHyps_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) : TateCurve.SymAddHyps q := by
  revert K q hq0 hq
  exact @_root_.P2MW.S_TateCurve_symAddHyps_unconditional.solution
