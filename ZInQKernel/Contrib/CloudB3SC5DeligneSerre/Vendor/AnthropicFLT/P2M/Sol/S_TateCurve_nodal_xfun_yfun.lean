/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_nodal_xfun_yfun (git blob a8637d2873ba6fb5c09fe6cb5e61da90f783208d, sha256 3eaad2bc590f9c56ed2f52036061604084a39dd3faa74ea80a26c04799e389fc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_nodal_xfun_yfun
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {w : K} (hw1 : w ≠ 1) :
    yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have e2 : xfun w * ((1 : K) - w) ^ 2 = w := by
    rw [xfun, div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
  have e3 : yfun w * ((1 : K) - w) ^ 3 = w ^ 2 := by
    rw [yfun, div_mul_cancel₀ _ (pow_ne_zero 3 h1)]
  apply mul_right_cancel₀ (pow_ne_zero 6 h1)
  calc (yfun w ^ 2 + xfun w * yfun w) * ((1 : K) - w) ^ 6
      = (yfun w * ((1 : K) - w) ^ 3) ^ 2
        + (xfun w * ((1 : K) - w) ^ 2) * (yfun w * ((1 : K) - w) ^ 3) * ((1 : K) - w) := by ring
    _ = (w ^ 2) ^ 2 + w * w ^ 2 * ((1 : K) - w) := by rw [e2, e3]
    _ = w ^ 3 := by ring
    _ = (xfun w * ((1 : K) - w) ^ 2) ^ 3 := by rw [e2]
    _ = xfun w ^ 3 * ((1 : K) - w) ^ 6 := by ring
