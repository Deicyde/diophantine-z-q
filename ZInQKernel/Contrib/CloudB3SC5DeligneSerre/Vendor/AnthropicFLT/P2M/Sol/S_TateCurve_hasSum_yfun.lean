/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_hasSum_yfun (git blob 7433624e96bed7402b1c02154acb272c0909b66b, sha256 d897c07671c3a55d951f6b18928581cedb1d1c6bc8af1b85ae5e82a2f060c1b9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_hasSum_yfun
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hw').mul_left (w ^ 2)
  have hfun : (fun m : ℕ => w ^ 2 * (((m + 2).choose 2 : ℕ) * w ^ m))
      = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
    funext m; ring
  have hval : w ^ 2 * (1 / (1 - w) ^ 3) = yfun w := by rw [yfun]; ring
  rw [hfun, hval] at h
  exact h
