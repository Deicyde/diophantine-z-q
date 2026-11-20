/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_pointX_zpow_mul (git blob 1a5e6c2fa07fe49bc174f1e16cee10188f1545f3, sha256 5c990d908abf32a5da96867cdefbbf2183fd5d3edad74887580e3c26f2ce2d68).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_pointX_q_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_pointX_zpow_mul
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (n : ℤ) :
    pointX q (q ^ n * u) = pointX q u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ k ih =>
      have h : q ^ ((k : ℤ) + 1) * u = q * (q ^ (k : ℤ) * u) := by
        rw [zpow_add_one₀ hq0]; ring
      rw [h, TateCurve.pointX_q_mul hq0, ih]
  | pred k ih =>
      have h : q ^ (-(k : ℤ)) * u = q * (q ^ (-(k : ℤ) - 1) * u) := by
        rw [show (-(k : ℤ)) = (-(k : ℤ) - 1) + 1 by ring, zpow_add_one₀ hq0]; ring
      have hstep := TateCurve.pointX_q_mul (q := q) (u := q ^ (-(k : ℤ) - 1) * u) hq0
      rw [← h] at hstep
      rw [← hstep, ih]
