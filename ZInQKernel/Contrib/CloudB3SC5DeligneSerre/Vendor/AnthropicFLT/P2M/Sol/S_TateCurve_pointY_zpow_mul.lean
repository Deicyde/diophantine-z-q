/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_pointY_zpow_mul (git blob e1245641099538b343169b9dbddf25ec79c33b52, sha256 d8aa965da1d72a974973579e020a52219616b354e54748b496b834e227123e2c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_pointY_q_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_pointY_zpow_mul
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (n : ℤ) :
    pointY q (q ^ n * u) = pointY q u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ k ih =>
      have h : q ^ ((k : ℤ) + 1) * u = q * (q ^ (k : ℤ) * u) := by
        rw [zpow_add_one₀ hq0]; ring
      rw [h, TateCurve.pointY_q_mul hq0, ih]
  | pred k ih =>
      have h : q ^ (-(k : ℤ)) * u = q * (q ^ (-(k : ℤ) - 1) * u) := by
        rw [show (-(k : ℤ)) = (-(k : ℤ) - 1) + 1 by ring, zpow_add_one₀ hq0]; ring
      have hstep := TateCurve.pointY_q_mul (q := q) (u := q ^ (-(k : ℤ) - 1) * u) hq0
      rw [← h] at hstep
      rw [← hstep, ih]
