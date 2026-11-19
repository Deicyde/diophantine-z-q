/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_pointX_inv (git blob 3511c8ded8367500f6a3531b1e77d7a1af057b7b, sha256 3ff3955f9ca3e421931ee404c22651b8dbdc1563a2b2eb8d346d8de11e8327c7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_pointX_inv

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointX q u⁻¹ = pointX q u := by
  have hinv : ∀ n : ℤ, xTerm q u⁻¹ (-n) = xTerm q u n := fun n => by
    rw [xTerm, xTerm, zpow_neg, ← mul_inv]
    exact xfun_inv (mul_ne_zero (zpow_ne_zero n hq0) hu0) (hu n)
  rw [pointX, pointX]
  congr 1
  calc ∑' n : ℤ, xTerm q u⁻¹ n = ∑' n : ℤ, xTerm q u⁻¹ (-n) := (tsum_comp_neg _).symm
    _ = ∑' n : ℤ, xTerm q u n := tsum_congr hinv
