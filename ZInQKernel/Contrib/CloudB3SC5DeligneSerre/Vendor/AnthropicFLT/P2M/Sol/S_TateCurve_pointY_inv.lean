/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_pointY_inv (git blob 2d90aec7480eb24dc8fe0c8d0e6b262aaa78d20a, sha256 838680305ecf8bce7d63f5c13e95858b269bdc6f98a4928649cd42d134287559).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_pointY_inv

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointY q u⁻¹ = -pointY q u - pointX q u := by
  have hinv : ∀ n : ℤ, yTerm q u⁻¹ (-n) = -yTerm q u n - xTerm q u n := fun n => by
    rw [yTerm, yTerm, xTerm, zpow_neg, ← mul_inv]
    exact yfun_inv (mul_ne_zero (zpow_ne_zero n hq0) hu0) (hu n)
  have hs : HasSum (fun n : ℤ => -yTerm q u n - xTerm q u n)
      (-(∑' n : ℤ, yTerm q u n) - ∑' n : ℤ, xTerm q u n) :=
    ((summable_yTerm hq0 hq hu0).hasSum.neg).sub (summable_xTerm hq0 hq hu0).hasSum
  have h1 : ∑' n : ℤ, yTerm q u⁻¹ n = -(∑' n : ℤ, yTerm q u n) - ∑' n : ℤ, xTerm q u n := by
    calc ∑' n : ℤ, yTerm q u⁻¹ n = ∑' n : ℤ, yTerm q u⁻¹ (-n) := (tsum_comp_neg _).symm
      _ = ∑' n : ℤ, (-yTerm q u n - xTerm q u n) := tsum_congr hinv
      _ = _ := hs.tsum_eq
  rw [pointY, pointY, pointX, h1]
  ring
