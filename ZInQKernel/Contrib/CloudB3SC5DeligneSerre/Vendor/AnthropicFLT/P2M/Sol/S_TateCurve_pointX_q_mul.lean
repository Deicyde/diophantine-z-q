/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_pointX_q_mul (git blob 06270f570b70da3df0f984ac7952a95d2bf095a5, sha256 46bb5475d80818ca366cf45e591e83e570eb65ae629caa495f2ab5c3432e2e26).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_pointX_q_mul
open TateCurve
open scoped NNReal

private theorem tsum_comp_add_one' {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) :
    ∑' n : ℤ, f (n + 1) = ∑' n : ℤ, f n :=
  (Equiv.addRight (1 : ℤ)).tsum_eq f

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointX q (q * u) = pointX q u := by
  have hterm : ∀ n : ℤ, xTerm q (q * u) n = xTerm q u (n + 1) := fun n => by
    rw [xTerm, xTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointX, pointX]
  congr 1
  calc ∑' n : ℤ, xTerm q (q * u) n = ∑' n : ℤ, xTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, xTerm q u n := tsum_comp_add_one' _
