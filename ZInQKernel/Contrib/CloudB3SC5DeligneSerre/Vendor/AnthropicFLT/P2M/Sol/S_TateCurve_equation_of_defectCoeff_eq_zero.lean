/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_equation_of_defectCoeff_eq_zero (git blob bc45430a090f07dbaa20a16bdd6b565adc952f9a, sha256 6549b7c7682e35cf9dae3e0205a105b7c65147aa36bd3ea2e980292d6689d20d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_Defect
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_defectCoeff_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_defect_qExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_equation_of_defectCoeff_eq_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (h : ∀ N : ℕ, 0 < N → defectCoeff u N = 0) :
    pointY q u ^ 2 + pointX q u * pointY q u
      = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by
  have hu1 : u ≠ 1 := by simpa using hu 0
  have hall : ∀ N : ℕ, defectCoeff u N = 0 := by
    intro N; cases N with
    | zero => exact TateCurve.defectCoeff_zero hu1
    | succ n => exact h (n + 1) n.succ_pos
  have hexp := TateCurve.defect_qExpansion hq0 hq hu0 hu hqu hqu'
  have hzero : ∑' N : ℕ, defectCoeff u N * q ^ N = 0 := by
    have hterm : ∀ N : ℕ, defectCoeff u N * q ^ N = 0 := fun N => by rw [hall N, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  rw [hzero] at hexp
  exact sub_eq_zero.mp hexp
