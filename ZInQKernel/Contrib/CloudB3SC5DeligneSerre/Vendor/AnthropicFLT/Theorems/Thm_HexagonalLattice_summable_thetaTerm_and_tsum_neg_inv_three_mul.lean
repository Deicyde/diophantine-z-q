/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul (git blob 663ead86e88c3047a25584a32ec2725b515eaa2d, sha256 8fc2c4cc69a208239ba73b512a1cb66695454924212ce2c0564bf359d25e9880).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul (σ : ℂ) (hσ : 0 < σ.im) :
    Summable (fun p : ℤ × ℤ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) ∧
    (∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-1 / (3 * σ)) *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) =
      -Complex.I * (Real.sqrt 3 : ℂ) * σ *
        ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
          ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by
  revert σ hσ
  exact @_root_.P2MW.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.solution
