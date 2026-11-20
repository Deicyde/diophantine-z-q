/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_defectCoeff_zero (git blob 3b78c81ab6ef269bafbf104a6a4ec347dc3bdb68, sha256 8b49c6afcc44bf88e29979a8c991e7807fa20fbd20aa6b59f44bf769832f6b1c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_Defect
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_nodal_xfun_yfun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_defectCoeff_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by
  have hnodal := TateCurve.nodal_xfun_yfun (K := K) (w := u) hu1
  simp only [defectCoeff, cauchyMul_zero, xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero,
    a₆Coeff_zero, zero_mul, add_zero]
  linear_combination hnodal
