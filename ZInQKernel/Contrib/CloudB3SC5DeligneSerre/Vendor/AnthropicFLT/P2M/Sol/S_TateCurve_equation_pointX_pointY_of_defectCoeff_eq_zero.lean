/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero (git blob 2e345f994e861898d4f73ae464c697cdb20a7745, sha256 f1c535287953bb552777cbf919c734106f6212cc9cd9bce3db9b25f80a961ae1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_Defect
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_equation_of_defectCoeff_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_pointX_zpow_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_pointY_zpow_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K}
    (hD : ∀ v : K, v ≠ 0 → v ≠ 1 → ∀ N : ℕ, 0 < N → defectCoeff v N = 0)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by
  obtain ⟨n, hqu, hqu'⟩ := TateCurve.exists_zpow_mul_mem_annulus hq0 hq hu0
  have hv0 : q ^ n * u ≠ 0 := mul_ne_zero (zpow_ne_zero n hq0) hu0
  have hvlat : ∀ m : ℤ, q ^ m * (q ^ n * u) ≠ 1 := by
    intro m; rw [← mul_assoc, ← zpow_add₀ hq0]; exact hu (m + n)
  have hv1 : q ^ n * u ≠ 1 := by simpa using hvlat 0
  have heq := TateCurve.equation_of_defectCoeff_eq_zero hq0 hq hv0 hvlat hqu hqu' (hD _ hv0 hv1)
  rwa [TateCurve.pointX_zpow_mul hq0 n, TateCurve.pointY_zpow_mul hq0 n] at heq
