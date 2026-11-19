/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus (git blob 3bd37bf7039f98c19964c8c84ec3c044685cae48, sha256 85a5682a3b35a1f932e166dcaa5b7fb3d9ad82c083e82da38b9ef5ebe3363aa1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_exists_zpow_mul_mem_annulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped NNReal
theorem TateCurve.exists_zpow_mul_mem_annulus {K : Type*} [NontriviallyNormedField K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) : ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by
  revert K q u hq0 hq hu0
  exact @_root_.P2MW.S_TateCurve_exists_zpow_mul_mem_annulus.solution
