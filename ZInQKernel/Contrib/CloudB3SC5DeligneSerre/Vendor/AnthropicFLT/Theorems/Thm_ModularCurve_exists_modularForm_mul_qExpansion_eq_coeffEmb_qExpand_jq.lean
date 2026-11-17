/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq (git blob 17f6d238a6b4595310aa1cee85fd76ff613da7c3, sha256 a3995106b91132cb33411daaf06f8b7b0f5d53b433e4246163678c85ac93695f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane in

theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq (N d : ℕ)
    [NeZero N] [NeZero d] (hd : d ∣ N) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ d ModularCurve.jq) *
          ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  revert N d hd
  exact @_root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.solution
