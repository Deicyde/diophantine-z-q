/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_TateCurve_symAdd_sum_regional (git blob 72f78cd892c696fe95b1d299e8871491adbbd603, sha256 359812f0ce81db8ee755e92066cdd9efca158f9983d942317014c3f895499ddc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_XMultIdentities
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_KeystoneVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_TateCurve_symAdd_sum_regional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem TateCurve.symAdd_sum_regional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {q : K} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∀ u' v' : K, TateCurve.ExpansionRegion q u' v' →
      (TateCurve.pointX q (u' * v') + TateCurve.pointX q (u' * v'⁻¹)) * (TateCurve.pointX q u' - TateCurve.pointX q v') ^ 2 =
        TateCurve.symSumNum q (TateCurve.pointX q u') (TateCurve.pointX q v') := by
  revert K q hq0 hq1
  exact @_root_.P2MW.S_TateCurve_symAdd_sum_regional.solution
